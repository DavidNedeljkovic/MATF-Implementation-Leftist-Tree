theory LeftistHeap
  imports Main "HOL-Library.Multiset"
begin

datatype 'a LHeap = Null | Node "'a LHeap" 'a nat  "'a LHeap"

(* Racunamo rastojanje do null-a koristeci sledece svojstvo leftist hipa:
    dist(right(i)) <= dist(left(i))
*)
fun dist :: "'a LHeap \<Rightarrow> nat" where
  "dist Null = 0"
| "dist (Node _ _ _ r) = dist r + 1"


(* Citamo rastojanje prosledjenog cvora *)
fun readDist :: "'a LHeap \<Rightarrow> nat" where
  "readDist Null = 0"
| "readDist (Node _ _ n _) = n"


(* Ukoliko uslov dist(right(i)) <= dist(left(i) nije ispunjen rotiramo levo i desno
    podstablo i racunamo razdaljinu za koreni cvor
*)
definition node :: "'a LHeap \<Rightarrow> 'a \<Rightarrow> 'a LHeap \<Rightarrow> 'a LHeap" where
  "node l v r =
    (let dl = readDist l; dr = readDist r 
     in if dl \<ge> dr then Node l v (dr+1) r else Node r v (dl+1) l)"

fun merge :: "'a::ord LHeap \<Rightarrow> 'a LHeap \<Rightarrow> 'a LHeap" where
  "merge Null t2 = t2"
| "merge t1 Null = t1"
| "merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2) = 
    (if v1 \<le> v2 then node l1 v1 (merge r1 (Node l2 v2 n2 r2))
     else node l2 v2 (merge (Node l1 v1 n1 r1) r2))"

value "merge Null (Node Null 4 1 Null)::nat LHeap"

definition insert :: "'a::ord \<Rightarrow> 'a LHeap \<Rightarrow> 'a LHeap" where
  "insert v t = merge (Node Null v 1 Null) t"

(* testiranje insert-a *)
definition test_tree_1 :: "nat LHeap" where
  "test_tree_1 = (insert 7 (insert 6 (insert 8 (insert 14 Null))))"

definition test_tree_2 :: "nat LHeap" where
    "test_tree_2 = insert 8 (insert 25 (insert 12 (insert 15 (insert 4 (insert 20 (insert 19 (insert 27 (insert 43 Null))))))))"

(* testiranje merge-a*)
value "merge test_tree_1 test_tree_2"

(* brisemo najmanji element (koren) stabla *)
fun delMin :: "'a::ord LHeap \<Rightarrow> 'a LHeap" where
"delMin Null = Null" |
"delMin (Node l v n r) = merge l r"

value "delMin test_tree_1"

(* Uzimamo najmanji element iz stabla *)
fun getMin :: "'a LHeap \<Rightarrow> 'a" where
  "getMin (Node l v n r) = v"

value "getMin test_tree_1"

datatype ('a, 'b) Tree = TNull | TNode "('a, 'b) Tree" 'a 'b "('a, 'b) Tree"

(* Pravimo multiset elemenata iz drveta *)
fun treeToMSet :: "'a LHeap \<Rightarrow> 'a multiset" where
  "treeToMSet Null = {#}" 
| "treeToMSet (Node l v _ r) = treeToMSet l + {#v#} + treeToMSet r"

(* Proverava "Normal Min Heap Property" svojstvo:
    key(i) >= key(parent(i))
*)
fun isHeap :: "'a::ord LHeap \<Rightarrow> bool" where
  "isHeap Null = True"
| "isHeap (Node l v _ r) = ((\<forall>x \<in> set_mset(treeToMSet l + treeToMSet r).v \<le> x) 
                            \<and> isHeap l \<and> isHeap r)"

definition heap :: "nat LHeap" where
  "heap = (Node (Node (Node Null 4 20 Null) 2 5 (Node Null 5 25 Null)) 1 11 (Node Null 3 7 Null))"
definition not_heap :: "nat LHeap" where
  "not_heap = (Node (Node (Node Null 14 20 Null) 21 5 (Node Null 5 25 Null)) 19 11 (Node Null 6 7 Null))"

value "isHeap heap"
value "isHeap not_heap"


(* Proverava "Heavier on left side" svojstvo:
     dist(right(i)) <= dist(left(i))
*)
fun isLHeap :: "'a LHeap \<Rightarrow> bool" where
  "isLHeap Null = True"
| "isLHeap (Node l v n r) = (n = dist r + 1 \<and> dist l \<ge> dist r 
                             \<and> (isLHeap l \<and> isLHeap r))"

(* Prosledjeno leftist drvo*) 
value "isLHeap test_tree_1"


(* Prosledjeno drvo koje nije leftist *)
definition not_ltree :: "nat LHeap" where
  "not_ltree = (Node (Node Null 6 1 Null) 4 3 (Node (Node Null 6 1 Null) 8 2 (Node Null 10 1 Null)))"
value "isLHeap not_ltree"

(* Prazan multiset nekog drveta znaci da je drvo null *)
lemma emptyMSetEQNullTree[simp]: "treeToMSet tree = {#} \<longleftrightarrow> tree = Null"
  by (induction tree) auto

lemma getDistEQDist[simp]: "isLHeap tree \<Longrightarrow> readDist tree = dist tree"
  by (induction tree) auto

(* Ako primenimo node funkciju na dva leftist stabla, dobijeno stablo
    ostaje leftist
 *)
lemma isLHeapNode[simp]: "isLHeap l \<and> isLHeap r \<longleftrightarrow> isLHeap (node l v r)"
  using node_def
  by (smt getDistEQDist isLHeap.simps(2) linear)

(* Izvrsavanjem node funkcije drvo ne gubi "Normal Min Heap Property" svojstvo:
    key(i) >= key(parent(i))
*)
lemma heapNode[simp]: "isHeap (node l v r) \<longleftrightarrow>
  isHeap l \<and> isHeap r \<and> (\<forall>x \<in> set_mset(treeToMSet l + treeToMSet r). v \<le> x)"
  using node_def
  by (smt add.commute isHeap.simps(2))


(* Multiskup dva spojena drveta je jednak uniji multiskupova pojedinacnih dveta *)
lemma mergeMSet[simp]: "treeToMSet (merge tree1 tree2) = treeToMSet tree1 + treeToMSet tree2"
proof (induction tree1 tree2 rule: merge.induct)
case (1 t2)
then show ?case
  by simp
next
  case (2 v va vb vc)
  then show ?case
    by simp
next
  case (3 l1 v1 n1 r1 l2 v2 n2 r2)
  then show ?case
  proof cases
    assume "v1 \<le> v2"
    hence "treeToMSet (merge r1 (Node l2 v2 n2 r2)) = treeToMSet r1 + treeToMSet (Node l2 v2 n2 r2)"
      by (simp add: "3.IH"(1))
    thus "treeToMSet (merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2)) = treeToMSet (Node l1 v1 n1 r1) + treeToMSet (Node l2 v2 n2 r2)"
      using  LHeap.simps(1)  LHeap.simps(3)  merge.simps(3) node_def treeToMSet.simps(2)
    by (smt \<open>v1 \<le> v2\<close> add.commute add.left_commute )
  next
    assume "\<not> v1 \<le> v2"
    hence "treeToMSet (merge (Node l1 v1 n1 r1) r2) = treeToMSet (Node l1 v1 n1 r1) + treeToMSet r2"
      by (simp add: "3.IH"(2))
    thus "treeToMSet (merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2)) = treeToMSet (Node l1 v1 n1 r1) + treeToMSet (Node l2 v2 n2 r2)"
      using  merge.simps(3) node_def treeToMSet.simps(2)
  by (smt \<open>\<not> v1 \<le> v2\<close> add.assoc add.commute)
  qed
qed

(* Multiskup drveta nakon ubacivanja elemenata je jednak multiskupu kojem smo dodali novi element*)
lemma insertMSet[simp]: "treeToMSet (insert v tree) = treeToMSet tree + {#v#}"
  using insert_def
  by (metis add.commute add_mset_add_single mergeMSet treeToMSet.simps(1) treeToMSet.simps(2))


(* Ukoliko je drvo hip i nije Null tada je njegov najmanji element jednak najmanjem 
  elementu multiskupa tog drveta*)
lemma minHeapEQminMSet[simp]:
  assumes "isHeap tree" and "tree \<noteq> Null"
  shows "getMin tree = Min_mset (treeToMSet tree)"
  by (smt Min_insert2 add_mset_add_single assms(1) assms(2) finite_set_mset
      getMin.simps isHeap.simps(2) set_mset_add_mset_insert treeToMSet.elims
      union_mset_add_mset_left)

(* Multiskup drveta sa izbrisanim najmanjim elementom jednak je razlici  multiskupu
 celog drveta i najmanjeg elementa. *)
lemma delMinMSet[simp]: "treeToMSet (delMin tree) = treeToMSet tree - {#getMin tree#}"
  by (smt add_mset_add_single add_mset_not_empty add_mset_remove_trivial
      add_mset_remove_trivial_If delMin.simps(1) delMin.simps(2) diff_single_trivial
      getMin.simps mergeMSet treeToMSet.elims union_mset_add_mset_left)


(* Ako pretpostavimo da je levo podstablo leftist i desno podstablo leftist kad ih 
  spojimo novo stablo je takodje leftist. *)
lemma LHeapMerge[simp]: 
  assumes "isLHeap l" and "isLHeap r"
  shows "isLHeap (merge l r)"
  using assms
proof (induction l r rule: merge.induct)
case (1 t2)
  then show ?case
    by simp
next
  case (2 v va vb vc)
  then show ?case
    by simp
next
  case (3 l1 v1 n1 r1 l2 v2 n2 r2)
  then show ?case
    by (metis isLHeap.simps(2) isLHeapNode merge.simps(3))
qed

lemma heapMerge: 
  assumes "isHeap l" and "isHeap r"
  shows "isHeap (merge l r)"
  using assms
  proof (induction l r rule: merge.induct)
case (1 t2)
then show ?case
  by simp
next
  case (2 v va vb vc)
  then show ?case by simp
next
  case (3 l1 v1 n1 r1 l2 v2 n2 r2)
  then show ?case
  proof(cases)
    assume "v1 \<le> v2"
    hence "isHeap r1" 
      using "3.prems"(1) by auto
    hence "isHeap (Node l2 v2 n2 r2)"
  using "3.prems"(2) by auto
  hence *:"isHeap (merge r1 (Node l2 v2 n2 r2))"
    by (simp add: "3.IH"(1) \<open>isHeap r1\<close> \<open>v1 \<le> v2\<close>)
  have **: "isHeap (Node l1 v1 n1 r1)" 
    using "3.prems"(1) by blast
  have "isHeap (Node l2 v2 n2 r2)"
    using "3.prems"(2) by auto
  thus "isHeap (merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2))"
    using * ** 
    sorry

next
  assume "\<not> v1 \<le> v2"
  hence "isHeap (Node l1 v1 n1 r1)"
    using "3.prems"(1) by blast
  hence "isHeap r2"
    using "3.prems"(2) isHeap.simps(2) by blast
  hence "isHeap (merge (Node l1 v1 n1 r1) r2)"
    using "3.IH"(2) "3.prems"(1) \<open>\<not> v1 \<le> v2\<close> by blast
  thus "isHeap (merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2))"
    sorry
  qed
qed

(* U narednim lemama se proverava da li drvo posle ubacivanja elementa ili
    brisanja najmanjeg elementa zadrzava sledeca svojstva:
    -"Normal Min Heap Property": value(i) >= value(parent(i))
    -"Heavier on left side": dist(right(i)) <= dist(left(i))
*)
lemma insertIsLHeap: "isLHeap tree \<Longrightarrow> isLHeap (insert v tree)"
  by (simp add: LeftistHeap.insert_def)

lemma isertIsHeap: "isHeap tree \<Longrightarrow> isHeap (insert v tree)"
  by (simp add: LeftistHeap.insert_def heapMerge)

lemma delMinIsLHeap: "isLHeap tree \<Longrightarrow> isLHeap (delMin tree)"
  by (metis LHeapMerge delMin.simps(1) delMin.simps(2) isLHeap.elims(2))

lemma delMinIsHeap: "isHeap tree \<Longrightarrow> isHeap (delMin tree)"
  by (metis (full_types) delMin.elims heapMerge isHeap.simps(2))

(*
Implementiramo red sa prioritetom zasnovan na leftist drvetu sa sledecim operacijama:
  push: Ubacujemo element sa njegovim prioritetom.
  top: Ocitavamo element sa najmanjim prioritetom.
  pop: Brisemo element sa najmanjim prioritetom.
  empty: Proveravamo da li je red prazan.
 *)

type_synonym PriorityQueue = "nat LHeap"

fun push :: "nat \<Rightarrow> PriorityQueue \<Rightarrow> PriorityQueue" where
  "push pr PQ  = insert pr PQ"

fun top :: "PriorityQueue \<Rightarrow> nat" where
  "top PQ = getMin PQ"

fun pop :: "PriorityQueue \<Rightarrow> PriorityQueue" where
  "pop PQ = delMin PQ"

fun empty :: "PriorityQueue \<Rightarrow> bool" where
  "empty PQ \<longleftrightarrow> PQ = Null"

definition bank :: "PriorityQueue" where
  "bank = push 5 (push 150 (push 112 Null))"

value "top bank"
value "top (pop bank)"
value "empty bank"


(* Hipsort zasnovan na leftist drvetu *)

fun listToLHeap :: "'a::ord list \<Rightarrow> 'a LHeap" where
  "listToLHeap [] = Null"
| "listToLHeap (x # xs) = insert x (listToLHeap xs)"

value "listToLHeap [2::nat,7,1,9,6]"

fun size :: "'a::ord LHeap \<Rightarrow> nat" where
  "size Null = 0"
| "size (Node Null _ _ Null) = 1"
| "size (Node l _ _ Null) = 1 + size l" 
| "size (Node Null _ _ r) = 1 + size r"
| "size (Node l _ _ r) = 1 + size l + size r"



lemma sizeMerge[simp]: "size t1 + size t2 = size (merge t1 t2)"
proof (induction t1 t2 rule: merge.induct)
  case (1 t2)
then show ?case by simp
next
  case (2 v va vb vc)
  then show ?case by simp
next
  case (3 l1 v1 n1 r1 l2 v2 n2 r2)
  then show ?case
  proof (cases)
    assume "v1 \<le> v2"
    hence "LeftistHeap.size r1 + LeftistHeap.size (Node l2 v2 n2 r2) = LeftistHeap.size (merge r1 (Node l2 v2 n2 r2))"
      by (simp add: "3.IH"(1))
    thus "LeftistHeap.size (Node l1 v1 n1 r1) + LeftistHeap.size (Node l2 v2 n2 r2) = LeftistHeap.size (merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2))"
      using node_def
      sorry
next
  assume "\<not>v1 \<le> v2"
  hence " LeftistHeap.size (Node l1 v1 n1 r1) + LeftistHeap.size r2 = LeftistHeap.size (merge (Node l1 v1 n1 r1) r2)"
    by (simp add: "3.IH"(2))
  thus "LeftistHeap.size (Node l1 v1 n1 r1) + LeftistHeap.size (Node l2 v2 n2 r2) = LeftistHeap.size (merge (Node l1 v1 n1 r1) (Node l2 v2 n2 r2))"
    sorry
qed
qed

function heapsort' :: "nat LHeap \<Rightarrow> nat list" where
  "heapsort' Null = []"
| "heapsort' (Node Null v _ Null) = [v]"
| "heapsort' (Node l v _ r) = v # heapsort' (merge l r)" 
  apply pat_completeness 
apply   auto

end