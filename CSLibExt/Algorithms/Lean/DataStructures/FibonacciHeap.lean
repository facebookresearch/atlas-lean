/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.AddSub

/-!
# Fibonacci min-heaps

This module implements persistent Fibonacci heaps following CLRS Chapter 19, in the
correctness-only style of `BinomialHeap.lean`. A heap is a list of heap-ordered trees together
with a cached minimum root value. Insertion and meld are lazy: they only add trees to the root
list and update the cached minimum. Deleting the minimum promotes the children of the minimum
tree and then consolidates the root list by repeatedly linking trees of equal degree, so the
resulting roots have strictly increasing degrees.

The core representation here omits marked nodes and cascading cuts; tree nodes store
only a degree, a root value, and children. A simplified `decreaseKey` operation that
does not perform cascading cuts lives in `FibonacciHeap.DecreaseKey`. The classical Fibonacci size bound
(count at least the `(degree + 2)`-nd Fibonacci number) is also deferred: it depends on
controlling the degrees of children through the mark/cut invariant of CLRS, while `Valid`
here records only heap order and `degree = children.length`. The size facts proved instead
are positivity of tree counts, `degree < count` for every valid tree, and the bound
`roots ≤ count` for consolidated forests.

There is no formal cost model here. The machine-checked results establish the heap-order,
cached-minimum, consolidation, and multiset invariants.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- **Fibonacci tree.** A Fibonacci tree over a type $\alpha$ is a rose tree: a node carrying a
stored degree $d \in \mathbb{N}$, a root value in $\alpha$, and a finite list of child Fibonacci
trees.

Heap order and the equality of the stored degree with the number of children are not part of
the type; they are imposed by the validity predicate on trees. -/
public inductive FibonacciTree (α : Type u) where
  | node (degree : Nat) (root : α) (children : List (FibonacciTree α))
deriving Repr

namespace FibonacciTree

variable {α : Type u}

/-- **Degree of a Fibonacci tree.** The degree of the Fibonacci tree with stored degree $d$,
root value $r$ and list of children $c$ is the stored natural number $d$; it is not computed
from the children. -/
@[expose] public def degree : FibonacciTree α → Nat
  | .node degree _ _ => degree

/-- **Root of a Fibonacci tree.** The root of a Fibonacci tree is the value stored at its top
node. -/
@[expose] public def root : FibonacciTree α → α
  | .node _ root _ => root

/-- **Children of a Fibonacci tree.** The children of the Fibonacci tree with stored degree $d$,
root value $r$ and list of subtrees $c$ are the trees of the list $c$, in order. -/
@[expose] public def children : FibonacciTree α → List (FibonacciTree α)
  | .node _ _ children => children

/-- **Multiset of a Fibonacci tree.** The multiset $M(t)$ of values stored in a Fibonacci tree $t$,
defined recursively: if $t$ has root value $r$ and children $t_1, \dots, t_k$, then
$M(t) = \{r\} + M(t_1) + \cdots + M(t_k)$. The stored degree plays no role. -/
@[expose] public def elements : FibonacciTree α → Multiset α
  | .node _ root children => root ::ₘ (children.map elements).sum

/-- **The root of a Fibonacci tree is one of its elements.** For every Fibonacci tree, its root
value belongs to the multiset of elements the tree represents. -/
public theorem root_mem_elements (tree : FibonacciTree α) : tree.root ∈ tree.elements := by
  cases tree
  simp [root, elements]

/-- **Fibonacci trees are nonempty.** Every Fibonacci tree represents at least one element: the
multiset of elements of any Fibonacci tree has positive size. -/
public theorem card_elements_pos (tree : FibonacciTree α) : 0 < tree.elements.card := by
  cases tree
  simp [elements]

/-- **Valid Fibonacci trees.** Let $\alpha$ carry a relation $\le$. A Fibonacci tree with
stored degree $d$, root $r \in \alpha$ and list of children $c$ is valid when every tree in $c$ is
valid, $d$ equals the length of $c$, and $r \le x$ for every element $x$ of the multiset
represented by the tree (the root together with the elements of all children). -/
public inductive Valid {α : Type u} [LE α] : FibonacciTree α → Prop
  | node {degree : Nat} {root : α} {children : List (FibonacciTree α)}
      (children_valid : ∀ child ∈ children, Valid child)
      (degree_eq : degree = children.length)
      (root_le : ∀ value ∈ elements (.node degree root children), root ≤ value) :
      Valid (.node degree root children)

/-- **One-element Fibonacci heap.** For a value $x$ of a linearly ordered type, the one-element
Fibonacci heap on $x$ has as its only tree the single-node tree with root $x$, and its cached
minimum is $x$. -/
@[expose] public def singleton (value : α) : FibonacciTree α :=
  .node 0 value []

/-- **Linking two Fibonacci trees.** Let $s$ and $t$ be Fibonacci trees over a linearly ordered
type. If the root of $s$ is at most the root of $t$, the link of $s$ and $t$ is the tree with the
root of $s$, stored degree one more than that of $s$, and children $t$ followed by the children
of $s$. Otherwise it is the tree with the root of $t$, stored degree one more than that of $t$,
and children $s$ followed by the children of $t$. -/
@[expose] public def link [LinearOrder α] (left right : FibonacciTree α) : FibonacciTree α :=
  if left.root ≤ right.root then
    .node (left.degree + 1) left.root (right :: left.children)
  else
    .node (right.degree + 1) right.root (left :: right.children)

@[simp] public theorem degree_singleton (value : α) : (singleton value).degree = 0 := by
  rfl

@[simp] public theorem root_singleton (value : α) : (singleton value).root = value := by
  rfl

@[simp] public theorem children_singleton (value : α) :
    (singleton value).children = [] := by
  rfl

@[simp] public theorem elements_singleton (value : α) :
    (singleton value).elements = {value} := by
  simp [singleton, elements]

/-- **Degree of the link of two trees of equal degree.** If two Fibonacci trees $s$ and $t$
over a linearly ordered type have the same degree $d$, then their link has degree $d + 1$. -/
public theorem degree_link_of_eq [LinearOrder α] {left right : FibonacciTree α}
    (degrees : left.degree = right.degree) :
    (link left right).degree = left.degree + 1 := by
  rw [link]
  split
  · rfl
  · show right.degree + 1 = left.degree + 1
    rw [degrees]

/-- **Linking adds the elements.** For any two Fibonacci trees $S$ and $T$ over a linearly ordered
type, the tree obtained by linking $S$ and $T$ represents the sum of the multisets represented by
$S$ and by $T$. -/
public theorem elements_link [LinearOrder α] (left right : FibonacciTree α) :
    (link left right).elements = left.elements + right.elements := by
  rw [link]
  split
  · cases left
    cases right
    simp only [root, degree, children, elements, List.map_cons, List.sum_cons]
    rw [Multiset.cons_add, Multiset.add_cons, Multiset.add_comm]
    simpa only [Multiset.cons_add] using Multiset.cons_swap _ _ _
  · cases left
    cases right
    simp only [root, degree, children, elements, List.map_cons, List.sum_cons]
    rw [Multiset.cons_add, Multiset.add_cons]
    simp only [Multiset.cons_add, Multiset.cons_swap]

/-- **Singleton Fibonacci trees are valid.** Let $\alpha$ be a linearly ordered type. For every
$v \in \alpha$, the Fibonacci tree of degree $0$ with root $v$ and no children is valid. -/
public theorem valid_singleton [LinearOrder α] (value : α) : Valid (singleton value) := by
  constructor
  · simp
  · rfl
  · simp [elements]

/-- **Children of a valid Fibonacci tree are valid.** Every child of a valid Fibonacci tree is
itself a valid Fibonacci tree. -/
public theorem Valid.child_valid [LE α] {tree child : FibonacciTree α}
    (valid : Valid tree) (member : child ∈ tree.children) : Valid child := by
  cases valid with
  | node children_valid _ _ => exact children_valid child member

/-- **The degree of a valid Fibonacci tree is its number of children.** For every valid Fibonacci
tree, its stored degree equals the number of its children. -/
public theorem Valid.degree_eq [LE α] {tree : FibonacciTree α} (valid : Valid tree) :
    tree.degree = tree.children.length := by
  cases valid with
  | node _ degree_eq _ => exact degree_eq

/-- **Roots of valid Fibonacci trees are lower bounds.** The root of a valid Fibonacci tree is no
greater than every element of the multiset the tree represents. -/
public theorem Valid.root_le [LE α] {tree : FibonacciTree α} (valid : Valid tree)
    {value : α} (member : value ∈ tree.elements) : tree.root ≤ value := by
  cases valid with
  | node _ _ root_le => exact root_le value member

private lemma length_le_card_sum (trees : List (FibonacciTree α)) :
    trees.length ≤ ((trees.map elements).sum).card := by
  induction trees with
  | nil => simp
  | cons tree trees ih =>
      simp only [List.map_cons, List.sum_cons, Multiset.card_add, List.length_cons]
      have pos := card_elements_pos tree
      omega

/-- **The degree of a valid Fibonacci tree is less than its size.** For every valid Fibonacci
tree over a type with a relation $\le$, the degree of the tree is strictly less than the
number of elements, counted with multiplicity, of the multiset the tree represents, since
every child contributes at least one element. -/
public theorem Valid.degree_lt_card [LE α] {tree : FibonacciTree α} (valid : Valid tree) :
    tree.degree < tree.elements.card := by
  cases tree with
  | node storedDegree storedRoot storedChildren =>
      have degree_eq := valid.degree_eq
      have bound := length_le_card_sum storedChildren
      simp only [FibonacciTree.degree, FibonacciTree.children] at degree_eq
      simp only [FibonacciTree.degree, FibonacciTree.elements, Multiset.card_cons]
      omega

/-- **Linking preserves validity of Fibonacci trees.** If $s$ and $t$ are valid Fibonacci trees
over a linearly ordered type, then the link of $s$ and $t$ is a valid Fibonacci tree. -/
public theorem Valid.link [LinearOrder α] {left right : FibonacciTree α}
    (left_valid : Valid left) (right_valid : Valid right) : Valid (link left right) := by
  rw [FibonacciTree.link]
  split
  · rename_i root_le
    constructor
    · intro child member
      simp only [children, List.mem_cons] at member
      rcases member with rfl | member
      · exact right_valid
      · exact left_valid.child_valid member
    · simp only [List.length_cons]
      rw [left_valid.degree_eq]
    · intro value member
      have union_member : value ∈ left.elements + right.elements := by
        rw [← elements_link left right]
        simpa [FibonacciTree.link, root_le] using member
      rcases Multiset.mem_add.mp union_member with member | member
      · exact left_valid.root_le member
      · exact root_le.trans (right_valid.root_le member)
  · rename_i not_le
    have root_le : right.root ≤ left.root := le_of_not_ge not_le
    constructor
    · intro child member
      simp only [children, List.mem_cons] at member
      rcases member with rfl | member
      · exact left_valid
      · exact right_valid.child_valid member
    · simp only [List.length_cons]
      rw [right_valid.degree_eq]
    · intro value member
      have union_member : value ∈ left.elements + right.elements := by
        rw [← elements_link left right]
        simpa [FibonacciTree.link, not_le] using member
      rcases Multiset.mem_add.mp union_member with member | member
      · exact root_le.trans (left_valid.root_le member)
      · exact right_valid.root_le member

end FibonacciTree

/-- **Valid Fibonacci forests.** Let $\alpha$ carry a relation $\le$. A Fibonacci forest,
a list of Fibonacci trees with values in $\alpha$, is valid when every tree in it is a valid
Fibonacci tree.

Root degrees may repeat; consolidation is what makes them distinct. -/
@[expose] public def FibonacciForest.Valid {α : Type u} [LE α]
    (trees : List (FibonacciTree α)) : Prop :=
  ∀ tree ∈ trees, tree.Valid

namespace FibonacciForest

variable {α : Type u}

/-- **Multiset of a Fibonacci forest.** Write $M(t)$ for the multiset of values stored in a
Fibonacci tree $t$. The multiset represented by a Fibonacci forest, a list of Fibonacci trees
$t_1, \dots, t_k$, is the sum $M(t_1) + \cdots + M(t_k)$; the empty forest represents the empty
multiset. -/
@[expose] public def elements (trees : List (FibonacciTree α)) : Multiset α :=
  (trees.map FibonacciTree.elements).sum

/-- **Forests with strictly increasing degrees.** A Fibonacci forest, a list of Fibonacci trees
$t_1, \dots, t_k$, has sorted degrees when the stored degrees of its trees strictly increase along
the list: $\deg t_i < \deg t_j$ whenever $i < j$. -/
@[expose] public def SortedDegrees (trees : List (FibonacciTree α)) : Prop :=
  trees.Pairwise fun a b => a.degree < b.degree

private lemma card_elements_le_card {trees : List (FibonacciTree α)} {tree : FibonacciTree α}
    (member : tree ∈ trees) : tree.elements.card ≤ (elements trees).card := by
  induction trees with
  | nil => simp at member
  | cons head tail ih =>
    change tree.elements.card ≤ (head.elements + elements tail).card
    rw [Multiset.card_add]
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have card_le := ih member
      omega

private theorem mem_elements_iff {trees : List (FibonacciTree α)} {value : α} :
    value ∈ elements trees ↔ ∃ tree ∈ trees, value ∈ tree.elements := by
  induction trees with
  | nil => simp [elements]
  | cons tree trees ih =>
      change value ∈ tree.elements + elements trees ↔
        ∃ current ∈ tree :: trees, value ∈ current.elements
      rw [Multiset.mem_add, ih]
      simp

/-- **The empty Fibonacci forest is valid.** Let $\alpha$ carry a relation $\le$. The empty
forest, containing no Fibonacci trees with values in $\alpha$, is valid. -/
public theorem valid_nil [LE α] : Valid ([] : List (FibonacciTree α)) := by
  intro tree member
  simp at member

/-- **Concatenation preserves validity of Fibonacci forests.** Let $\alpha$ carry a relation
$\le$. If $F$ and $G$ are valid Fibonacci forests with values in $\alpha$, then the forest
consisting of the trees of $F$ followed by the trees of $G$ is valid. -/
public theorem valid_append [LE α] {left right : List (FibonacciTree α)}
    (left_valid : Valid left) (right_valid : Valid right) : Valid (left ++ right) := by
  intro tree member
  rw [List.mem_append] at member
  rcases member with member | member
  · exact left_valid tree member
  · exact right_valid tree member

/-- **Sublists of valid Fibonacci forests are valid.** If a list of Fibonacci trees is a valid
forest, then every sublist of it (a subsequence, not necessarily contiguous) is a valid forest. -/
public theorem Valid.sublist [LE α] {left right : List (FibonacciTree α)}
    (sublist : left.Sublist right) (valid : Valid right) : Valid left := by
  intro tree member
  exact valid tree (sublist.subset member)

private theorem sum_append (left right : List (Multiset α)) :
    (left ++ right).sum = left.sum + right.sum := by
  induction left with
  | nil => simp
  | cons value values ih =>
      simp only [List.cons_append, List.sum_cons]
      rw [ih, Multiset.add_assoc]

/-- **Elements of a concatenated forest.** For any two lists $L$ and $R$ of Fibonacci trees, the
forest made of the trees of $L$ followed by the trees of $R$ represents the sum of the multisets
represented by $L$ and by $R$. -/
public theorem elements_append (left right : List (FibonacciTree α)) :
    elements (left ++ right) = elements left + elements right := by
  simp only [elements, List.map_append]
  rw [sum_append]

/-- **Minimum root of a forest.** The minimum root of a forest of Fibonacci trees over a linearly
ordered type is an optional value: it is absent for the empty forest, and for a nonempty forest
it is the least of the roots of its trees. -/
@[expose] public def minRoot [LinearOrder α] : List (FibonacciTree α) → Option α
  | [] => none
  | tree :: trees =>
      match minRoot trees with
      | none => some tree.root
      | some minimum => some (min tree.root minimum)

/-- **Minimum of two optional values.** For optional values $x$ and $y$ of a linearly ordered
type, their combined minimum is defined as follows: if $x$ and $y$ are both present, with values
$a$ and $b$, it is $\min(a, b)$; if exactly one of $x$ and $y$ is present, it is that value; and
if both are absent, it is absent. -/
@[expose] public def minOption [LinearOrder α] (left right : Option α) : Option α :=
  match left, right with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-- **Only the empty forest has no minimum root.** A forest of Fibonacci trees over a linearly
ordered type has no minimum root exactly when it is empty. -/
public theorem minRoot_eq_none_iff [LinearOrder α] (trees : List (FibonacciTree α)) :
    minRoot trees = none ↔ trees = [] := by
  cases trees with
  | nil => simp [minRoot]
  | cons tree trees =>
      cases found : minRoot trees with
      | none => simp [minRoot, found]
      | some minimum => simp [minRoot, found]

/-- **The minimum root is a least root.** If a forest $F$ of Fibonacci trees over a linearly
ordered type has minimum root $m$, then $m$ is the root of some tree of $F$ and $m$ is at most
the root of every tree of $F$. -/
public theorem minRoot_spec [LinearOrder α] {trees : List (FibonacciTree α)} {minimum : α}
    (result : minRoot trees = some minimum) :
    (∃ tree ∈ trees, tree.root = minimum) ∧ ∀ tree ∈ trees, minimum ≤ tree.root := by
  induction trees generalizing minimum with
  | nil => simp [minRoot] at result
  | cons tree trees ih =>
      cases found : minRoot trees with
      | none =>
          have trees_empty := (minRoot_eq_none_iff trees).mp found
          subst trees
          simp only [minRoot, Option.some.injEq] at result
          refine ⟨⟨tree, by simp, result⟩, ?_⟩
          intro current member
          rw [List.mem_singleton] at member
          subst member
          exact le_of_eq result.symm
      | some tailMinimum =>
          have tail_spec := ih found
          simp only [minRoot, found, Option.some.injEq] at result
          have head_le : minimum ≤ tree.root := by
            rw [← result]
            exact min_le_left _ _
          have tail_le : minimum ≤ tailMinimum := by
            rw [← result]
            exact min_le_right _ _
          refine ⟨?_, ?_⟩
          · rcases le_total tree.root tailMinimum with order | order
            · have min_eq : min tree.root tailMinimum = tree.root := min_eq_left order
              exact ⟨tree, by simp, by rw [← result, min_eq]⟩
            · have min_eq : min tree.root tailMinimum = tailMinimum := min_eq_right order
              rcases tail_spec.1 with ⟨current, current_member, current_root⟩
              exact ⟨current, List.mem_cons_of_mem tree current_member,
                by rw [current_root, ← result, min_eq]⟩
          · intro current member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact head_le
            · exact tail_le.trans (tail_spec.2 current member)

/-- **Minimum root of a concatenated forest.** For forests $F$ and $G$ of Fibonacci trees over a
linearly ordered type, the minimum root of $F$ followed by $G$ is the combined minimum of the
optional minimum roots of $F$ and of $G$: their minimum if both exist, the one that exists if
only one does, and absent if neither does. -/
public theorem minRoot_append [LinearOrder α] (left right : List (FibonacciTree α)) :
    minRoot (left ++ right) = minOption (minRoot left) (minRoot right) := by
  induction left with
  | nil =>
      cases found : minRoot right <;> simp [minRoot, minOption, found]
  | cons tree left ih =>
      cases left_found : minRoot left <;> cases right_found : minRoot right <;>
        simp [minRoot, minOption, left_found, right_found, ih, min_assoc]

/-- **Inserting a tree into a forest.** Given a Fibonacci tree $t$ and a list of Fibonacci
trees, the insertion of $t$ into the list is defined recursively. Inserting $t$ into the empty
list gives the one-tree list $[t]$. For a list with first tree $s$ and remaining list $L$: if
the stored degree of $t$ is less than the stored degree of $s$, the result is $t$ followed by
$s$ and then $L$; if the two stored degrees are equal, the result is the insertion of the link
of $t$ and $s$ into $L$; otherwise the result is $s$ followed by the insertion of $t$ into $L$.

On a list whose stored degrees strictly increase, this links $t$ with any tree of equal degree
and carries the linked tree forward, as in binary addition. -/
@[expose] public def addTree [LinearOrder α] (tree : FibonacciTree α) :
    List (FibonacciTree α) → List (FibonacciTree α)
  | [] => [tree]
  | other :: trees =>
      if tree.degree < other.degree then
        tree :: other :: trees
      else if tree.degree = other.degree then
        addTree (tree.link other) trees
      else
        other :: addTree tree trees

theorem elements_addTree [LinearOrder α] (tree : FibonacciTree α)
    (trees : List (FibonacciTree α)) :
    elements (addTree tree trees) = tree.elements + elements trees := by
  induction trees generalizing tree with
  | nil => simp [addTree, elements]
  | cons other trees ih =>
      rw [addTree]
      split
      · rfl
      · split
        · rw [ih, FibonacciTree.elements_link]
          change (tree.elements + other.elements) + elements trees =
            tree.elements + (other.elements + elements trees)
          rw [Multiset.add_assoc]
        · change other.elements + elements (addTree tree trees) =
            tree.elements + (other.elements + elements trees)
          rw [ih, ← Multiset.add_assoc,
            Multiset.add_comm other.elements tree.elements, Multiset.add_assoc]

theorem valid_addTree [LinearOrder α] {tree : FibonacciTree α}
    {trees : List (FibonacciTree α)} (tree_valid : tree.Valid)
    (trees_valid : Valid trees) : Valid (addTree tree trees) := by
  induction trees generalizing tree with
  | nil =>
      intro current member
      simp only [addTree, List.mem_singleton] at member
      subst member
      exact tree_valid
  | cons other trees ih =>
      have head_valid : other.Valid := trees_valid other (by simp)
      have tail_valid : Valid trees :=
        fun current member => trees_valid current (List.mem_cons_of_mem other member)
      rw [addTree]
      split
      · intro current member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | member
        · exact tree_valid
        · exact head_valid
        · exact tail_valid current member
      · split
        · exact ih (tree_valid.link head_valid) tail_valid
        · intro current member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact head_valid
          · exact ih tree_valid tail_valid current member

private theorem addTree_degree_or_mem [LinearOrder α] {tree current : FibonacciTree α}
    {trees : List (FibonacciTree α)} (member : current ∈ addTree tree trees) :
    current ∈ trees ∨ tree.degree ≤ current.degree := by
  induction trees generalizing tree with
  | nil =>
      simp only [addTree, List.mem_singleton] at member
      subst member
      exact Or.inr le_rfl
  | cons other trees ih =>
      rw [addTree] at member
      split at member
      · simp only [List.mem_cons] at member
        rcases member with rfl | rfl | member
        · exact Or.inr le_rfl
        · exact Or.inl (by simp)
        · exact Or.inl (List.mem_cons_of_mem other member)
      · split at member
        · have degrees_eq : tree.degree = other.degree := by assumption
          rcases ih member with member | degree_le
          · exact Or.inl (List.mem_cons_of_mem other member)
          · have link_degree := FibonacciTree.degree_link_of_eq degrees_eq
            exact Or.inr (by omega)
        · simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact Or.inl (by simp)
          · rcases ih member with member | degree_le
            · exact Or.inl (List.mem_cons_of_mem other member)
            · exact Or.inr degree_le

private theorem sorted_addTree [LinearOrder α] {tree : FibonacciTree α}
    {trees : List (FibonacciTree α)} (sorted : SortedDegrees trees) :
    SortedDegrees (addTree tree trees) := by
  induction trees generalizing tree with
  | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons other trees ih =>
      have head_lt : ∀ current ∈ trees, other.degree < current.degree :=
        (List.pairwise_cons.mp sorted).1
      have tail_sorted : SortedDegrees trees := (List.pairwise_cons.mp sorted).2
      rw [addTree]
      split
      · rename_i degree_lt
        refine List.pairwise_cons.mpr ⟨?_, sorted⟩
        intro current member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact degree_lt
        · exact degree_lt.trans (head_lt current member)
      · split
        · exact ih tail_sorted
        · have degree_gt : other.degree < tree.degree := by
            have not_lt : ¬ tree.degree < other.degree := by assumption
            have not_eq : ¬ tree.degree = other.degree := by assumption
            omega
          refine List.pairwise_cons.mpr ⟨?_, ih tail_sorted⟩
          intro current member
          rcases addTree_degree_or_mem member with member | degree_le
          · exact head_lt current member
          · exact degree_gt.trans_le degree_le

/-- **Consolidation of a forest.** The consolidation of a list of Fibonacci trees is defined
recursively: the consolidation of the empty list is the empty list, and the consolidation of a
list with first tree $t$ and remaining list $L$ is the insertion of $t$ into the consolidation
of $L$.

Each insertion links trees of equal stored degree as in binary addition, so the result has
strictly increasing, hence distinct, stored root degrees, as in the consolidate step of CLRS. -/
@[expose] public def consolidate [LinearOrder α] :
    List (FibonacciTree α) → List (FibonacciTree α)
  | [] => []
  | tree :: trees => addTree tree (consolidate trees)

/-- **Consolidation preserves the elements.** For every list of Fibonacci trees over a linearly
ordered type, its consolidation represents the same multiset as the original list. -/
public theorem elements_consolidate [LinearOrder α] (trees : List (FibonacciTree α)) :
    elements (consolidate trees) = elements trees := by
  induction trees with
  | nil => rfl
  | cons tree trees ih =>
      rw [consolidate, elements_addTree, ih]
      rfl

/-- **Consolidation preserves validity.** Let $\alpha$ be a linearly ordered type. If a
Fibonacci forest with values in $\alpha$ is valid, then its consolidation is valid. -/
public theorem valid_consolidate [LinearOrder α] {trees : List (FibonacciTree α)}
    (valid : Valid trees) : Valid (consolidate trees) := by
  induction trees with
  | nil => exact valid
  | cons tree trees ih =>
      rw [consolidate]
      exact valid_addTree (valid tree (by simp))
        (ih (fun current member => valid current (List.mem_cons_of_mem tree member)))

/-- **Consolidation sorts root degrees.** For every list of Fibonacci trees, the stored degrees
of the trees in its consolidation are strictly increasing in list order. -/
public theorem consolidate_sorted [LinearOrder α] (trees : List (FibonacciTree α)) :
    SortedDegrees (consolidate trees) := by
  induction trees with
  | nil => exact List.Pairwise.nil
  | cons tree trees ih =>
      rw [consolidate]
      exact sorted_addTree ih

/-- **Consolidation yields distinct root degrees.** For every list of Fibonacci trees, the trees
in its consolidation have pairwise distinct stored degrees. -/
public theorem consolidate_degrees_nodup [LinearOrder α]
    (trees : List (FibonacciTree α)) :
    ((consolidate trees).map FibonacciTree.degree).Nodup :=
  (List.pairwise_map.mpr (consolidate_sorted trees)).nodup

/-- **Degree-sorted forests have at most as many trees as elements.** Let $F$ be a valid forest
of Fibonacci trees whose degrees are strictly increasing along the list. Then the number of
trees in $F$ is at most the number of elements, counted with multiplicity, that $F$ represents.

Every degree is smaller than the total element count and the degrees are distinct. -/
public theorem length_le_card_of_sorted [LE α] {trees : List (FibonacciTree α)}
    (valid : Valid trees) (sorted : SortedDegrees trees) :
    trees.length ≤ (elements trees).card := by
  have nodup : (trees.map FibonacciTree.degree).Nodup :=
    (List.pairwise_map.mpr sorted).nodup
  have subset : trees.map FibonacciTree.degree ⊆ List.range (elements trees).card := by
    intro storedDegree member
    rcases List.mem_map.mp member with ⟨tree, tree_member, rfl⟩
    have degree_lt : tree.degree < (elements trees).card :=
      (valid tree tree_member).degree_lt_card.trans_le (card_elements_le_card tree_member)
    simpa using degree_lt
  simpa using nodup.length_le_of_subset subset

/-- **Removing a minimum tree from a Fibonacci forest.** For a list of Fibonacci trees over a
linearly ordered type, this returns nothing on the empty list. Otherwise it returns the first tree
whose root is minimal among all roots in the list, so earlier trees win ties, together with the list
of the remaining trees in their original order. -/
@[expose] public def removeMinTree [LinearOrder α] :
    List (FibonacciTree α) → Option (FibonacciTree α × List (FibonacciTree α))
  | [] => none
  | tree :: trees =>
      match removeMinTree trees with
      | none => some (tree, [])
      | some (minimum, rest) =>
          if minimum.root < tree.root then
            some (minimum, tree :: rest)
          else
            some (tree, trees)

theorem removeMinTree_eq_none_iff [LinearOrder α]
    (trees : List (FibonacciTree α)) : removeMinTree trees = none ↔ trees = [] := by
  cases trees with
  | nil => simp [removeMinTree]
  | cons tree trees =>
      cases found : removeMinTree trees with
      | none => simp [removeMinTree, found]
      | some result =>
          rcases result with ⟨minimum, rest⟩
          by_cases less : minimum.root < tree.root <;>
            simp [removeMinTree, found, less]

/-- **Minimum-tree removal in a Fibonacci forest.** Let $T$ be a list of Fibonacci trees over a
linearly ordered type. If removing a minimum tree from $T$ returns a tree $m$ and a list $R$, then
the multiset of elements of $m$ plus the multiset of elements of $R$ equals the multiset of elements
of $T$, the tree $m$ belongs to $T$, the list $R$ is a sublist of $T$, and the root of $m$ is at
most the root of every tree in $T$. -/
public theorem removeMinTree_spec [LinearOrder α]
    {trees : List (FibonacciTree α)} {minimum : FibonacciTree α}
    {rest : List (FibonacciTree α)} (result : removeMinTree trees = some (minimum, rest)) :
    minimum.elements + elements rest = elements trees ∧
      minimum ∈ trees ∧ rest.Sublist trees ∧
      ∀ tree ∈ trees, minimum.root ≤ tree.root := by
  induction trees generalizing minimum rest with
  | nil => simp [removeMinTree] at result
  | cons tree trees ih =>
      cases found : removeMinTree trees with
      | none =>
          have trees_empty := (removeMinTree_eq_none_iff trees).mp found
          subst trees
          simp only [removeMinTree] at result
          simp only [Option.some.injEq, Prod.mk.injEq] at result
          rcases result with ⟨rfl, rfl⟩
          simp [elements]
      | some selected =>
          rcases selected with ⟨tailMinimum, tailRest⟩
          have tail_spec := ih found
          by_cases less : tailMinimum.root < tree.root
          · simp only [removeMinTree, found, less, ite_true, Option.some.injEq,
              Prod.mk.injEq] at result
            rcases result with ⟨rfl, rfl⟩
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [elements, List.map_cons, List.sum_cons]
              change tailMinimum.elements + (tree.elements + elements tailRest) =
                tree.elements + elements trees
              rw [← tail_spec.1]
              rw [← Multiset.add_assoc,
                Multiset.add_comm tailMinimum.elements tree.elements,
                Multiset.add_assoc]
            · simp [tail_spec.2.1]
            · exact tail_spec.2.2.1.cons_cons tree
            · intro current member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact le_of_lt less
              · exact tail_spec.2.2.2 current member
          · simp only [removeMinTree, found, less, ite_false, Option.some.injEq,
              Prod.mk.injEq] at result
            rcases result with ⟨rfl, rfl⟩
            refine ⟨by rfl, by simp, by simp, ?_⟩
            intro current member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact le_rfl
            · exact (le_of_not_gt less).trans (tail_spec.2.2.2 current member)

theorem removeMinTree_root_le [LinearOrder α] {trees : List (FibonacciTree α)}
    {minimum : FibonacciTree α} {rest : List (FibonacciTree α)}
    (valid : Valid trees) (result : removeMinTree trees = some (minimum, rest))
    {value : α} (member : value ∈ elements trees) : minimum.root ≤ value := by
  have spec := removeMinTree_spec result
  rcases mem_elements_iff.mp member with ⟨tree, tree_mem, value_mem⟩
  exact (spec.2.2.2 tree tree_mem).trans ((valid tree tree_mem).root_le value_mem)

theorem root_cons_elements_children (tree : FibonacciTree α) :
    tree.root ::ₘ elements tree.children = tree.elements := by
  cases tree
  simp only [FibonacciTree.root, FibonacciTree.children, FibonacciTree.elements, elements]

end FibonacciForest

/-- **Fibonacci heap.** A Fibonacci min-heap over a linearly ordered type consists of a list of
Fibonacci trees, each valid (heap-ordered, and at every node the stored degree equals the number
of children), together with a cached minimum equal to the least root value of these trees,
absent when the list is empty. -/
public structure FibonacciHeap (α : Type u) [LinearOrder α] where
  /-- The heap-ordered trees; root degrees may repeat between deletions. -/
  trees : List (FibonacciTree α)
  /-- The cached minimum element. -/
  cachedMin : Option α
  valid : FibonacciForest.Valid trees
  min_eq : cachedMin = FibonacciForest.minRoot trees

namespace FibonacciHeap

variable {α : Type u}

/-- **Multiset of a Fibonacci heap.** The multiset represented by a Fibonacci heap over a linearly
ordered type is the multiset of its list of trees: the sum, over the trees in the list, of the
multisets of values stored in them. The cached minimum plays no role. -/
@[expose] public def elements [LinearOrder α] (heap : FibonacciHeap α) : Multiset α :=
  FibonacciForest.elements heap.trees

/-- **Empty Fibonacci heap.** The Fibonacci heap over a linearly ordered type whose list of trees
is empty and whose cached minimum is absent. -/
@[expose] public def empty [LinearOrder α] : FibonacciHeap α :=
  ⟨[], none, FibonacciForest.valid_nil, rfl⟩

/-- **Singleton Fibonacci heap.** For a value $x$ of a linearly ordered type, the singleton
Fibonacci heap on $x$ has as its only tree the single-node tree with root $x$, stored degree $0$
and no children, and its cached minimum is $x$. -/
@[expose] public def singleton [LinearOrder α] (value : α) : FibonacciHeap α :=
  ⟨[FibonacciTree.singleton value], some value, by
    intro tree member
    simp only [List.mem_singleton] at member
    subst member
    exact FibonacciTree.valid_singleton value, by
    simp [FibonacciForest.minRoot, FibonacciTree.singleton, FibonacciTree.root]⟩

/-- **Melding Fibonacci heaps.** The meld of Fibonacci heaps $H_1$ and $H_2$ is the Fibonacci heap
whose root list is the root list of $H_1$ followed by that of $H_2$, and whose cached minimum is
the smaller of the two cached minima when both heaps have one, and otherwise the cached minimum
of whichever heap has one (none if neither does).

No linking happens until the next minimum deletion. -/
@[expose] public def meld [LinearOrder α] (left right : FibonacciHeap α) : FibonacciHeap α :=
  ⟨left.trees ++ right.trees,
    FibonacciForest.minOption left.cachedMin right.cachedMin,
    FibonacciForest.valid_append left.valid right.valid,
    by rw [FibonacciForest.minRoot_append, left.min_eq, right.min_eq]⟩

/-- **Union of Fibonacci heaps.** The union of Fibonacci heaps $H_1$ and $H_2$ is their meld: the
heap whose trees are those of $H_1$ followed by those of $H_2$, and whose cached minimum is the
smaller of the two cached minima (the one that exists if a heap is empty, none if both are).

CLRS calls this operation union. -/
@[expose] public def union [LinearOrder α] (left right : FibonacciHeap α) : FibonacciHeap α :=
  left.meld right

/-- **Insertion into a Fibonacci heap.** Inserting a value $x$ into a Fibonacci heap $H$ gives
the meld of the one-element Fibonacci heap containing $x$ with $H$, the one-element heap coming
first. -/
@[expose] public def insert [LinearOrder α] (heap : FibonacciHeap α) (value : α) :
    FibonacciHeap α :=
  (singleton value).meld heap

/-- **Find-min for Fibonacci heaps.** Find-min on a Fibonacci heap returns its cached minimum
without modifying the heap: the least root value of its trees, or no value when the heap has no
trees. -/
@[expose] public def findMin [LinearOrder α] (heap : FibonacciHeap α) : Option α :=
  heap.cachedMin

/-- **Minimum deletion on a forest.** Given a list of Fibonacci trees over a linearly ordered type,
the result is nothing if the list is empty. Otherwise the first tree whose root is minimal is
removed, and the result is its root value together with the consolidation of the forest made of
the removed tree's children followed by the remaining trees.

This is the forest-level computation behind deleting the minimum of a Fibonacci heap, without the
validity proofs. -/
@[expose] public def deleteMinTrees [LinearOrder α]
    (trees : List (FibonacciTree α)) : Option (α × List (FibonacciTree α)) :=
  match FibonacciForest.removeMinTree trees with
  | none => none
  | some (minimum, rest) =>
      some (minimum.root, FibonacciForest.consolidate (minimum.children ++ rest))

/-- **Deleting the minimum of a Fibonacci heap.** If the root list of the heap is empty, the result
is nothing. Otherwise the first tree of the root list whose root is minimal is removed, and the
result is its root value together with the heap whose root list is the consolidation of the
removed tree's children followed by the remaining trees, and whose cached minimum is the minimum
root of this consolidated forest. -/
public def deleteMin [LinearOrder α]
    (heap : FibonacciHeap α) : Option (α × FibonacciHeap α) :=
  match found : FibonacciForest.removeMinTree heap.trees with
  | none => none
  | some (minimum, rest) =>
      have spec := FibonacciForest.removeMinTree_spec found
      have minimum_valid : minimum.Valid := heap.valid minimum spec.2.1
      have rest_valid : FibonacciForest.Valid rest := heap.valid.sublist spec.2.2.1
      have children_valid : FibonacciForest.Valid minimum.children :=
        fun _ member => minimum_valid.child_valid member
      have combined_valid : FibonacciForest.Valid (minimum.children ++ rest) :=
        FibonacciForest.valid_append children_valid rest_valid
      let trees := FibonacciForest.consolidate (minimum.children ++ rest)
      have trees_valid : FibonacciForest.Valid trees :=
        FibonacciForest.valid_consolidate combined_valid
      some (minimum.root, ⟨trees, FibonacciForest.minRoot trees, trees_valid, rfl⟩)

/-- **Fibonacci heap minimum deletion agrees with its root-list version.** For every Fibonacci
heap $H$, deleting the minimum of $H$ and keeping only the returned value and the root list
of the resulting heap gives the same result as the root-list minimum deletion applied to the
root list of $H$: either both fail, or both return the same value and the same list of
trees. -/
public theorem deleteMin_trees [LinearOrder α] (heap : FibonacciHeap α) :
    heap.deleteMin.map (fun result => (result.1, result.2.trees)) =
      deleteMinTrees heap.trees := by
  unfold deleteMin deleteMinTrees
  split <;> rename_i found <;> simp only [found] <;> rfl

/-- **The empty Fibonacci heap has no elements.** The empty Fibonacci heap represents the empty
multiset. -/
public theorem elements_empty [LinearOrder α] : (empty : FibonacciHeap α).elements = 0 := by
  simp [empty, elements, FibonacciForest.elements]

/-- **Multiset of a singleton Fibonacci heap.** For every value $x$ of a linearly ordered type, the
singleton Fibonacci heap on $x$, whose only tree is the single-node tree with root $x$, represents
the multiset $\{x\}$. -/
public theorem elements_singleton [LinearOrder α] (value : α) :
    (singleton value).elements = {value} := by
  simp [singleton, elements, FibonacciForest.elements]

/-- **Melding adds the elements.** For any two Fibonacci heaps $H_1$ and $H_2$ over a linearly
ordered type, the meld of $H_1$ and $H_2$ represents the sum of the multisets represented by
$H_1$ and by $H_2$. -/
public theorem elements_meld [LinearOrder α] (left right : FibonacciHeap α) :
    (left.meld right).elements = left.elements + right.elements := by
  simpa [meld, elements] using
    (FibonacciForest.elements_append left.trees right.trees)

/-- **The union of Fibonacci heaps adds their multisets.** For Fibonacci heaps $H_1$ and $H_2$ over
a linearly ordered type, the multiset represented by the union of $H_1$ and $H_2$ is the sum of
the multisets represented by $H_1$ and by $H_2$. -/
public theorem elements_union [LinearOrder α] (left right : FibonacciHeap α) :
    (left.union right).elements = left.elements + right.elements :=
  elements_meld left right

/-- **Insertion adds one occurrence.** For every Fibonacci heap $H$ over a linearly ordered type
and every value $x$, the heap obtained by inserting $x$ into $H$ represents the multiset of $H$
with one more occurrence of $x$. -/
public theorem elements_insert [LinearOrder α] (heap : FibonacciHeap α) (value : α) :
    (heap.insert value).elements = value ::ₘ heap.elements := by
  rw [insert, elements_meld]
  simp [singleton, elements, FibonacciForest.elements]

/-- **Melding adds the sizes of Fibonacci heaps.** For Fibonacci heaps $H_1$ and $H_2$, the number
of elements of the meld of $H_1$ and $H_2$, counted with multiplicity, is the number of
elements of $H_1$ plus the number of elements of $H_2$. -/
public theorem card_elements_meld [LinearOrder α] (left right : FibonacciHeap α) :
    (left.meld right).elements.card = left.elements.card + right.elements.card := by
  rw [elements_meld, Multiset.card_add]

/-- **Insertion increases the size of a Fibonacci heap by one.** For every Fibonacci heap $H$
and every value $x$, the number of elements of the heap obtained by inserting $x$ into $H$,
counted with multiplicity, is the number of elements of $H$ plus one. -/
public theorem card_elements_insert [LinearOrder α] (heap : FibonacciHeap α) (value : α) :
    (heap.insert value).elements.card = heap.elements.card + 1 := by
  rw [elements_insert, Multiset.card_cons]

/-- **Find-min fails exactly on the empty Fibonacci heap.** For a Fibonacci heap $H$ over a
linearly ordered type, find-min on $H$ returns no value if and only if $H$ has no trees. -/
public theorem findMin_eq_none_iff [LinearOrder α] (heap : FibonacciHeap α) :
    heap.findMin = none ↔ heap.trees = [] := by
  show heap.cachedMin = none ↔ heap.trees = []
  rw [heap.min_eq]
  exact FibonacciForest.minRoot_eq_none_iff heap.trees

/-- **Find-min returns an element of the Fibonacci heap.** Let $H$ be a Fibonacci heap over a
linearly ordered type. If find-min on $H$ returns $m$, then $m$ belongs to the multiset
represented by $H$. -/
public theorem findMin_mem [LinearOrder α] {heap : FibonacciHeap α} {minimum : α}
    (result : heap.findMin = some minimum) : minimum ∈ heap.elements := by
  have min_root : FibonacciForest.minRoot heap.trees = some minimum := by
    rw [← heap.min_eq]
    exact result
  rcases (FibonacciForest.minRoot_spec min_root).1 with ⟨tree, tree_member, root_eq⟩
  change minimum ∈ FibonacciForest.elements heap.trees
  rw [FibonacciForest.mem_elements_iff]
  exact ⟨tree, tree_member, by
    rw [← root_eq]
    exact FibonacciTree.root_mem_elements tree⟩

/-- **Find-min returns a lower bound of the Fibonacci heap.** Let $H$ be a Fibonacci heap over a
linearly ordered type. If find-min on $H$ returns $m$, then $m \le v$ for every value $v$ in the
multiset represented by $H$. -/
public theorem findMin_le [LinearOrder α] {heap : FibonacciHeap α} {minimum value : α}
    (result : heap.findMin = some minimum) (member : value ∈ heap.elements) :
    minimum ≤ value := by
  have min_root : FibonacciForest.minRoot heap.trees = some minimum := by
    rw [← heap.min_eq]
    exact result
  have spec := FibonacciForest.minRoot_spec min_root
  change value ∈ FibonacciForest.elements heap.trees at member
  rcases FibonacciForest.mem_elements_iff.mp member with ⟨tree, tree_member, value_member⟩
  exact (spec.2 tree tree_member).trans ((heap.valid tree tree_member).root_le value_member)

theorem deleteMin_partition [LinearOrder α] {heap : FibonacciHeap α} {minimum : α}
    {rest : FibonacciHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    have spec := FibonacciForest.removeMinTree_spec found
    change tree.root ::ₘ
        FibonacciForest.elements
          (FibonacciForest.consolidate (tree.children ++ remaining)) =
      FibonacciForest.elements heap.trees
    rw [FibonacciForest.elements_consolidate, FibonacciForest.elements_append,
      ← Multiset.cons_add, FibonacciForest.root_cons_elements_children, spec.1]

/-- **Fibonacci heap minimum deletion fails exactly on the empty heap.** Deleting the minimum
of a Fibonacci heap fails if and only if the heap's list of root trees is empty. -/
public theorem deleteMin_eq_none_iff [LinearOrder α] (heap : FibonacciHeap α) :
    heap.deleteMin = none ↔ heap.trees = [] := by
  unfold deleteMin
  split
  · rename_i found
    exact ⟨fun _ => (FibonacciForest.removeMinTree_eq_none_iff heap.trees).mp found,
      fun _ => rfl⟩
  · rename_i tree remaining found
    constructor
    · intro impossible
      contradiction
    · intro trees_empty
      have none_found : FibonacciForest.removeMinTree heap.trees = none :=
        (FibonacciForest.removeMinTree_eq_none_iff heap.trees).mpr trees_empty
      rw [none_found] at found
      contradiction

/-- **Fibonacci heap minimum deletion removes one copy of the minimum.** If deleting the
minimum of a Fibonacci heap $H$ succeeds and returns the value $m$ and the heap $H'$, then the
multiset of elements of $H'$ is the multiset of elements of $H$ with one occurrence of $m$
removed. -/
public theorem deleteMin_elements [LinearOrder α] {heap : FibonacciHeap α} {minimum : α}
    {rest : FibonacciHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    rest.elements = heap.elements.erase minimum := by
  rw [← deleteMin_partition result, Multiset.erase_cons_head]

/-- **Fibonacci heap minimum deletion splits off the minimum.** If deleting the minimum of a
Fibonacci heap $H$ succeeds and returns the value $m$ and the heap $H'$, then the multiset of
elements of $H$ is the multiset of elements of $H'$ with one copy of $m$ added. -/
public theorem deleteMin_cons_elements [LinearOrder α] {heap : FibonacciHeap α}
    {minimum : α} {rest : FibonacciHeap α}
    (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements :=
  deleteMin_partition result

/-- **Fibonacci heap minimum deletion returns a lower bound.** If deleting the minimum of a
Fibonacci heap $H$ succeeds and returns the value $m$, then $m \le v$ for every element $v$
of $H$. -/
public theorem deleteMin_le [LinearOrder α] {heap : FibonacciHeap α} {minimum value : α}
    {rest : FibonacciHeap α} (result : heap.deleteMin = some (minimum, rest))
    (member : value ∈ heap.elements) : minimum ≤ value := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact FibonacciForest.removeMinTree_root_le heap.valid found member

/-- **Minimum deletion leaves a Fibonacci heap with strictly increasing root degrees.** If
deleting the minimum of a Fibonacci heap succeeds and returns the heap $H'$, then the degrees
of the root trees of $H'$, in list order, are strictly increasing; consolidation is what
makes them so. -/
public theorem deleteMin_sortedDegrees [LinearOrder α] {heap : FibonacciHeap α}
    {minimum : α} {rest : FibonacciHeap α}
    (result : heap.deleteMin = some (minimum, rest)) :
    FibonacciForest.SortedDegrees rest.trees := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact FibonacciForest.consolidate_sorted _

/-- **After minimum deletion a Fibonacci heap has at most as many roots as elements.** If
deleting the minimum of a Fibonacci heap succeeds and returns the heap $H'$, then the number
of root trees of $H'$ is at most the number of elements of $H'$, counted with multiplicity. -/
public theorem deleteMin_length_le_card [LinearOrder α] {heap : FibonacciHeap α}
    {minimum : α} {rest : FibonacciHeap α}
    (result : heap.deleteMin = some (minimum, rest)) :
    rest.trees.length ≤ rest.elements.card :=
  FibonacciForest.length_le_card_of_sorted rest.valid (deleteMin_sortedDegrees result)

end FibonacciHeap

end Cslib.Algorithms.Lean
