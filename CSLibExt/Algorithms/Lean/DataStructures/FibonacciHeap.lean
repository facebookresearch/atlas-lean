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

/-- A heap-ordered rose tree used by a Fibonacci heap. The stored degree is the number of
children. -/
public inductive FibonacciTree (α : Type u) where
  | node (degree : Nat) (root : α) (children : List (FibonacciTree α))
deriving Repr

namespace FibonacciTree

variable {α : Type u}

/-- The stored degree of a Fibonacci tree. -/
@[expose] public def degree : FibonacciTree α → Nat
  | .node degree _ _ => degree

/-- The root value of a Fibonacci tree. -/
@[expose] public def root : FibonacciTree α → α
  | .node _ root _ => root

/-- The children of a Fibonacci tree. -/
@[expose] public def children : FibonacciTree α → List (FibonacciTree α)
  | .node _ _ children => children

/-- The multiset represented by a Fibonacci tree. -/
@[expose] public def elements : FibonacciTree α → Multiset α
  | .node _ root children => root ::ₘ (children.map elements).sum

/-- A tree's root occurs in its represented multiset. -/
public theorem root_mem_elements (tree : FibonacciTree α) : tree.root ∈ tree.elements := by
  cases tree
  simp [root, elements]

/-- Every Fibonacci tree represents at least one element. -/
public theorem card_elements_pos (tree : FibonacciTree α) : 0 < tree.elements.card := by
  cases tree
  simp [elements]

/-- A Fibonacci tree has recursively valid children, stored degree equal to the number of
children, and a globally minimal root. -/
public inductive Valid {α : Type u} [LE α] : FibonacciTree α → Prop
  | node {degree : Nat} {root : α} {children : List (FibonacciTree α)}
      (children_valid : ∀ child ∈ children, Valid child)
      (degree_eq : degree = children.length)
      (root_le : ∀ value ∈ elements (.node degree root children), root ≤ value) :
      Valid (.node degree root children)

/-- A degree-zero tree containing one value. -/
@[expose] public def singleton (value : α) : FibonacciTree α :=
  .node 0 value []

/-- Link two trees by making the tree with the larger root a child of the other, retaining
the left root when the roots compare equal. -/
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

/-- Linking trees of equal degree increments that degree. -/
public theorem degree_link_of_eq [LinearOrder α] {left right : FibonacciTree α}
    (degrees : left.degree = right.degree) :
    (link left right).degree = left.degree + 1 := by
  rw [link]
  split
  · rfl
  · show right.degree + 1 = left.degree + 1
    rw [degrees]

/-- Linking preserves the disjoint multiset union of both input trees. -/
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

/-- A singleton tree satisfies every Fibonacci-tree invariant. -/
public theorem valid_singleton [LinearOrder α] (value : α) : Valid (singleton value) := by
  constructor
  · simp
  · rfl
  · simp [elements]

/-- Every child of a valid tree is valid. -/
public theorem Valid.child_valid [LE α] {tree child : FibonacciTree α}
    (valid : Valid tree) (member : child ∈ tree.children) : Valid child := by
  cases valid with
  | node children_valid _ _ => exact children_valid child member

/-- The stored degree of a valid tree is its number of children. -/
public theorem Valid.degree_eq [LE α] {tree : FibonacciTree α} (valid : Valid tree) :
    tree.degree = tree.children.length := by
  cases valid with
  | node _ degree_eq _ => exact degree_eq

/-- The root of a valid tree is no greater than every represented element. -/
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

/-- The degree of a valid tree is smaller than its element count, since every child
contributes at least one element. -/
public theorem Valid.degree_lt_card [LE α] {tree : FibonacciTree α} (valid : Valid tree) :
    tree.degree < tree.elements.card := by
  cases tree with
  | node storedDegree storedRoot storedChildren =>
      have degree_eq := valid.degree_eq
      have bound := length_le_card_sum storedChildren
      simp only [FibonacciTree.degree, FibonacciTree.children] at degree_eq
      simp only [FibonacciTree.degree, FibonacciTree.elements, Multiset.card_cons]
      omega

/-- Linking valid trees preserves all tree invariants. -/
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

/-- A Fibonacci forest is valid when every tree in it is valid. Root degrees may repeat;
consolidation below is what makes them distinct. -/
@[expose] public def FibonacciForest.Valid {α : Type u} [LE α]
    (trees : List (FibonacciTree α)) : Prop :=
  ∀ tree ∈ trees, tree.Valid

namespace FibonacciForest

variable {α : Type u}

/-- The multiset represented by a forest. -/
@[expose] public def elements (trees : List (FibonacciTree α)) : Multiset α :=
  (trees.map FibonacciTree.elements).sum

/-- The trees of a forest have strictly increasing degrees. -/
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

/-- The empty forest is valid. -/
public theorem valid_nil [LE α] : Valid ([] : List (FibonacciTree α)) := by
  intro tree member
  simp at member

/-- The concatenation of valid forests is valid. -/
public theorem valid_append [LE α] {left right : List (FibonacciTree α)}
    (left_valid : Valid left) (right_valid : Valid right) : Valid (left ++ right) := by
  intro tree member
  rw [List.mem_append] at member
  rcases member with member | member
  · exact left_valid tree member
  · exact right_valid tree member

/-- Forest validity is preserved by sublists. -/
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

/-- The elements of a concatenated forest are the sum of the elements of its parts. -/
public theorem elements_append (left right : List (FibonacciTree α)) :
    elements (left ++ right) = elements left + elements right := by
  simp only [elements, List.map_append]
  rw [sum_append]

/-- The minimum root value in a forest, or `none` for the empty forest. -/
@[expose] public def minRoot [LinearOrder α] : List (FibonacciTree α) → Option α
  | [] => none
  | tree :: trees =>
      match minRoot trees with
      | none => some tree.root
      | some minimum => some (min tree.root minimum)

/-- Combine two optional minima. -/
@[expose] public def minOption [LinearOrder α] (left right : Option α) : Option α :=
  match left, right with
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/-- A forest has no minimum root exactly when it is empty. -/
public theorem minRoot_eq_none_iff [LinearOrder α] (trees : List (FibonacciTree α)) :
    minRoot trees = none ↔ trees = [] := by
  cases trees with
  | nil => simp [minRoot]
  | cons tree trees =>
      cases found : minRoot trees with
      | none => simp [minRoot, found]
      | some minimum => simp [minRoot, found]

/-- The minimum root is the root of some tree in the forest and is no greater than
every root in the forest. -/
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

/-- The minimum root of a concatenated forest combines the minima of its parts. -/
public theorem minRoot_append [LinearOrder α] (left right : List (FibonacciTree α)) :
    minRoot (left ++ right) = minOption (minRoot left) (minRoot right) := by
  induction left with
  | nil =>
      cases found : minRoot right <;> simp [minRoot, minOption, found]
  | cons tree left ih =>
      cases left_found : minRoot left <;> cases right_found : minRoot right <;>
        simp [minRoot, minOption, left_found, right_found, ih, min_assoc]

/-- Insert a tree into a degree-sorted forest, linking it with any tree of equal degree
and carrying the link forward, as in binary addition. -/
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

/-- Consolidate a forest by linking trees of equal degree until all root degrees are
distinct, as in the `consolidate` step of CLRS. The result is sorted by degree. -/
@[expose] public def consolidate [LinearOrder α] :
    List (FibonacciTree α) → List (FibonacciTree α)
  | [] => []
  | tree :: trees => addTree tree (consolidate trees)

/-- Consolidation preserves every occurrence in the forest. -/
public theorem elements_consolidate [LinearOrder α] (trees : List (FibonacciTree α)) :
    elements (consolidate trees) = elements trees := by
  induction trees with
  | nil => rfl
  | cons tree trees ih =>
      rw [consolidate, elements_addTree, ih]
      rfl

/-- Consolidation preserves forest validity. -/
public theorem valid_consolidate [LinearOrder α] {trees : List (FibonacciTree α)}
    (valid : Valid trees) : Valid (consolidate trees) := by
  induction trees with
  | nil => exact valid
  | cons tree trees ih =>
      rw [consolidate]
      exact valid_addTree (valid tree (by simp))
        (ih (fun current member => valid current (List.mem_cons_of_mem tree member)))

/-- A consolidated forest has strictly increasing root degrees. -/
public theorem consolidate_sorted [LinearOrder α] (trees : List (FibonacciTree α)) :
    SortedDegrees (consolidate trees) := by
  induction trees with
  | nil => exact List.Pairwise.nil
  | cons tree trees ih =>
      rw [consolidate]
      exact sorted_addTree ih

/-- A consolidated forest has distinct root degrees. -/
public theorem consolidate_degrees_nodup [LinearOrder α]
    (trees : List (FibonacciTree α)) :
    ((consolidate trees).map FibonacciTree.degree).Nodup :=
  (List.pairwise_map.mpr (consolidate_sorted trees)).nodup

/-- A valid forest with distinct degrees has at most as many roots as elements, since
every degree is smaller than the total count. -/
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

/-- Remove the first tree whose root is minimal, preferring earlier trees on ties. -/
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

/-- Removing a minimum tree partitions the forest and returns a globally minimal root. -/
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

/-- A Fibonacci min-heap: a valid forest together with a cached minimum root value. -/
public structure FibonacciHeap (α : Type u) [LinearOrder α] where
  /-- The heap-ordered trees; root degrees may repeat between deletions. -/
  trees : List (FibonacciTree α)
  /-- The cached minimum element. -/
  cachedMin : Option α
  valid : FibonacciForest.Valid trees
  min_eq : cachedMin = FibonacciForest.minRoot trees

namespace FibonacciHeap

variable {α : Type u}

/-- The multiset represented by a Fibonacci heap. -/
@[expose] public def elements [LinearOrder α] (heap : FibonacciHeap α) : Multiset α :=
  FibonacciForest.elements heap.trees

/-- The empty Fibonacci heap. -/
@[expose] public def empty [LinearOrder α] : FibonacciHeap α :=
  ⟨[], none, FibonacciForest.valid_nil, rfl⟩

/-- A one-element Fibonacci heap. -/
@[expose] public def singleton [LinearOrder α] (value : α) : FibonacciHeap α :=
  ⟨[FibonacciTree.singleton value], some value, by
    intro tree member
    simp only [List.mem_singleton] at member
    subst member
    exact FibonacciTree.valid_singleton value, by
    simp [FibonacciForest.minRoot, FibonacciTree.singleton, FibonacciTree.root]⟩

/-- Meld two Fibonacci heaps: concatenate the root lists and keep the smaller cached
minimum. No linking happens until the next minimum deletion. -/
@[expose] public def meld [LinearOrder α] (left right : FibonacciHeap α) : FibonacciHeap α :=
  ⟨left.trees ++ right.trees,
    FibonacciForest.minOption left.cachedMin right.cachedMin,
    FibonacciForest.valid_append left.valid right.valid,
    by rw [FibonacciForest.minRoot_append, left.min_eq, right.min_eq]⟩

/-- `union` is the CLRS name for `meld`. -/
@[expose] public def union [LinearOrder α] (left right : FibonacciHeap α) : FibonacciHeap α :=
  left.meld right

/-- Insert one value into a Fibonacci heap by melding with a one-element heap. -/
@[expose] public def insert [LinearOrder α] (heap : FibonacciHeap α) (value : α) :
    FibonacciHeap α :=
  (singleton value).meld heap

/-- Inspect the minimum value (the cached minimum) without removing it. -/
@[expose] public def findMin [LinearOrder α] (heap : FibonacciHeap α) : Option α :=
  heap.cachedMin

/-- The computational forest projection of minimum deletion: remove a minimum tree,
promote its children, and consolidate. -/
@[expose] public def deleteMinTrees [LinearOrder α]
    (trees : List (FibonacciTree α)) : Option (α × List (FibonacciTree α)) :=
  match FibonacciForest.removeMinTree trees with
  | none => none
  | some (minimum, rest) =>
      some (minimum.root, FibonacciForest.consolidate (minimum.children ++ rest))

/-- Remove and return the minimum value. The children of the minimum tree become roots
and the root list is consolidated; the new cached minimum is the minimum root of the
consolidated forest. -/
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

/-- Projecting away the validity proofs from deletion gives `deleteMinTrees`. -/
public theorem deleteMin_trees [LinearOrder α] (heap : FibonacciHeap α) :
    heap.deleteMin.map (fun result => (result.1, result.2.trees)) =
      deleteMinTrees heap.trees := by
  unfold deleteMin deleteMinTrees
  split <;> rename_i found <;> simp only [found] <;> rfl

/-- The empty heap represents the empty multiset. -/
public theorem elements_empty [LinearOrder α] : (empty : FibonacciHeap α).elements = 0 := by
  simp [empty, elements, FibonacciForest.elements]

/-- A singleton heap represents a singleton multiset. -/
public theorem elements_singleton [LinearOrder α] (value : α) :
    (singleton value).elements = {value} := by
  simp [singleton, elements, FibonacciForest.elements]

/-- Meld preserves every occurrence from both heaps. -/
public theorem elements_meld [LinearOrder α] (left right : FibonacciHeap α) :
    (left.meld right).elements = left.elements + right.elements := by
  simpa [meld, elements] using
    (FibonacciForest.elements_append left.trees right.trees)

/-- Union preserves every occurrence from both heaps. -/
public theorem elements_union [LinearOrder α] (left right : FibonacciHeap α) :
    (left.union right).elements = left.elements + right.elements :=
  elements_meld left right

/-- Insertion adds exactly one occurrence. -/
public theorem elements_insert [LinearOrder α] (heap : FibonacciHeap α) (value : α) :
    (heap.insert value).elements = value ::ₘ heap.elements := by
  rw [insert, elements_meld]
  simp [singleton, elements, FibonacciForest.elements]

/-- Meld adds the element counts of both heaps. -/
public theorem card_elements_meld [LinearOrder α] (left right : FibonacciHeap α) :
    (left.meld right).elements.card = left.elements.card + right.elements.card := by
  rw [elements_meld, Multiset.card_add]

/-- Insertion increments the element count. -/
public theorem card_elements_insert [LinearOrder α] (heap : FibonacciHeap α) (value : α) :
    (heap.insert value).elements.card = heap.elements.card + 1 := by
  rw [elements_insert, Multiset.card_cons]

/-- Minimum inspection fails exactly for the empty heap. -/
public theorem findMin_eq_none_iff [LinearOrder α] (heap : FibonacciHeap α) :
    heap.findMin = none ↔ heap.trees = [] := by
  show heap.cachedMin = none ↔ heap.trees = []
  rw [heap.min_eq]
  exact FibonacciForest.minRoot_eq_none_iff heap.trees

/-- Minimum inspection returns a represented element. -/
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

/-- Minimum inspection returns a value no greater than every represented value. -/
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

/-- Deletion fails exactly for the empty heap. -/
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

/-- Successful deletion erases exactly one occurrence of the returned minimum. -/
public theorem deleteMin_elements [LinearOrder α] {heap : FibonacciHeap α} {minimum : α}
    {rest : FibonacciHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    rest.elements = heap.elements.erase minimum := by
  rw [← deleteMin_partition result, Multiset.erase_cons_head]

/-- Successful deletion partitions the original multiset into its minimum and remainder. -/
public theorem deleteMin_cons_elements [LinearOrder α] {heap : FibonacciHeap α}
    {minimum : α} {rest : FibonacciHeap α}
    (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements :=
  deleteMin_partition result

/-- Successful deletion returns a represented globally minimal value. -/
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

/-- After a successful deletion, consolidation has made the root degrees strictly
increasing. -/
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

/-- After a successful deletion, the heap has at most as many roots as elements. -/
public theorem deleteMin_length_le_card [LinearOrder α] {heap : FibonacciHeap α}
    {minimum : α} {rest : FibonacciHeap α}
    (result : heap.deleteMin = some (minimum, rest)) :
    rest.trees.length ≤ rest.elements.card :=
  FibonacciForest.length_le_card_of_sorted rest.valid (deleteMin_sortedDegrees result)

end FibonacciHeap

end Cslib.Algorithms.Lean
