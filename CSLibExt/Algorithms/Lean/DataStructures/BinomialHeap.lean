/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.AddSub

/-!
# Binomial min-heaps

This module implements persistent binomial trees and forests. A valid tree of rank `r` has
children of ranks `r - 1, ..., 0`, contains exactly `2 ^ r` elements, and has a root no greater
than any represented element. A valid heap is a forest whose tree ranks are strictly increasing.

`BinomialTree.link` retains its left argument as parent when the roots compare equal. The same
left-biased policy is used when selecting the minimum tree.

The machine-checked results establish the rank, size, order, forest, and multiset invariants.
There is no formal cost model here. Under constant-time comparison and constructor assumptions,
`link` takes constant time; insertion and minimum inspection visit at most the number of roots
`k`; and the implementation gives conservative worst-case bounds `O((k₁ + k₂) ^ 2)` for
meld and `O(k + r + (k + r) ^ 2)` for deleting a tree of rank `r`. The proved powers-of-two tree
sizes and unique ranks give the usual logarithmic bounds on `k` and `r` as a prose consequence,
not as a theorem about running time in this module.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- A ranked rose tree used by a binomial heap. -/
public inductive BinomialTree (α : Type u) where
  | node (rank : Nat) (root : α) (children : List (BinomialTree α))
deriving Repr

namespace BinomialTree

variable {α : Type u}

/-- The stored rank of a binomial tree. -/
@[expose] public def rank {α : Type u} : BinomialTree α → Nat
  | .node rank _ _ => rank

/-- The root value of a binomial tree. -/
@[expose] public def root {α : Type u} : BinomialTree α → α
  | .node _ root _ => root

/-- The children of a binomial tree, stored in decreasing rank order. -/
@[expose] public def children {α : Type u} : BinomialTree α → List (BinomialTree α)
  | .node _ _ children => children

/-- The multiset represented by a binomial tree. -/
@[expose] public def elements {α : Type u} : BinomialTree α → Multiset α
  | .node _ root children => root ::ₘ (children.map elements).sum

/-- A tree's root occurs in its represented multiset. -/
public theorem root_mem_elements (tree : BinomialTree α) : tree.root ∈ tree.elements := by
  cases tree
  simp [root, elements]

/-- A binomial tree has recursively valid children of ranks `r - 1, ..., 0`, exact size
`2 ^ r`, and a globally minimal root. -/
public inductive Valid {α : Type u} [LE α] : BinomialTree α → Prop
  | node {rank : Nat} {root : α} {children : List (BinomialTree α)}
      (children_valid : ∀ child ∈ children, Valid child)
      (children_ranks : children.map BinomialTree.rank = (List.range rank).reverse)
      (card_elements : (elements (.node rank root children)).card = 2 ^ rank)
      (root_le : ∀ value ∈ elements (.node rank root children), root ≤ value) :
      Valid (.node rank root children)

/-- A rank-zero tree containing one value. -/
@[expose] public def singleton (value : α) : BinomialTree α :=
  .node 0 value []

/-- Link two trees, retaining the left root when the roots compare equal. -/
@[expose] public def link [LinearOrder α] (left right : BinomialTree α) : BinomialTree α :=
  if left.root ≤ right.root then
    .node (left.rank + 1) left.root (right :: left.children)
  else
    .node (left.rank + 1) right.root (left :: right.children)

@[simp] public theorem rank_singleton (value : α) : (singleton value).rank = 0 := by
  rfl

@[simp] public theorem root_singleton (value : α) : (singleton value).root = value := by
  rfl

@[simp] public theorem children_singleton (value : α) :
    (singleton value).children = [] := by
  rfl

@[simp] public theorem elements_singleton (value : α) :
    (singleton value).elements = {value} := by
  simp [singleton, elements]

@[simp] public theorem rank_link [LinearOrder α] (left right : BinomialTree α) :
    (link left right).rank = left.rank + 1 := by
  rw [link]
  split <;> rfl

/-- Linking preserves the disjoint multiset union of both input trees. -/
public theorem elements_link [LinearOrder α] (left right : BinomialTree α) :
    (link left right).elements = left.elements + right.elements := by
  rw [link]
  split
  · cases left
    cases right
    simp only [root, rank, children, elements, List.map_cons, List.sum_cons]
    rw [Multiset.cons_add, Multiset.add_cons, Multiset.add_comm]
    simpa only [Multiset.cons_add] using Multiset.cons_swap _ _ _
  · cases left
    cases right
    simp only [root, rank, children, elements, List.map_cons, List.sum_cons]
    rw [Multiset.cons_add, Multiset.add_cons]
    simp only [Multiset.cons_add, Multiset.cons_swap]

/-- A singleton tree satisfies every binomial-tree invariant. -/
public theorem valid_singleton [LinearOrder α] (value : α) : Valid (singleton value) := by
  constructor
  · simp
  · rfl
  · simp [elements]
  · simp [elements]

/-- Every child of a valid tree is valid. -/
public theorem Valid.child_valid [LE α] {tree child : BinomialTree α}
    (valid : Valid tree) (member : child ∈ tree.children) : Valid child := by
  cases valid with
  | node children_valid _ _ _ => exact children_valid child member

/-- The child ranks of a valid tree are exactly `r - 1, ..., 0`. -/
public theorem Valid.children_ranks [LE α] {tree : BinomialTree α} (valid : Valid tree) :
    tree.children.map BinomialTree.rank = (List.range tree.rank).reverse := by
  cases valid with
  | node _ children_ranks _ _ => exact children_ranks

/-- A valid rank-`r` tree contains exactly `2 ^ r` elements. -/
public theorem Valid.card_elements [LE α] {tree : BinomialTree α} (valid : Valid tree) :
    tree.elements.card = 2 ^ tree.rank := by
  cases valid with
  | node _ _ card_elements _ => exact card_elements

/-- The root of a valid tree is no greater than every represented element. -/
public theorem Valid.root_le [LE α] {tree : BinomialTree α} (valid : Valid tree)
    {value : α} (member : value ∈ tree.elements) : tree.root ≤ value := by
  cases valid with
  | node _ _ _ root_le => exact root_le value member

/-- Linking equal-rank valid trees preserves all tree invariants. -/
public theorem Valid.link [LinearOrder α] {left right : BinomialTree α}
    (left_valid : Valid left) (right_valid : Valid right)
    (ranks : left.rank = right.rank) : Valid (link left right) := by
  rw [BinomialTree.link]
  split
  · rename_i root_le
    constructor
    · intro child member
      simp only [children, List.mem_cons] at member
      rcases member with rfl | member
      · exact right_valid
      · exact left_valid.child_valid member
    · simp only [children, rank, List.map_cons, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.cons.injEq]
      exact ⟨ranks.symm, left_valid.children_ranks⟩
    · have element_eq :
          (BinomialTree.node (left.rank + 1) left.root
            (right :: left.children)).elements = left.elements + right.elements := by
          simpa [BinomialTree.link, root_le] using elements_link left right
      rw [element_eq, Multiset.card_add, left_valid.card_elements,
        right_valid.card_elements, ← ranks, Nat.two_pow_succ]
    · intro value member
      have union_member : value ∈ left.elements + right.elements := by
        rw [← elements_link left right]
        simpa [BinomialTree.link, root_le] using member
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
    · simp only [children, rank, List.map_cons, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.cons.injEq]
      constructor
      · trivial
      · change right.children.map BinomialTree.rank =
          (List.range left.rank).reverse
        rw [right_valid.children_ranks]
        exact congrArg (fun rank => (List.range rank).reverse) ranks.symm
    · have element_eq :
          (BinomialTree.node (left.rank + 1) right.root
            (left :: right.children)).elements = left.elements + right.elements := by
          simpa [BinomialTree.link, not_le] using elements_link left right
      rw [element_eq, Multiset.card_add, left_valid.card_elements,
        right_valid.card_elements, ← ranks, Nat.two_pow_succ]
    · intro value member
      have union_member : value ∈ left.elements + right.elements := by
        rw [← elements_link left right]
        simpa [BinomialTree.link, not_le] using member
      rcases Multiset.mem_add.mp union_member with member | member
      · exact root_le.trans (left_valid.root_le member)
      · exact right_valid.root_le member

end BinomialTree

/-- A forest has valid trees at unique, strictly increasing ranks. -/
@[expose] public def BinomialForest.Valid {α : Type u} [LE α]
    (trees : List (BinomialTree α)) : Prop :=
  (∀ tree ∈ trees, tree.Valid) ∧
    (trees.map BinomialTree.rank).Pairwise (· < ·)

namespace BinomialForest

variable {α : Type u}

/-- The multiset represented by a forest. -/
@[expose] public def elements {α : Type u} (trees : List (BinomialTree α)) : Multiset α :=
  (trees.map BinomialTree.elements).sum

private theorem mem_elements_iff {trees : List (BinomialTree α)} {value : α} :
    value ∈ elements trees ↔ ∃ tree ∈ trees, value ∈ tree.elements := by
  induction trees with
  | nil => simp [elements]
  | cons tree trees ih =>
      change value ∈ tree.elements + elements trees ↔
        ∃ current ∈ tree :: trees, value ∈ current.elements
      rw [Multiset.mem_add, ih]
      simp

/-- Every tree in the forest has at least the given rank. -/
public def RanksAtLeast {α : Type u} (rank : Nat)
    (trees : List (BinomialTree α)) : Prop :=
  ∀ tree ∈ trees, rank ≤ tree.rank

/-- The empty forest is valid. -/
public theorem valid_nil [LE α] : Valid ([] : List (BinomialTree α)) := by
  simp [Valid]

private theorem Valid.head_valid [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (valid : Valid (tree :: trees)) : tree.Valid := by
  exact valid.1 tree (by simp)

private theorem Valid.tail [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (valid : Valid (tree :: trees)) : Valid trees := by
  constructor
  · intro current member
    exact valid.1 current (by simp [member])
  · simpa [List.pairwise_map] using valid.2.tail

private theorem Valid.head_lt [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (valid : Valid (tree :: trees))
    {other : BinomialTree α} (member : other ∈ trees) : tree.rank < other.rank := by
  rw [Valid, List.map_cons, List.pairwise_cons] at valid
  exact valid.2.1 other.rank (List.mem_map.mpr ⟨other, member, rfl⟩)

theorem valid_cons [LE α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (tree_valid : tree.Valid) (trees_valid : Valid trees)
    (rank_lt : ∀ other ∈ trees, tree.rank < other.rank) : Valid (tree :: trees) := by
  rw [Valid, List.map_cons, List.pairwise_cons]
  constructor
  · intro current member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact tree_valid
    · exact trees_valid.1 current member
  · refine ⟨?_, trees_valid.2⟩
    intro rank member
    rcases List.mem_map.mp member with ⟨other, other_mem, rfl⟩
    exact rank_lt other other_mem

/-- Forest validity is preserved by sublists. -/
public theorem Valid.sublist [LE α] {left right : List (BinomialTree α)}
    (sublist : left.Sublist right) (valid : Valid right) : Valid left := by
  constructor
  · intro tree member
    exact valid.1 tree (sublist.subset member)
  · exact valid.2.sublist (sublist.map BinomialTree.rank)

/-- Insert a tree whose rank is no greater than every forest rank, propagating equal-rank
links as a binary carry. -/
@[expose] public def carry [LinearOrder α] (tree : BinomialTree α) :
    List (BinomialTree α) → List (BinomialTree α)
  | [] => [tree]
  | other :: trees =>
      if tree.rank < other.rank then
        tree :: other :: trees
      else
        carry (tree.link other) trees

private theorem elements_carry [LinearOrder α] (tree : BinomialTree α)
    (trees : List (BinomialTree α)) :
    elements (carry tree trees) = tree.elements + elements trees := by
  induction trees generalizing tree with
  | nil => simp [carry, elements]
  | cons other trees ih =>
      rw [carry]
      split
      · simp [elements]
      · rw [ih, BinomialTree.elements_link]
        simp only [elements, List.map_cons, List.sum_cons]
        rw [Multiset.add_assoc]

private theorem carry_correct [LinearOrder α] {tree : BinomialTree α}
    {trees : List (BinomialTree α)} (tree_valid : tree.Valid) (trees_valid : Valid trees)
    (lower : RanksAtLeast tree.rank trees) :
    Valid (carry tree trees) ∧ RanksAtLeast tree.rank (carry tree trees) := by
  induction trees generalizing tree with
  | nil =>
      constructor
      · exact valid_cons tree_valid valid_nil (by simp)
      · simp [carry, RanksAtLeast]
  | cons other trees ih =>
      rw [carry]
      split
      · rename_i rank_lt
        constructor
        · apply valid_cons tree_valid trees_valid
          intro current member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact rank_lt
          · exact rank_lt.trans (trees_valid.head_lt member)
        · intro current member
          by_cases equal : current = tree
          · subst current
            exact Nat.le_refl tree.rank
          · exact lower current (by simpa [equal] using member)
      · rename_i not_lt
        have rank_le : tree.rank ≤ other.rank := lower other (by simp)
        have ranks : tree.rank = other.rank :=
          Nat.le_antisymm rank_le (Nat.le_of_not_gt not_lt)
        have linked_valid := tree_valid.link trees_valid.head_valid ranks
        have linked_lower : RanksAtLeast (tree.link other).rank trees := by
          intro current member
          rw [BinomialTree.rank_link, ranks]
          exact trees_valid.head_lt member
        have result := ih linked_valid trees_valid.tail linked_lower
        exact ⟨result.1, fun current member => by
          have := result.2 current member
          rw [BinomialTree.rank_link] at this
          omega⟩

/-- Merge two increasing-rank forests, linking equal-rank trees and propagating carries. -/
@[expose] public def meldTrees [LinearOrder α] :
    List (BinomialTree α) → List (BinomialTree α) → List (BinomialTree α)
  | [], right => right
  | left, [] => left
  | leftTree :: leftTrees, rightTree :: rightTrees =>
      if leftTree.rank < rightTree.rank then
        leftTree :: meldTrees leftTrees (rightTree :: rightTrees)
      else if rightTree.rank < leftTree.rank then
        rightTree :: meldTrees (leftTree :: leftTrees) rightTrees
      else
        carry (leftTree.link rightTree) (meldTrees leftTrees rightTrees)
termination_by left right => left.length + right.length

/-- Forest meld preserves every occurrence from both inputs. -/
theorem elements_meldTrees [LinearOrder α]
    (left right : List (BinomialTree α)) :
    elements (meldTrees left right) = elements left + elements right := by
  cases left with
  | nil => simp [meldTrees, elements]
  | cons leftTree leftTrees =>
      cases right with
      | nil => simp [meldTrees, elements]
      | cons rightTree rightTrees =>
          rw [meldTrees]
          split
          · change leftTree.elements +
                elements (meldTrees leftTrees (rightTree :: rightTrees)) =
              (leftTree.elements + elements leftTrees) +
                elements (rightTree :: rightTrees)
            rw [elements_meldTrees leftTrees (rightTree :: rightTrees)]
            rw [Multiset.add_assoc]
          · split
            · change rightTree.elements +
                  elements (meldTrees (leftTree :: leftTrees) rightTrees) =
                elements (leftTree :: leftTrees) +
                  (rightTree.elements + elements rightTrees)
              rw [elements_meldTrees (leftTree :: leftTrees) rightTrees]
              exact calc
                rightTree.elements +
                    (elements (leftTree :: leftTrees) + elements rightTrees) =
                    (rightTree.elements + elements (leftTree :: leftTrees)) +
                      elements rightTrees := (Multiset.add_assoc _ _ _).symm
                _ =
                    (elements (leftTree :: leftTrees) + rightTree.elements) +
                      elements rightTrees := congrArg
                        (fun values => values + elements rightTrees)
                        (Multiset.add_comm _ _)
                _ = elements (leftTree :: leftTrees) +
                    (rightTree.elements + elements rightTrees) :=
                      Multiset.add_assoc _ _ _
            · rw [elements_carry, BinomialTree.elements_link,
                elements_meldTrees leftTrees rightTrees]
              change (leftTree.elements + rightTree.elements) +
                  (elements leftTrees + elements rightTrees) =
                (leftTree.elements + elements leftTrees) +
                  (rightTree.elements + elements rightTrees)
              exact calc
                (leftTree.elements + rightTree.elements) +
                    (elements leftTrees + elements rightTrees) =
                    leftTree.elements +
                      (rightTree.elements +
                        (elements leftTrees + elements rightTrees)) :=
                          Multiset.add_assoc _ _ _
                _ = leftTree.elements +
                    ((rightTree.elements + elements leftTrees) +
                      elements rightTrees) := congrArg _
                        (Multiset.add_assoc _ _ _).symm
                _ = leftTree.elements +
                    ((elements leftTrees + rightTree.elements) +
                      elements rightTrees) := congrArg
                        (fun values => leftTree.elements +
                          (values + elements rightTrees))
                        (Multiset.add_comm _ _)
                _ = leftTree.elements +
                    (elements leftTrees +
                      (rightTree.elements + elements rightTrees)) := congrArg _
                        (Multiset.add_assoc _ _ _)
                _ = (leftTree.elements + elements leftTrees) +
                    (rightTree.elements + elements rightTrees) :=
                      (Multiset.add_assoc _ _ _).symm
termination_by left.length + right.length

/-- Melding valid forests preserves validity and their common rank lower bound. -/
public theorem meldTrees_correct [LinearOrder α] {rank : Nat}
    {left right : List (BinomialTree α)} (left_valid : Valid left)
    (right_valid : Valid right) (left_lower : RanksAtLeast rank left)
    (right_lower : RanksAtLeast rank right) :
    Valid (meldTrees left right) ∧ RanksAtLeast rank (meldTrees left right) := by
  cases left with
  | nil => simpa [meldTrees] using And.intro right_valid right_lower
  | cons leftTree leftTrees =>
      cases right with
      | nil => simpa [meldTrees] using And.intro left_valid left_lower
      | cons rightTree rightTrees =>
          rw [meldTrees]
          split
          · rename_i rank_lt
            have recursive := meldTrees_correct (rank := leftTree.rank + 1)
              left_valid.tail right_valid
              (fun current member => left_valid.head_lt member)
              (by
                intro current member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact rank_lt
                · exact rank_lt.trans (right_valid.head_lt member))
            constructor
            · apply valid_cons left_valid.head_valid recursive.1
              intro current member
              exact recursive.2 current member
            · intro current member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact left_lower current (by simp)
              · have lower_head := left_lower leftTree (by simp)
                have lower_current := recursive.2 current member
                omega
          · split
            · rename_i rank_lt
              have recursive := meldTrees_correct (rank := rightTree.rank + 1)
                left_valid right_valid.tail
                (by
                  intro current member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact rank_lt
                  · exact rank_lt.trans (left_valid.head_lt member))
                (fun current member => right_valid.head_lt member)
              constructor
              · apply valid_cons right_valid.head_valid recursive.1
                intro current member
                exact recursive.2 current member
              · intro current member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact right_lower current (by simp)
                · have lower_head := right_lower rightTree (by simp)
                  have lower_current := recursive.2 current member
                  omega
            · rename_i right_not_lt left_not_lt
              have ranks : leftTree.rank = rightTree.rank := by omega
              have recursive := meldTrees_correct (rank := leftTree.rank + 1)
                left_valid.tail right_valid.tail
                (fun current member => left_valid.head_lt member)
                (by
                  intro current member
                  rw [ranks]
                  exact right_valid.head_lt member)
              have linked_valid := left_valid.head_valid.link right_valid.head_valid ranks
              have carried := carry_correct linked_valid recursive.1 (by
                simpa [BinomialTree.rank_link] using recursive.2)
              exact ⟨carried.1, fun current member => by
                have lower_head := left_lower leftTree (by simp)
                have lower_current := carried.2 current member
                rw [BinomialTree.rank_link] at lower_current
                omega⟩
termination_by left.length + right.length

/-- Remove the first tree whose root is minimal, preferring earlier trees on ties. -/
@[expose] public def removeMinTree [LinearOrder α] :
    List (BinomialTree α) → Option (BinomialTree α × List (BinomialTree α))
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
    (trees : List (BinomialTree α)) : removeMinTree trees = none ↔ trees = [] := by
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
    {trees : List (BinomialTree α)} {minimum : BinomialTree α}
    {rest : List (BinomialTree α)} (result : removeMinTree trees = some (minimum, rest)) :
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

theorem removeMinTree_root_le [LinearOrder α] {trees : List (BinomialTree α)}
    {minimum : BinomialTree α} {rest : List (BinomialTree α)}
    (valid : Valid trees) (result : removeMinTree trees = some (minimum, rest))
    {value : α} (member : value ∈ elements trees) : minimum.root ≤ value := by
  have spec := removeMinTree_spec result
  rcases mem_elements_iff.mp member with ⟨tree, tree_mem, value_mem⟩
  exact (spec.2.2.2 tree tree_mem).trans ((valid.1 tree tree_mem).root_le value_mem)

/-- Reversing a valid tree's children produces a valid increasing-rank forest. -/
public theorem valid_reverse_children [LinearOrder α] {tree : BinomialTree α}
    (valid : tree.Valid) : Valid tree.children.reverse := by
  constructor
  · intro child member
    exact valid.child_valid (by simpa using member)
  · rw [List.map_reverse, valid.children_ranks, List.reverse_reverse]
    exact List.pairwise_lt_range

private theorem sum_append (left right : List (Multiset α)) :
    (left ++ right).sum = left.sum + right.sum := by
  induction left with
  | nil => simp
  | cons value values ih =>
      simp only [List.cons_append, List.sum_cons]
      rw [ih, Multiset.add_assoc]

private theorem sum_reverse (values : List (Multiset α)) :
    values.reverse.sum = values.sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [List.reverse_cons, sum_append, ih]
      rw [Multiset.add_comm]
      change (value + 0) + values.sum = value + values.sum
      rw [Multiset.add_zero]

theorem root_cons_elements_reverse_children (tree : BinomialTree α) :
    tree.root ::ₘ elements tree.children.reverse = tree.elements := by
  cases tree
  simp only [BinomialTree.root, BinomialTree.children, BinomialTree.elements, elements,
    List.map_reverse]
  rw [sum_reverse]

end BinomialForest

/-- A binomial min-heap represented by a valid increasing-rank forest. -/
public structure BinomialHeap (α : Type u) [LinearOrder α] where
  /-- The binomial trees, in strictly increasing rank order. -/
  trees : List (BinomialTree α)
  valid : BinomialForest.Valid trees

namespace BinomialHeap

variable {α : Type u}

/-- The multiset represented by a binomial heap. -/
@[expose] public def elements [LinearOrder α] (heap : BinomialHeap α) : Multiset α :=
  BinomialForest.elements heap.trees

/-- The empty binomial heap. -/
@[expose] public def empty [LinearOrder α] : BinomialHeap α :=
  ⟨[], BinomialForest.valid_nil⟩

/-- Meld two binomial heaps. -/
@[expose] public def meld [LinearOrder α] (left right : BinomialHeap α) : BinomialHeap α :=
  ⟨BinomialForest.meldTrees left.trees right.trees,
    (BinomialForest.meldTrees_correct (rank := 0) left.valid right.valid
      (by simp [BinomialForest.RanksAtLeast])
      (by simp [BinomialForest.RanksAtLeast])).1⟩

/-- A one-element binomial heap. -/
@[expose] public def singleton [LinearOrder α] (value : α) : BinomialHeap α :=
  ⟨[BinomialTree.singleton value], by
    apply BinomialForest.valid_cons (BinomialTree.valid_singleton value)
      BinomialForest.valid_nil
    simp⟩

/-- Insert one value into a binomial heap. -/
@[expose] public def insert [LinearOrder α] (heap : BinomialHeap α) (value : α) : BinomialHeap α :=
  (singleton value).meld heap

/-- Inspect the minimum value without removing it. -/
@[expose] public def findMin [LinearOrder α] (heap : BinomialHeap α) : Option α :=
  (BinomialForest.removeMinTree heap.trees).map fun result => result.1.root

/-- The computational forest projection of minimum deletion. -/
@[expose] public def deleteMinTrees [LinearOrder α]
    (trees : List (BinomialTree α)) : Option (α × List (BinomialTree α)) :=
  match BinomialForest.removeMinTree trees with
  | none => none
  | some (minimum, rest) =>
      some (minimum.root,
        BinomialForest.meldTrees minimum.children.reverse rest)

/-- Remove and return the minimum value. -/
public def deleteMin [LinearOrder α]
    (heap : BinomialHeap α) : Option (α × BinomialHeap α) :=
  match found : BinomialForest.removeMinTree heap.trees with
  | none => none
  | some (minimum, rest) =>
      have spec := BinomialForest.removeMinTree_spec found
      have minimum_valid : minimum.Valid := heap.valid.1 minimum spec.2.1
      have rest_valid : BinomialForest.Valid rest := heap.valid.sublist spec.2.2.1
      have children_valid := BinomialForest.valid_reverse_children minimum_valid
      let trees := BinomialForest.meldTrees minimum.children.reverse rest
      have trees_valid : BinomialForest.Valid trees :=
        (BinomialForest.meldTrees_correct (rank := 0) children_valid rest_valid
          (by simp [BinomialForest.RanksAtLeast])
          (by simp [BinomialForest.RanksAtLeast])).1
      some (minimum.root, ⟨trees, trees_valid⟩)

/-- Projecting away the validity proof from deletion gives `deleteMinTrees`. -/
public theorem deleteMin_trees [LinearOrder α] (heap : BinomialHeap α) :
    heap.deleteMin.map (fun result => (result.1, result.2.trees)) =
      deleteMinTrees heap.trees := by
  unfold deleteMin deleteMinTrees
  split <;> rename_i found <;> simp only [found] <;> rfl

/-- Meld preserves every occurrence from both heaps. -/
public theorem elements_meld [LinearOrder α] (left right : BinomialHeap α) :
    (left.meld right).elements = left.elements + right.elements := by
  simpa [meld, elements] using
    (BinomialForest.elements_meldTrees left.trees right.trees)

/-- Insertion adds exactly one occurrence. -/
public theorem elements_insert [LinearOrder α] (heap : BinomialHeap α) (value : α) :
    (heap.insert value).elements = value ::ₘ heap.elements := by
  rw [insert, elements_meld]
  simp [singleton, elements, BinomialForest.elements]

/-- Minimum inspection fails exactly for the empty heap. -/
public theorem findMin_eq_none_iff [LinearOrder α] (heap : BinomialHeap α) :
    heap.findMin = none ↔ heap.trees = [] := by
  simp [findMin, BinomialForest.removeMinTree_eq_none_iff]

/-- Minimum inspection returns a represented element. -/
public theorem findMin_mem [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    (result : heap.findMin = some minimum) : minimum ∈ heap.elements := by
  unfold findMin at result
  cases found : BinomialForest.removeMinTree heap.trees with
  | none => simp [found] at result
  | some selected =>
      rcases selected with ⟨tree, rest⟩
      simp only [found, Option.map_some, Option.some.injEq] at result
      subst minimum
      have spec := BinomialForest.removeMinTree_spec found
      change tree.root ∈ BinomialForest.elements heap.trees
      rw [← spec.1]
      exact Multiset.mem_add.mpr (Or.inl (BinomialTree.root_mem_elements tree))

/-- Minimum inspection returns a value no greater than every represented value. -/
public theorem findMin_le [LinearOrder α] {heap : BinomialHeap α} {minimum value : α}
    (result : heap.findMin = some minimum) (member : value ∈ heap.elements) :
    minimum ≤ value := by
  unfold findMin at result
  cases found : BinomialForest.removeMinTree heap.trees with
  | none => simp [found] at result
  | some selected =>
      rcases selected with ⟨tree, rest⟩
      simp only [found, Option.map_some, Option.some.injEq] at result
      subst minimum
      exact BinomialForest.removeMinTree_root_le heap.valid found member

theorem deleteMin_partition [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    have spec := BinomialForest.removeMinTree_spec found
    change tree.root ::ₘ
        BinomialForest.elements
          (BinomialForest.meldTrees tree.children.reverse remaining) =
      BinomialForest.elements heap.trees
    rw [BinomialForest.elements_meldTrees, ← Multiset.cons_add,
      BinomialForest.root_cons_elements_reverse_children, spec.1]

/-- Deletion fails exactly for the empty heap. -/
public theorem deleteMin_eq_none_iff [LinearOrder α] (heap : BinomialHeap α) :
    heap.deleteMin = none ↔ heap.trees = [] := by
  unfold deleteMin
  split
  · rename_i found
    exact ⟨fun _ => (BinomialForest.removeMinTree_eq_none_iff heap.trees).mp found,
      fun _ => rfl⟩
  · rename_i tree remaining found
    constructor
    · intro impossible
      contradiction
    · intro empty
      have none : BinomialForest.removeMinTree heap.trees = none :=
        (BinomialForest.removeMinTree_eq_none_iff heap.trees).mpr empty
      rw [none] at found
      contradiction

/-- Successful deletion erases exactly one occurrence of the returned minimum. -/
public theorem deleteMin_elements [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    rest.elements = heap.elements.erase minimum := by
  rw [← deleteMin_partition result, Multiset.erase_cons_head]

/-- Successful deletion partitions the original multiset into its minimum and remainder. -/
public theorem deleteMin_cons_elements [LinearOrder α] {heap : BinomialHeap α} {minimum : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest)) :
    minimum ::ₘ rest.elements = heap.elements := by
  exact deleteMin_partition result

/-- Successful deletion returns a represented globally minimal value. -/
public theorem deleteMin_le [LinearOrder α] {heap : BinomialHeap α} {minimum value : α}
    {rest : BinomialHeap α} (result : heap.deleteMin = some (minimum, rest))
    (member : value ∈ heap.elements) : minimum ≤ value := by
  unfold deleteMin at result
  split at result
  · contradiction
  · rename_i tree remaining found
    simp only [Option.some.injEq, Prod.mk.injEq] at result
    rcases result with ⟨rfl, rfl⟩
    exact BinomialForest.removeMinTree_root_le heap.valid found member

end BinomialHeap

end Cslib.Algorithms.Lean
