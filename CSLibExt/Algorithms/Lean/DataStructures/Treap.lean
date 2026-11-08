/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

set_option autoImplicit false

universe u v

@[expose] public section

/-!
# Treaps

This module defines deterministic treap operations. Each node stores an explicit
priority; no correctness theorem depends on a random source. Insertion and
deletion are implemented from key splitting and priority-guided merging.

The implementation and proofs were authored for this module. The representation
style follows `BinarySearchTree` from D123980084; no public treap implementation
was copied.
-/

namespace Cslib.Algorithms.Lean
namespace Treap

/-- A finite binary tree whose nodes carry keys, values, and explicit priorities. -/
public inductive Tree (κ : Type u) (ν : Type v) where
  | empty
  | node (left : Tree κ ν) (key : κ) (value : ν) (priority : Nat)
      (right : Tree κ ν)
  deriving DecidableEq, Repr

namespace Tree

/-- `AllNodes p tree` states that every node in `tree` satisfies `p`. -/
public def AllNodes {κ : Type u} {ν : Type v} (p : κ → ν → Nat → Prop) :
    Tree κ ν → Prop
  | .empty => True
  | .node left key value priority right =>
      AllNodes p left ∧ p key value priority ∧ AllNodes p right

/-- Structural membership of a complete key-value-priority entry. -/
public def MemNode {κ : Type u} {ν : Type v} (key : κ) (value : ν)
    (priority : Nat) : Tree κ ν → Prop
  | .empty => False
  | .node left rootKey rootValue rootPriority right =>
      MemNode key value priority left ∨
        (key = rootKey ∧ value = rootValue ∧ priority = rootPriority) ∨
        MemNode key value priority right

/-- Structural membership of a key, independent of representation invariants. -/
public def MemKey {κ : Type u} {ν : Type v} (key : κ) : Tree κ ν → Prop
  | .empty => False
  | .node left rootKey _ _ right =>
      MemKey key left ∨ key = rootKey ∨ MemKey key right

/-- Key membership notation for trees. -/
public instance {κ : Type u} {ν : Type v} : Membership κ (Tree κ ν) :=
  ⟨fun tree key => MemKey key tree⟩

/-- Append the inorder key-value traversal of a tree to a suffix in linear
time: the left traversal is accumulated onto the node entry and the already
traversed right suffix, so no ancestor recopies a completed traversal. -/
public def contentsAux {κ : Type u} {ν : Type v} :
    Tree κ ν → List (κ × ν) → List (κ × ν)
  | .empty, suffix => suffix
  | .node left key value _ right, suffix =>
      contentsAux left ((key, value) :: contentsAux right suffix)

private theorem contentsAux_append {κ : Type u} {ν : Type v} (tree : Tree κ ν)
    (xs ys : List (κ × ν)) :
    contentsAux tree (xs ++ ys) = contentsAux tree xs ++ ys := by
  induction tree generalizing xs with
  | empty => rfl
  | node left key value priority right ihLeft ihRight =>
      simp only [contentsAux]
      rw [ihRight]
      change contentsAux left (((key, value) :: contentsAux right xs) ++ ys) =
        contentsAux left ((key, value) :: contentsAux right xs) ++ ys
      exact ihLeft _

/-- The inorder key-value refinement of a tree, computed by the linear
accumulating traversal `contentsAux`. -/
public def contents {κ : Type u} {ν : Type v} (tree : Tree κ ν) : List (κ × ν) :=
  contentsAux tree []

/-- Characteristic node equation for the linear inorder traversal. -/
public theorem contents_node {κ : Type u} {ν : Type v}
    (left : Tree κ ν) (key : κ) (value : ν) (priority : Nat) (right : Tree κ ν) :
    contents (.node left key value priority right) =
      contents left ++ (key, value) :: contents right := by
  show contentsAux left ((key, value) :: contentsAux right []) =
    contentsAux left [] ++ (key, value) :: contentsAux right []
  rw [← List.singleton_append, contentsAux_append]
  conv_lhs => rw [← List.nil_append [(key, value)], contentsAux_append]
  rw [List.append_assoc]

/-- The recursively computed number of nodes. -/
public def size {κ : Type u} {ν : Type v} : Tree κ ν → Nat
  | .empty => 0
  | .node left _ _ _ right => size left + 1 + size right

/-- Every left key is smaller and every right key is larger, recursively. -/
public def Ordered {κ : Type u} {ν : Type v} [LT κ] : Tree κ ν → Prop
  | .empty => True
  | .node left key _ _ right =>
      Ordered left ∧ Ordered right ∧
        AllNodes (fun childKey _ _ => childKey < key) left ∧
        AllNodes (fun childKey _ _ => key < childKey) right

/-- Every node priority is no greater than every descendant priority. -/
public def HeapOrdered {κ : Type u} {ν : Type v} : Tree κ ν → Prop
  | .empty => True
  | .node left _ _ priority right =>
      HeapOrdered left ∧ HeapOrdered right ∧
        AllNodes (fun _ _ childPriority => priority ≤ childPriority) left ∧
        AllNodes (fun _ _ childPriority => priority ≤ childPriority) right

/-- The representation invariant: strict BST order and min-heap priority order. -/
public def Valid {κ : Type u} {ν : Type v} [LT κ] (tree : Tree κ ν) : Prop :=
  Ordered tree ∧ HeapOrdered tree

/-- Search for a key by following the BST comparisons. -/
public def lookup {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ) :
    Tree κ ν → Option ν
  | .empty => none
  | .node left rootKey value _ right =>
      if key < rootKey then lookup key left
      else if rootKey < key then lookup key right
      else some value

/-- Search result paired with the number of visited nodes. -/
public def lookupWithCost {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ) :
    Tree κ ν → Option ν × Nat
  | .empty => (none, 0)
  | .node left rootKey value _ right =>
      if key < rootKey then
        let result := lookupWithCost key left
        (result.1, result.2 + 1)
      else if rootKey < key then
        let result := lookupWithCost key right
        (result.1, result.2 + 1)
      else (some value, 1)

/-- The optional priority at a root. -/
public def rootPriority {κ : Type u} {ν : Type v} : Tree κ ν → Option Nat
  | .empty => none
  | .node _ _ _ priority _ => some priority

/-- Merge two trees, choosing the smaller root priority at every step. -/
public def merge {κ : Type u} {ν : Type v} : Tree κ ν → Tree κ ν → Tree κ ν
  | .empty, right => right
  | left, .empty => left
  | .node leftLeft leftKey leftValue leftPriority leftRight,
      .node rightLeft rightKey rightValue rightPriority rightRight =>
    if leftPriority ≤ rightPriority then
      .node leftLeft leftKey leftValue leftPriority
        (merge leftRight (.node rightLeft rightKey rightValue rightPriority rightRight))
    else
      .node
        (merge (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft)
        rightKey rightValue rightPriority rightRight
termination_by left right => size left + size right
decreasing_by all_goals (simp_wf; simp [size] <;> omega)

/-- The result of splitting a tree around a key. -/
public structure SplitResult (κ : Type u) (ν : Type v) where
  /-- The subtree containing keys below the pivot. -/
  less : Tree κ ν
  /-- The pivot's value and priority when it was present. -/
  found : Option (ν × Nat)
  /-- The subtree containing keys above the pivot. -/
  greater : Tree κ ν
  deriving DecidableEq, Repr

/-- Split into keys below a pivot, its optional value/priority, and keys above it. -/
public def split {κ : Type u} {ν : Type v} [LinearOrder κ] (pivot : κ) :
    Tree κ ν → SplitResult κ ν
  | .empty => ⟨.empty, none, .empty⟩
  | .node left key value priority right =>
      if key < pivot then
        let result := split pivot right
        ⟨.node left key value priority result.less, result.found, result.greater⟩
      else if pivot < key then
        let result := split pivot left
        ⟨result.less, result.found,
          .node result.greater key value priority right⟩
      else ⟨left, some (value, priority), right⟩

/-- Insert or replace a key with an explicit priority using split and merge. -/
public def insert {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ)
    (value : ν) (priority : Nat) (tree : Tree κ ν) : Tree κ ν :=
  let result := split key tree
  merge (merge result.less (.node .empty key value priority .empty)) result.greater

/-- Delete a key by splitting around it and merging the two remaining trees. -/
public def erase {κ : Type u} {ν : Type v} [LinearOrder κ] (key : κ)
    (tree : Tree κ ν) : Tree κ ν :=
  let result := split key tree
  merge result.less result.greater

@[simp] private theorem allNodes_empty {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} : AllNodes p (.empty : Tree κ ν) :=
  trivial

@[simp] private theorem allNodes_node {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} {left right : Tree κ ν} {key : κ} {value : ν}
    {priority : Nat} :
    AllNodes p (.node left key value priority right) ↔
      AllNodes p left ∧ p key value priority ∧ AllNodes p right :=
  Iff.rfl

@[simp] private theorem memKey_empty {κ : Type u} {ν : Type v} {key : κ} :
    key ∈ (.empty : Tree κ ν) ↔ False :=
  Iff.rfl

@[simp] private theorem memKey_node {κ : Type u} {ν : Type v} {key rootKey : κ}
    {left right : Tree κ ν} {value : ν} {priority : Nat} :
    key ∈ (Tree.node left rootKey value priority right) ↔
      key ∈ left ∨ key = rootKey ∨ key ∈ right :=
  Iff.rfl

/-- `AllNodes` is universal quantification over complete structural membership. -/
public theorem allNodes_iff_forall_mem {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} {tree : Tree κ ν} :
    AllNodes p tree ↔ ∀ key value priority, MemNode key value priority tree →
      p key value priority := by
  induction tree with
  | empty => simp [AllNodes, MemNode]
  | node left key value priority right ihLeft ihRight =>
    simp only [AllNodes, MemNode, ihLeft, ihRight]
    constructor
    · rintro ⟨hLeft, hRoot, hRight⟩ childKey childValue childPriority
        (h | h | h)
      · exact hLeft _ _ _ h
      · rcases h with ⟨rfl, rfl, rfl⟩
        exact hRoot
      · exact hRight _ _ _ h
    · intro h
      exact ⟨
        fun childKey childValue childPriority hMem => h _ _ _ (Or.inl hMem),
        h key value priority (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
        fun childKey childValue childPriority hMem => h _ _ _ (Or.inr (Or.inr hMem))⟩

/-- Complete node membership implies key membership. -/
public theorem memKey_of_memNode {κ : Type u} {ν : Type v} {key : κ} {value : ν}
    {priority : Nat} {tree : Tree κ ν} (h : MemNode key value priority tree) :
    key ∈ tree := by
  induction tree with
  | empty => exact h.elim
  | node left rootKey rootValue rootPriority right ihLeft ihRight =>
    rcases h with h | ⟨hKey, _, _⟩ | h
    · exact Or.inl (ihLeft h)
    · exact Or.inr (Or.inl hKey)
    · exact Or.inr (Or.inr (ihRight h))

/-- Inorder contents contain exactly the tree's key-value pairs. -/
public theorem mem_contents {κ : Type u} {ν : Type v} {key : κ} {value : ν}
    {tree : Tree κ ν} :
    (key, value) ∈ contents tree ↔ ∃ priority, MemNode key value priority tree := by
  induction tree with
  | empty => simp [contents, contentsAux, contents_node, contentsAux, MemNode]
  | node left rootKey rootValue rootPriority right ihLeft ihRight =>
    simp only [contents_node, List.mem_append, List.mem_cons, ihLeft, ihRight]
    constructor
    · rintro (⟨priority, h⟩ | h | ⟨priority, h⟩)
      · exact ⟨priority, Or.inl h⟩
      · simp only [Prod.mk.injEq] at h
        exact ⟨rootPriority, Or.inr (Or.inl ⟨h.1, h.2, rfl⟩)⟩
      · exact ⟨priority, Or.inr (Or.inr h)⟩
    · rintro ⟨priority, h | ⟨hKey, hValue, _⟩ | h⟩
      · exact Or.inl ⟨priority, h⟩
      · exact Or.inr (Or.inl (by simp [hKey, hValue]))
      · exact Or.inr (Or.inr ⟨priority, h⟩)

/-- Inorder contents contain exactly the structurally present keys. -/
public theorem key_mem_contents {κ : Type u} {ν : Type v} {key : κ}
    {tree : Tree κ ν} :
    (∃ value, (key, value) ∈ contents tree) ↔ key ∈ tree := by
  induction tree with
  | empty => simp [contents, contentsAux, contents_node, contentsAux]
  | node left rootKey rootValue rootPriority right ihLeft ihRight =>
    simp only [contents_node, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨value, h | h | h⟩
      · exact Or.inl (ihLeft.mp ⟨value, h⟩)
      · exact Or.inr (Or.inl (Prod.mk.inj h).1)
      · exact Or.inr (Or.inr (ihRight.mp ⟨value, h⟩))
    · rintro (h | rfl | h)
      · rcases ihLeft.mpr h with ⟨value, hValue⟩
        exact ⟨value, Or.inl hValue⟩
      · exact ⟨rootValue, Or.inr (Or.inl rfl)⟩
      · rcases ihRight.mpr h with ⟨value, hValue⟩
        exact ⟨value, Or.inr (Or.inr hValue)⟩

/-- For predicates depending only on keys, `AllNodes` is key-membership quantification. -/
public theorem allNodes_key_iff {κ : Type u} {ν : Type v} {p : κ → Prop}
    {tree : Tree κ ν} :
    AllNodes (fun key _ _ => p key) tree ↔ ∀ key, key ∈ tree → p key := by
  induction tree with
  | empty => simp [AllNodes]
  | node left key value priority right ihLeft ihRight =>
    simp only [AllNodes, memKey_node, ihLeft, ihRight]
    constructor
    · rintro ⟨hLeft, hKey, hRight⟩ childKey (h | h | h)
      · exact hLeft childKey h
      · simpa [h] using hKey
      · exact hRight childKey h
    · intro h
      exact ⟨fun childKey hMem => h childKey (Or.inl hMem),
        h key (Or.inr (Or.inl rfl)),
        fun childKey hMem => h childKey (Or.inr (Or.inr hMem))⟩

/-- The inorder list of keys, used to state uniqueness independently of
values. Derived from the linear `contents` traversal. -/
public def keys {κ : Type u} {ν : Type v} (tree : Tree κ ν) : List κ :=
  (contents tree).map Prod.fst

/-- Characteristic node equation for the inorder key list. -/
public theorem keys_node {κ : Type u} {ν : Type v}
    (left : Tree κ ν) (key : κ) (value : ν) (priority : Nat) (right : Tree κ ν) :
    keys (.node left key value priority right) =
      keys left ++ key :: keys right := by
  simp [keys, contents_node]

/-- The key list contains exactly the structurally present keys. -/
public theorem mem_keys {κ : Type u} {ν : Type v} {key : κ} {tree : Tree κ ν} :
    key ∈ keys tree ↔ key ∈ tree := by
  induction tree with
  | empty => simp [keys, contents, contentsAux, contents_node, contentsAux]
  | node left rootKey value priority right ihLeft ihRight =>
    simp [keys_node, ihLeft, ihRight, or_left_comm]

/-- The inorder keys of an ordered tree are strictly increasing. -/
public theorem ordered_keys {κ : Type u} {ν : Type v} [LinearOrder κ]
    {tree : Tree κ ν} (hOrdered : Ordered tree) :
    List.Pairwise (· < ·) (keys tree) := by
  induction tree with
  | empty => simp [keys, contents, contentsAux, contents_node, contentsAux]
  | node left key value priority right ihLeft ihRight =>
    rcases hOrdered with ⟨hLeft, hRight, hKeysLeft, hKeysRight⟩
    rw [keys_node, List.pairwise_append]
    refine ⟨ihLeft hLeft, ?_, ?_⟩
    · rw [List.pairwise_cons]
      exact ⟨fun childKey hMem =>
        (allNodes_key_iff.mp hKeysRight) childKey (mem_keys.mp hMem), ihRight hRight⟩
    · intro leftKey hLeftMem rightKey hRightMem
      rw [List.mem_cons] at hRightMem
      rcases hRightMem with rfl | hRightMem
      · exact (allNodes_key_iff.mp hKeysLeft) leftKey (mem_keys.mp hLeftMem)
      · exact lt_trans
          ((allNodes_key_iff.mp hKeysLeft) leftKey (mem_keys.mp hLeftMem))
          ((allNodes_key_iff.mp hKeysRight) rightKey (mem_keys.mp hRightMem))

/-- Strict BST ordering implies that all stored keys are distinct. -/
public theorem keys_nodup {κ : Type u} {ν : Type v} [LinearOrder κ]
    {tree : Tree κ ν} (hOrdered : Ordered tree) : (keys tree).Nodup :=
  (ordered_keys hOrdered).nodup

/-- BST lookup returns a value exactly when the matching key-value node exists. -/
public theorem lookup_eq_some_iff {κ : Type u} {ν : Type v} [LinearOrder κ]
    {query : κ} {value : ν} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    lookup query tree = some value ↔ ∃ priority, MemNode query value priority tree := by
  induction tree with
  | empty => simp [lookup, MemNode]
  | node left key rootValue rootPriority right ihLeft ihRight =>
    rcases hOrdered with ⟨hLeft, hRight, hKeysLeft, hKeysRight⟩
    by_cases hQuery : query < key
    · have hNotRight : ¬query ∈ right := by
        intro hMem
        exact (lt_asymm hQuery ((allNodes_key_iff.mp hKeysRight) query hMem)).elim
      have hNotEq : query ≠ key := ne_of_lt hQuery
      have hNoRight : ∀ priority, ¬MemNode query value priority right :=
        fun _ hMem => hNotRight (memKey_of_memNode hMem)
      simp [lookup, hQuery, ihLeft hLeft, MemNode, hNoRight, hNotEq]
    · by_cases hKey : key < query
      · have hNotLeft : ¬query ∈ left := by
          intro hMem
          exact (lt_asymm hKey ((allNodes_key_iff.mp hKeysLeft) query hMem)).elim
        have hNotEq : query ≠ key := ne_of_gt hKey
        have hNoLeft : ∀ priority, ¬MemNode query value priority left :=
          fun _ hMem => hNotLeft (memKey_of_memNode hMem)
        simp [lookup, hQuery, hKey, ihRight hRight, MemNode, hNoLeft, hNotEq]
      · have hEq : query = key := le_antisymm (le_of_not_gt hKey) (le_of_not_gt hQuery)
        subst query
        have hRootNotLeft : ¬key ∈ left := by
          intro hMem
          exact (lt_irrefl key ((allNodes_key_iff.mp hKeysLeft) key hMem)).elim
        have hRootNotRight : ¬key ∈ right := by
          intro hMem
          exact (lt_irrefl key ((allNodes_key_iff.mp hKeysRight) key hMem)).elim
        have hNoLeft : ∀ priority, ¬MemNode key value priority left :=
          fun _ hMem => hRootNotLeft (memKey_of_memNode hMem)
        have hNoRight : ∀ priority, ¬MemNode key value priority right :=
          fun _ hMem => hRootNotRight (memKey_of_memNode hMem)
        simp [lookup, MemNode, hNoLeft, hNoRight, eq_comm]

/-- On an ordered tree, lookup agrees with membership in the key-value contents list. -/
public theorem lookup_contents {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {value : ν} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    lookup key tree = some value ↔ (key, value) ∈ contents tree := by
  rw [lookup_eq_some_iff hOrdered, mem_contents]

/-- The value component of costed lookup is ordinary lookup. -/
public theorem lookupWithCost_result {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} : (lookupWithCost key tree).1 = lookup key tree := by
  induction tree with
  | empty => rfl
  | node left rootKey value priority right ihLeft ihRight =>
    simp only [lookupWithCost, lookup]
    split_ifs <;> simp_all

/-- Costed lookup visits no more nodes than the tree contains. -/
public theorem lookupWithCost_le_size {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} : (lookupWithCost key tree).2 ≤ size tree := by
  induction tree with
  | empty => simp [lookupWithCost, size]
  | node left rootKey value priority right ihLeft ihRight =>
    simp only [lookupWithCost]
    split_ifs <;> simp_all [size] <;> omega

/-- Every node in a heap-ordered nonempty tree has priority at least its root. -/
public theorem heap_root_min {κ : Type u} {ν : Type v} {left right : Tree κ ν}
    {key : κ} {value : ν} {priority : Nat}
    (hHeap : HeapOrdered (.node left key value priority right)) :
    AllNodes (fun _ _ childPriority => priority ≤ childPriority)
      (.node left key value priority right) := by
  rcases hHeap with ⟨_, _, hLeft, hRight⟩
  exact ⟨hLeft, le_rfl, hRight⟩

private theorem allNodes_merge {κ : Type u} {ν : Type v}
    {p : κ → ν → Nat → Prop} (left right : Tree κ ν) :
    AllNodes p (merge left right) ↔ AllNodes p left ∧ AllNodes p right := by
  induction left, right using merge.induct with
  | case1 right => simp [merge, AllNodes]
  | case2 left hLeft => cases left <;> simp_all [merge, AllNodes]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, AllNodes, ih, and_assoc, and_left_comm]
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, AllNodes, ih, and_assoc, and_left_comm]

/-- Merging preserves exactly the union of structural key membership. -/
public theorem memKey_merge {κ : Type u} {ν : Type v} {key : κ}
    (left right : Tree κ ν) :
    key ∈ merge left right ↔ key ∈ left ∨ key ∈ right := by
  induction left, right using merge.induct with
  | case1 right => simp [merge]
  | case2 left hLeft => cases left <;> simp_all [merge]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, ih, or_assoc, or_left_comm]
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, ih, or_assoc, or_left_comm]

/-- Merging concatenates the two inorder key-value refinements. -/
public theorem contents_merge {κ : Type u} {ν : Type v} (left right : Tree κ ν) :
    contents (merge left right) = contents left ++ contents right := by
  induction left, right using merge.induct with
  | case1 right => simp [merge, contents, contentsAux, contents_node]
  | case2 left hLeft => cases left <;> simp_all [merge, contents, contentsAux, contents_node]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, contents_node, ih, List.append_assoc]
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    simp [merge, hPriority, contents_node, ih, List.append_assoc]

/-- `Separated left right` states that every left key is below every right key. -/
public def Separated {κ : Type u} {ν : Type v} [LT κ]
    (left right : Tree κ ν) : Prop :=
  ∀ leftKey, leftKey ∈ left → ∀ rightKey, rightKey ∈ right → leftKey < rightKey

/-- Priority-guided merge preserves strict BST ordering for separated inputs. -/
public theorem ordered_merge {κ : Type u} {ν : Type v} [LinearOrder κ]
    (left right : Tree κ ν) (hLeft : Ordered left) (hRight : Ordered right)
    (hSeparated : Separated left right) : Ordered (merge left right) := by
  induction left, right using merge.induct with
  | case1 right => simpa [merge] using hRight
  | case2 left hNotEmpty => cases left <;> simp_all [merge]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hLeft with ⟨hLeftLeft, hLeftRight, hKeysLeft, hKeysRight⟩
    have hSeparatedRight :
        Separated leftRight (.node rightLeft rightKey rightValue rightPriority rightRight) :=
      fun key hKey => hSeparated key (Or.inr (Or.inr hKey))
    have hRootBelowRight :
        AllNodes (fun key _ _ => leftKey < key)
          (.node rightLeft rightKey rightValue rightPriority rightRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        hSeparated leftKey (Or.inr (Or.inl rfl)) key (memKey_of_memNode hMem))
    simp only [merge, hPriority]
    exact ⟨hLeftLeft, ih hLeftRight hRight hSeparatedRight, hKeysLeft,
      (allNodes_merge leftRight
        (.node rightLeft rightKey rightValue rightPriority rightRight)).mpr
          ⟨hKeysRight, hRootBelowRight⟩⟩
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hRight with ⟨hRightLeft, hRightRight, hKeysLeft, hKeysRight⟩
    have hSeparatedLeft :
        Separated (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft :=
      fun key hKey rightKey hRightKey => hSeparated key hKey rightKey (Or.inl hRightKey)
    have hLeftBelowRoot :
        AllNodes (fun key _ _ => key < rightKey)
          (.node leftLeft leftKey leftValue leftPriority leftRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        hSeparated key (memKey_of_memNode hMem) rightKey (Or.inr (Or.inl rfl)))
    simp only [merge, hPriority]
    exact ⟨ih hLeft hRightLeft hSeparatedLeft, hRightRight,
      (allNodes_merge
        (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft).mpr
          ⟨hLeftBelowRoot, hKeysLeft⟩, hKeysRight⟩

/-- Priority-guided merge preserves the min-heap invariant. -/
public theorem heapOrdered_merge {κ : Type u} {ν : Type v}
    (left right : Tree κ ν) (hLeft : HeapOrdered left)
    (hRight : HeapOrdered right) : HeapOrdered (merge left right) := by
  induction left, right using merge.induct with
  | case1 right => simpa [merge] using hRight
  | case2 left hNotEmpty => cases left <;> simp_all [merge]
  | case3 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hLeft with ⟨hLeftLeft, hLeftRight, hPriorityLeft, hPriorityRight⟩
    have hRootRight := heap_root_min hRight
    have hPriorityAllRight :
        AllNodes (fun _ _ priority => leftPriority ≤ priority)
          (.node rightLeft rightKey rightValue rightPriority rightRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        le_trans hPriority
          (allNodes_iff_forall_mem.mp hRootRight key value priority hMem))
    simp only [merge, hPriority]
    exact ⟨hLeftLeft, ih hLeftRight hRight, hPriorityLeft,
      (allNodes_merge leftRight
        (.node rightLeft rightKey rightValue rightPriority rightRight)).mpr
          ⟨hPriorityRight, hPriorityAllRight⟩⟩
  | case4 leftLeft leftKey leftValue leftPriority leftRight rightLeft rightKey
      rightValue rightPriority rightRight hPriority ih =>
    rcases hRight with ⟨hRightLeft, hRightRight, hPriorityLeft, hPriorityRight⟩
    have hRightLeLeft : rightPriority ≤ leftPriority := Nat.le_of_lt (Nat.lt_of_not_ge hPriority)
    have hRootLeft := heap_root_min hLeft
    have hPriorityAllLeft :
        AllNodes (fun _ _ priority => rightPriority ≤ priority)
          (.node leftLeft leftKey leftValue leftPriority leftRight) :=
      allNodes_iff_forall_mem.mpr (fun key value priority hMem =>
        le_trans hRightLeLeft
          (allNodes_iff_forall_mem.mp hRootLeft key value priority hMem))
    simp only [merge, hPriority]
    exact ⟨ih hLeft hRightLeft, hRightRight,
      (allNodes_merge
        (.node leftLeft leftKey leftValue leftPriority leftRight) rightLeft).mpr
          ⟨hPriorityAllLeft, hPriorityLeft⟩, hPriorityRight⟩

private theorem split_allNodes {κ : Type u} {ν : Type v} [LinearOrder κ]
    {p : κ → ν → Nat → Prop} {pivot : κ} {tree : Tree κ ν}
    (hAll : AllNodes p tree) :
    AllNodes p (split pivot tree).less ∧ AllNodes p (split pivot tree).greater := by
  induction tree with
  | empty => simp [split]
  | node left key value priority right ihLeft ihRight =>
    rcases hAll with ⟨hAllLeft, hRoot, hAllRight⟩
    by_cases hKey : key < pivot
    · have ih := ihRight hAllRight
      simp [split, hKey, hAllLeft, hRoot, ih]
    · by_cases hPivot : pivot < key
      · have ih := ihLeft hAllLeft
        simp [split, hKey, hPivot, hAllRight, hRoot, ih]
      · simp [split, hKey, hPivot, hAllLeft, hAllRight]

/-- Splitting preserves strict BST ordering in both output trees. -/
public theorem ordered_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    Ordered (split pivot tree).less ∧ Ordered (split pivot tree).greater := by
  induction tree with
  | empty => simp [split, Ordered]
  | node left key value priority right ihLeft ihRight =>
    rcases hOrdered with ⟨hOrderedLeft, hOrderedRight, hKeysLeft, hKeysRight⟩
    by_cases hKey : key < pivot
    · rcases ihRight hOrderedRight with ⟨hLess, hGreater⟩
      have hInherited := split_allNodes (pivot := pivot) hKeysRight
      simp [split, hKey, Ordered, hOrderedLeft, hLess, hGreater, hKeysLeft,
        hInherited.1]
    · by_cases hPivot : pivot < key
      · rcases ihLeft hOrderedLeft with ⟨hLess, hGreater⟩
        have hInherited := split_allNodes (pivot := pivot) hKeysLeft
        simp [split, hKey, hPivot, Ordered, hOrderedRight, hLess, hGreater,
          hKeysRight, hInherited.2]
      · simp [split, hKey, hPivot, hOrderedLeft, hOrderedRight]

/-- Splitting preserves min-heap priority order in both output trees. -/
public theorem heapOrdered_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hHeap : HeapOrdered tree) :
    HeapOrdered (split pivot tree).less ∧ HeapOrdered (split pivot tree).greater := by
  induction tree with
  | empty => simp [split, HeapOrdered]
  | node left key value priority right ihLeft ihRight =>
    rcases hHeap with ⟨hHeapLeft, hHeapRight, hPriorityLeft, hPriorityRight⟩
    by_cases hKey : key < pivot
    · rcases ihRight hHeapRight with ⟨hLess, hGreater⟩
      have hInherited := split_allNodes (pivot := pivot) hPriorityRight
      simp [split, hKey, HeapOrdered, hHeapLeft, hLess, hGreater, hPriorityLeft,
        hInherited.1]
    · by_cases hPivot : pivot < key
      · rcases ihLeft hHeapLeft with ⟨hLess, hGreater⟩
        have hInherited := split_allNodes (pivot := pivot) hPriorityLeft
        simp [split, hKey, hPivot, HeapOrdered, hHeapRight, hLess, hGreater,
          hPriorityRight, hInherited.2]
      · simp [split, hKey, hPivot, hHeapLeft, hHeapRight]

/-- Split outputs contain only keys respectively below and above the pivot. -/
public theorem split_bounds {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hOrdered : Ordered tree) :
    AllNodes (fun key _ _ => key < pivot) (split pivot tree).less ∧
      AllNodes (fun key _ _ => pivot < key) (split pivot tree).greater := by
  induction tree with
  | empty => simp [split]
  | node left key value priority right ihLeft ihRight =>
    rcases hOrdered with ⟨hOrderedLeft, hOrderedRight, hKeysLeft, hKeysRight⟩
    by_cases hKey : key < pivot
    · rcases ihRight hOrderedRight with ⟨hLess, hGreater⟩
      have hLeftBelow : AllNodes (fun childKey _ _ => childKey < pivot) left :=
        allNodes_iff_forall_mem.mpr (fun childKey childValue childPriority hMem =>
          lt_trans (allNodes_iff_forall_mem.mp hKeysLeft _ _ _ hMem) hKey)
      simp [split, hKey, hLeftBelow, hLess, hGreater]
    · by_cases hPivot : pivot < key
      · rcases ihLeft hOrderedLeft with ⟨hLess, hGreater⟩
        have hRightAbove : AllNodes (fun childKey _ _ => pivot < childKey) right :=
          allNodes_iff_forall_mem.mpr (fun childKey childValue childPriority hMem =>
            lt_trans hPivot (allNodes_iff_forall_mem.mp hKeysRight _ _ _ hMem))
        simp [split, hKey, hPivot, hRightAbove, hLess, hGreater]
      · have hEq : key = pivot := le_antisymm (le_of_not_gt hPivot) (le_of_not_gt hKey)
        subst key
        simp [split, hKeysLeft, hKeysRight]

/-- Splitting a valid treap produces two valid treaps. -/
public theorem valid_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    {pivot : κ} {tree : Tree κ ν} (hValid : Valid tree) :
    Valid (split pivot tree).less ∧ Valid (split pivot tree).greater := by
  rcases hValid with ⟨hOrdered, hHeap⟩
  rcases ordered_split hOrdered with ⟨hOrderedLess, hOrderedGreater⟩
  rcases heapOrdered_split hHeap with ⟨hHeapLess, hHeapGreater⟩
  exact ⟨⟨hOrderedLess, hHeapLess⟩, ⟨hOrderedGreater, hHeapGreater⟩⟩

/-- Merging separated valid treaps produces a valid treap. -/
public theorem valid_merge {κ : Type u} {ν : Type v} [LinearOrder κ]
    {left right : Tree κ ν} (hLeft : Valid left) (hRight : Valid right)
    (hSeparated : Separated left right) : Valid (merge left right) :=
  ⟨ordered_merge left right hLeft.1 hRight.1 hSeparated,
    heapOrdered_merge left right hLeft.2 hRight.2⟩

/-- Insertion preserves strict key ordering and min-heap priority ordering. -/
public theorem valid_insert {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {value : ν} {priority : Nat} {tree : Tree κ ν}
    (hValid : Valid tree) : Valid (insert key value priority tree) := by
  let result := split key tree
  have hSplit := valid_split (pivot := key) hValid
  have hBounds := split_bounds (pivot := key) hValid.1
  have hSingleton : Valid (.node .empty key value priority .empty : Tree κ ν) := by
    simp [Valid, Ordered, HeapOrdered, AllNodes]
  have hLessSingleton :
      Separated result.less (.node .empty key value priority .empty) := by
    intro leftKey hLeftKey rightKey hRightKey
    have hRightEq : rightKey = key := by simpa using hRightKey
    subst rightKey
    exact (allNodes_key_iff.mp hBounds.1) leftKey hLeftKey
  have hFirstValid :
      Valid (merge result.less (.node .empty key value priority .empty)) :=
    valid_merge hSplit.1 hSingleton hLessSingleton
  have hFirstGreater :
      Separated (merge result.less (.node .empty key value priority .empty))
        result.greater := by
    intro leftKey hLeftKey rightKey hRightKey
    rcases (memKey_merge result.less
      (.node .empty key value priority .empty)).mp hLeftKey with hLess | hRoot
    · exact lt_trans ((allNodes_key_iff.mp hBounds.1) leftKey hLess)
        ((allNodes_key_iff.mp hBounds.2) rightKey hRightKey)
    · have hLeftEq : leftKey = key := by simpa using hRoot
      subst leftKey
      exact (allNodes_key_iff.mp hBounds.2) rightKey hRightKey
  change Valid (merge (merge result.less (.node .empty key value priority .empty))
    result.greater)
  exact valid_merge hFirstValid hSplit.2 hFirstGreater

/-- Deletion preserves strict key ordering and min-heap priority ordering. -/
public theorem valid_erase {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} (hValid : Valid tree) :
    Valid (erase key tree) := by
  let result := split key tree
  have hSplit := valid_split (pivot := key) hValid
  have hBounds := split_bounds (pivot := key) hValid.1
  have hSeparated : Separated result.less result.greater := by
    intro leftKey hLeftKey rightKey hRightKey
    exact lt_trans ((allNodes_key_iff.mp hBounds.1) leftKey hLeftKey)
      ((allNodes_key_iff.mp hBounds.2) rightKey hRightKey)
  change Valid (merge result.less result.greater)
  exact valid_merge hSplit.1 hSplit.2 hSeparated

/-- Splitting decomposes inorder contents around the optional pivot entry. -/
public theorem contents_split {κ : Type u} {ν : Type v} [LinearOrder κ]
    (pivot : κ) (tree : Tree κ ν) :
    contents tree = contents (split pivot tree).less ++
      ((split pivot tree).found.map fun result => (pivot, result.1)).toList ++
      contents (split pivot tree).greater := by
  induction tree with
  | empty => simp [split, contents, contentsAux, contents_node]
  | node left key value priority right ihLeft ihRight =>
    by_cases hKey : key < pivot
    · simp [split, hKey, contents_node, ihRight, List.append_assoc]
    · by_cases hPivot : pivot < key
      · simp [split, hKey, hPivot, contents_node, ihLeft, List.append_assoc]
      · have hEq : key = pivot := le_antisymm (le_of_not_gt hPivot) (le_of_not_gt hKey)
        subst key
        simp only [split, contents, contentsAux, contents_node]
        rw [← List.singleton_append, contentsAux_append]
        conv_lhs => rw [← List.nil_append [(pivot, value)], contentsAux_append]
        rw [List.append_assoc, List.singleton_append]
        simp

/-- Inserted contents are the split sides with the new key-value pair between them. -/
public theorem contents_insert {κ : Type u} {ν : Type v} [LinearOrder κ]
    (key : κ) (value : ν) (priority : Nat) (tree : Tree κ ν) :
    contents (insert key value priority tree) =
      contents (split key tree).less ++ (key, value) :: contents (split key tree).greater := by
  simp only [insert]
  rw [contents_merge, contents_merge, contents_node]
  simp [contents, contentsAux, List.append_assoc]

/-- Erased contents are exactly the two non-pivot split sides. -/
public theorem contents_erase {κ : Type u} {ν : Type v} [LinearOrder κ]
    (key : κ) (tree : Tree κ ν) :
    contents (erase key tree) =
      contents (split key tree).less ++ contents (split key tree).greater := by
  simp [erase, contents_merge]

/-- Looking up an inserted key returns its replacement value. -/
public theorem lookup_insert_eq {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {value : ν} {priority : Nat} {tree : Tree κ ν}
    (hValid : Valid tree) : lookup key (insert key value priority tree) = some value := by
  apply (lookup_contents (valid_insert hValid).1).mpr
  rw [contents_insert]
  simp

/-- Looking up an erased key returns no value. -/
public theorem lookup_erase_eq_none {κ : Type u} {ν : Type v} [LinearOrder κ]
    {key : κ} {tree : Tree κ ν} (hValid : Valid tree) :
    lookup key (erase key tree) = none := by
  have hValidErase := valid_erase (key := key) hValid
  have hBounds := split_bounds (pivot := key) hValid.1
  cases hLookup : lookup key (erase key tree) with
  | none => rfl
  | some value =>
    have hMem := (lookup_contents hValidErase.1).mp hLookup
    rw [contents_erase, List.mem_append] at hMem
    rcases hMem with hLess | hGreater
    · have hKeyMem : key ∈ (split key tree).less :=
        key_mem_contents.mp ⟨value, hLess⟩
      exact (lt_irrefl key ((allNodes_key_iff.mp hBounds.1) key hKeyMem)).elim
    · have hKeyMem : key ∈ (split key tree).greater :=
        key_mem_contents.mp ⟨value, hGreater⟩
      exact (lt_irrefl key ((allNodes_key_iff.mp hBounds.2) key hKeyMem)).elim

end Tree
end Treap
end Cslib.Algorithms.Lean
