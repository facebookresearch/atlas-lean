/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree.Delete
public import CSLibExt.Algorithms.Lean.DataStructures.BloomFilter
public import Mathlib.Data.Finmap
public import Mathlib.Data.Finset.Basic

/-!
# Dictionary specification records

Specification records for finite ordered sets, finite maps, and approximate
membership, with adapters for the existing binary search trees (insertion and
deletion) and Bloom filters; further adapters (AVL trees,
hash tables) live next to their providers.

The approximate-membership record is relational: it has no abstraction
function to an exact set and no converse membership law, so a positive
answer never has to mean the element was inserted. False-positive rates
are not part of these records. The existing provider results are recorded
here with their direction: the BloomFilterFalsePositive module in namespace
Cslib.Algorithms.Lean.BloomFilter proves the exact rate under uniform
independent hashing in falsePositiveProb_eq, and Bloom's classical formula
as a lower bound in classical_le_falsePositiveProb. Neither is an upper
bound; an explicit parameterized upper bound remains a separate obligation.
-/

set_option autoImplicit false

universe u v w

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace DictionarySpec

/-- A finite ordered-set implementation over a linear order, refined by a
`Finset` abstraction: every operation updates the abstraction exactly as
the corresponding `Finset` operation, on states satisfying the invariant. -/
public structure OrderedSetSpec (α : Type u) [LinearOrder α] (S : Type v) where
  /-- The empty state. -/
  empty : S
  /-- Insert a key. -/
  insert : α → S → S
  /-- Delete a key. -/
  delete : α → S → S
  /-- Membership of a key in a state. -/
  mem : α → S → Prop
  /-- The representation invariant. -/
  inv : S → Prop
  /-- The finite-set abstraction. -/
  toFinset : S → Finset α
  inv_empty : inv empty
  inv_insert : ∀ (x : α) {s : S}, inv s → inv (insert x s)
  inv_delete : ∀ (x : α) {s : S}, inv s → inv (delete x s)
  toFinset_empty : toFinset empty = ∅
  toFinset_insert : ∀ (x : α) {s : S}, inv s →
    toFinset (insert x s) = Insert.insert x (toFinset s)
  toFinset_delete : ∀ (x : α) {s : S}, inv s →
    toFinset (delete x s) = (toFinset s).erase x
  mem_iff_toFinset : ∀ (x : α) {s : S}, inv s → (mem x s ↔ x ∈ toFinset s)

/-- An inserted key is a member. -/
public theorem OrderedSetSpec.mem_insert_self {α : Type u} [LinearOrder α]
    {S : Type v} (spec : OrderedSetSpec α S) (x : α) {s : S}
    (hs : spec.inv s) : spec.mem x (spec.insert x s) := by
  rw [spec.mem_iff_toFinset x (spec.inv_insert x hs), spec.toFinset_insert x hs]
  exact Finset.mem_insert_self x _

/-- A deleted key is not a member. -/
public theorem OrderedSetSpec.not_mem_delete_self {α : Type u} [LinearOrder α]
    {S : Type v} (spec : OrderedSetSpec α S) (x : α) {s : S}
    (hs : spec.inv s) : ¬ spec.mem x (spec.delete x s) := by
  rw [spec.mem_iff_toFinset x (spec.inv_delete x hs), spec.toFinset_delete x hs]
  intro h
  exact (Finset.mem_erase.mp h).1 rfl

/-- A finite-map implementation, refined by a `Finmap` abstraction: every
operation updates the abstraction exactly as the corresponding `Finmap`
operation, lookup agrees with the abstraction, on states satisfying the
invariant. -/
public structure FiniteMapSpec (α : Type u) [DecidableEq α] (β : Type v)
    (S : Type w) where
  /-- The empty state. -/
  empty : S
  /-- Bind a key to a value, replacing any earlier binding. -/
  insert : α → β → S → S
  /-- Delete a key's binding. -/
  erase : α → S → S
  /-- Look up a key's value. -/
  lookup : α → S → Option β
  /-- The representation invariant. -/
  inv : S → Prop
  /-- The finite-map abstraction. -/
  toFinmap : S → Finmap (fun _ : α => β)
  inv_empty : inv empty
  inv_insert : ∀ (x : α) (v : β) {s : S}, inv s → inv (insert x v s)
  inv_erase : ∀ (x : α) {s : S}, inv s → inv (erase x s)
  toFinmap_empty : toFinmap empty = ∅
  toFinmap_insert : ∀ (x : α) (v : β) {s : S}, inv s →
    toFinmap (insert x v s) = Finmap.insert x v (toFinmap s)
  toFinmap_erase : ∀ (x : α) {s : S}, inv s →
    toFinmap (erase x s) = Finmap.erase x (toFinmap s)
  lookup_eq_toFinmap : ∀ (x : α) {s : S}, inv s →
    lookup x s = Finmap.lookup x (toFinmap s)

/-- An inserted key looks up to its inserted value. -/
public theorem FiniteMapSpec.lookup_insert_self {α : Type u} [DecidableEq α]
    {β : Type v} {S : Type w} (spec : FiniteMapSpec α β S) (x : α) (v : β)
    {s : S} (hs : spec.inv s) : spec.lookup x (spec.insert x v s) = some v := by
  rw [spec.lookup_eq_toFinmap x (spec.inv_insert x v hs),
    spec.toFinmap_insert x v hs, Finmap.lookup_insert]

/-- A deleted key looks up to nothing. -/
public theorem FiniteMapSpec.lookup_erase_self {α : Type u} [DecidableEq α]
    {β : Type v} {S : Type w} (spec : FiniteMapSpec α β S) (x : α) {s : S}
    (hs : spec.inv s) : spec.lookup x (spec.erase x s) = none := by
  rw [spec.lookup_eq_toFinmap x (spec.inv_erase x hs),
    spec.toFinmap_erase x hs, Finmap.lookup_erase]

/-- An approximate-membership implementation: a state represents a finite
set of inserted elements through a relation, insertion extends the
represented set, and represented elements are always reported present
(no false negatives). There is intentionally no converse law. -/
public structure ApproxMembershipSpec (α : Type u) [DecidableEq α] (F : Type v) where
  /-- The empty state, before any insertion. -/
  empty : F
  /-- Insert an element. -/
  insert : α → F → F
  /-- The (possibly over-approximating) membership test. -/
  mayContain : α → F → Prop
  /-- `Represents f s`: every element of `s` has been inserted into `f`. -/
  Represents : F → Finset α → Prop
  represents_empty : Represents empty ∅
  represents_insert : ∀ (x : α) {f : F} {s : Finset α},
    Represents f s → Represents (insert x f) (Insert.insert x s)
  no_false_negative : ∀ (x : α) {f : F} {s : Finset α},
    Represents f s → x ∈ s → mayContain x f

/-- An element is reported present in the state built by inserting it into
any representing state. -/
public theorem ApproxMembershipSpec.mayContain_insert_self {α : Type u}
    [DecidableEq α] {F : Type v} (spec : ApproxMembershipSpec α F) (x : α) {f : F}
    {s : Finset α} (hf : spec.Represents f s) :
    spec.mayContain x (spec.insert x f) := by
  exact spec.no_false_negative x (spec.represents_insert x hf) (Finset.mem_insert_self x s)

/-- Binary search trees refine the finite ordered-set record, with the
inorder traversal as the finite-set abstraction. Deletion is the deletion
of `BinarySearchTree.Delete`. -/
public def bstSpec (α : Type u) [LinearOrder α] :
    OrderedSetSpec α (BinaryTree α) where
  empty := .nil
  insert := BinarySearchTree.insert
  delete := BinarySearchTree.delete
  mem := fun x tree => x ∈ tree
  inv := BinarySearchTree.Ordered
  toFinset := fun tree => (BinarySearchTree.inorder tree).toFinset
  inv_empty := by trivial
  inv_insert := by intro x s hs; exact BinarySearchTree.ordered_insert hs
  inv_delete := by intro x s hs; exact BinarySearchTree.ordered_delete hs
  toFinset_empty := by rfl
  toFinset_insert := by
    intro x s _hs
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, BinarySearchTree.mem_inorder,
      BinarySearchTree.mem_insert, Finset.mem_insert]
  toFinset_delete := by
    intro x s hs
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, BinarySearchTree.mem_inorder,
      BinarySearchTree.mem_delete hs, Finset.mem_erase]
    exact and_comm
  mem_iff_toFinset := by
    intro x s _hs
    simp only [List.mem_toFinset, BinarySearchTree.mem_inorder]

/-- Folding insertions over a list preserves a positive answer. -/
private theorem foldl_preserves_mayContain {α : Type u} {m : Nat} (x : α)
    (l : List α) (b : BloomFilter α m)
    (present : b.mayContain x = true) :
    (l.foldl BloomFilter.insert b).mayContain x = true := by
  induction l generalizing b with
  | nil => exact present
  | cons y l ih =>
    rw [List.foldl_cons]
    exact ih _ (BloomFilter.mayContain_insert_mono b x y present)

/-- An element of the folded list is reported present after the fold. -/
private theorem foldl_mayContain_of_mem {α : Type u} {m : Nat} (x : α)
    (l : List α) (b : BloomFilter α m) (hmem : x ∈ l) :
    (l.foldl BloomFilter.insert b).mayContain x = true := by
  induction l generalizing b with
  | nil => exact absurd hmem List.not_mem_nil
  | cons y l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact foldl_preserves_mayContain x l _
        (BloomFilter.mayContain_insert_self b x)
    · exact ih _ hmem

/-- Bloom filters with a fixed list of hash functions instantiate
approximate membership: a filter represents a finite set `s` when some list
with set of entries `s` yields the filter by insertions from the empty filter.
A filter does not determine a unique history or represented set. -/
public def bloomSpec {α : Type u} [DecidableEq α] {m : Nat} (hashes : List (α → Fin m)) :
    ApproxMembershipSpec α (BloomFilter α m) where
  empty := BloomFilter.empty hashes
  insert := fun x filter => filter.insert x
  mayContain := fun x filter => filter.mayContain x = true
  Represents := fun filter s =>
    ∃ l : List α, l.toFinset = s ∧
      l.foldl BloomFilter.insert (BloomFilter.empty hashes) = filter
  represents_empty := by exact ⟨[], rfl, rfl⟩
  represents_insert := by
    intro x f s hf
    obtain ⟨l, hl, hfold⟩ := hf
    refine ⟨l ++ [x], ?_, ?_⟩
    · ext y
      simp only [List.mem_toFinset, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, Finset.mem_insert]
      rw [← List.mem_toFinset, hl]
      exact or_comm
    · rw [List.foldl_append, hfold, List.foldl_cons, List.foldl_nil]
  no_false_negative := by
    intro x f s hf hx
    obtain ⟨l, hl, hfold⟩ := hf
    have hmem : x ∈ l := List.mem_toFinset.mp (hl ▸ hx)
    subst hfold
    exact foldl_mayContain_of_mem x l _ hmem

end DictionarySpec
end Cslib.Algorithms.Lean
end
