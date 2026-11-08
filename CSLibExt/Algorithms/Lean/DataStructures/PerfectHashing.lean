/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.List.Basic

public import Init.Data.Vector.Lemmas

/-!
# Perfect hashing (two-level static scheme)

A static set of keys can be stored with worst-case constant lookup time by the
two-level scheme of Fredman, Komlós, and Szemerédi, presented in CLRS,
Section 11.5. A primary hash function sends each key to one of several buckets. Each
bucket `i` holding `nᵢ` keys gets its own secondary table of size `mᵢ = nᵢ²` and its
own secondary hash function that is *injective* on the keys of that bucket, so a lookup
probes exactly one secondary slot and never follows a chain or a probe sequence.

This file models the scheme as data with a correctness predicate. `PerfectHashing`
stores the bucket count, the secondary table sizes and hash functions, and the
secondary tables themselves. `PerfectHashing.Valid` requires every stored binding to
sit in the slot selected by the two hash functions for its key, plus injectivity of
each secondary hash on the keys stored in its bucket. The injectivity clause is
implied by the placement clause (two stored keys at the same secondary slot would
have to share a single slot), which is `Valid.injective_of_placed`; it is kept as a
separate field because it is the property the FKS construction has to achieve when
choosing the secondary hash functions.

## Main statements

* `lookup_eq_some_of_stored` and `stored_of_lookup_eq_some`: under `Valid`, lookup
  succeeds with value `v` for key `k` exactly when some slot stores `(k, v)`. The
  slot contents are equivalently described by the list abstraction `entries`
  (`mem_entries_iff`), with corollaries `lookup_eq_some_of_mem_entries` and
  `mem_entries_of_lookup_eq_some`. Stored values are unique (`stored_unique`), so
  the contents form a partial function from keys to values.
* `totalSecondarySpace` is `∑ i, mᵢ`, the total number of secondary slots. Under the
  FKS sizing rule `SquareSized` (`mᵢ = nᵢ²` for every bucket), it equals
  `∑ i, nᵢ²` (`totalSecondarySpace_eq_sum_sq`) and is at most the square of the total
  number of keys (`totalSecondarySpace_le_totalKeys_sq`).

## What is not proved here

The existence theorems of the FKS method are out of scope. CLRS shows that a primary
hash function with `∑ i, nᵢ² = O(n)` exists and can be found by random sampling from
a universal family, and that for each bucket a collision-free secondary hash into
`nᵢ²` slots exists because a random universal hash is injective on `nᵢ` keys with
probability at least `1 / 2`. Those arguments are probabilistic counting over a hash
family (Markov's inequality applied to expected collision counts). Collision counting
for a universal family (such as the mod-prime family) is a prerequisite for that work
but is not developed or used here; neither that counting nor the linear-space bound
is claimed in this module.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u v

/--
A static two-level (FKS) hash table. The primary hash selects a bucket
`primaryHash k % bucketCount`; inside bucket `i`, the secondary hash selects the slot
`secondaryHash i k % secondarySize i` of a table with one binding per slot. No
existence or expected-time claim about the hash functions is made; correctness is
conditioned on `PerfectHashing.Valid`.
-/
public structure PerfectHashing (α : Type u) (β : Type v) (primaryHash : α → Nat) where
  /-- The positive number of primary buckets. -/
  bucketCount : Nat
  /-- The table has at least one bucket. -/
  bucketCount_pos : 0 < bucketCount
  /-- The number of slots in each bucket's secondary table. -/
  secondarySize : Fin bucketCount → Nat
  /-- The secondary hash function of each bucket, reduced modulo the bucket size. -/
  secondaryHash : Fin bucketCount → α → Nat
  /-- The secondary tables, one optional binding per slot. -/
  secondaryTable : ∀ i : Fin bucketCount, Vector (Option (α × β)) (secondarySize i)

namespace PerfectHashing

variable {α : Type u} {β : Type v} {primaryHash : α → Nat}

private def primaryIndex (table : PerfectHashing α β primaryHash) (key : α) :
    Fin table.bucketCount :=
  ⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩

/--
Looks up a key by evaluating the primary and secondary hashes and inspecting the
single selected slot. Returns the stored value when that slot holds the key, and
`none` otherwise (in particular when the bucket's secondary table is empty).
-/
public def lookup [DecidableEq α] (key : α) (table : PerfectHashing α β primaryHash) :
    Option β :=
  let i : Fin table.bucketCount :=
    ⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩
  if hs : 0 < table.secondarySize i then
    match (table.secondaryTable i).get
        ⟨table.secondaryHash i key % table.secondarySize i, Nat.mod_lt _ hs⟩ with
    | some (k', v) => if k' = key then some v else none
    | none => none
  else
    none

/-- Unfolding of `lookup` with the primary index named. -/
private theorem lookup_def [DecidableEq α] (key : α)
    (table : PerfectHashing α β primaryHash) :
    lookup key table =
      if hs : 0 < table.secondarySize (primaryIndex table key) then
        match (table.secondaryTable (primaryIndex table key)).get
            ⟨table.secondaryHash (primaryIndex table key) key %
              table.secondarySize (primaryIndex table key), Nat.mod_lt _ hs⟩ with
        | some (k', v) => if k' = key then some v else none
        | none => none
      else
        none :=
  rfl

/-- The empty table for the given bucket sizes and secondary hash functions. -/
public def empty (primaryHash : α → Nat) (bucketCount : Nat)
    (bucketCount_pos : 0 < bucketCount) (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) :
    PerfectHashing α β primaryHash where
  bucketCount := bucketCount
  bucketCount_pos := bucketCount_pos
  secondarySize := secondarySize
  secondaryHash := secondaryHash
  secondaryTable := fun i => Vector.replicate (secondarySize i) none

/-- Every secondary slot of the empty table is vacant. -/
private theorem empty_get (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount)
    (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat)
    (i : Fin (empty primaryHash bucketCount bucketCount_pos secondarySize
      secondaryHash : PerfectHashing α β primaryHash).bucketCount)
    (j : Fin ((empty primaryHash bucketCount bucketCount_pos secondarySize
      secondaryHash : PerfectHashing α β primaryHash).secondarySize i)) :
    ((empty primaryHash bucketCount bucketCount_pos secondarySize secondaryHash :
      PerfectHashing α β primaryHash).secondaryTable i).get j = none :=
  Vector.getElem_replicate j.isLt

/-- Whether some secondary slot, in any bucket, holds the binding `(key, value)`. -/
public def Stored (table : PerfectHashing α β primaryHash) (key : α) (value : β) :
    Prop :=
  ∃ (i : Fin table.bucketCount) (j : Fin (table.secondarySize i)),
    (table.secondaryTable i).get j = some (key, value)

/--
The bucket-independent contents of the table as a list: every occupied secondary
slot, bucket by bucket. Stored bindings are exactly the members of this list
(`mem_entries_iff`).
-/
public def entries (table : PerfectHashing α β primaryHash) : List (α × β) :=
  (List.finRange table.bucketCount).flatMap fun i =>
    (List.finRange (table.secondarySize i)).filterMap fun j =>
      (table.secondaryTable i).get j

/--
The correctness invariant of a two-level table. `placed` says every stored binding
lies in the bucket selected by the primary hash for its key, at the slot selected by
that bucket's secondary hash. `injective` says each secondary hash is injective, as
a slot selector, on the keys stored in its bucket: no two stored keys of one bucket
collide. The second clause follows from the first (`Valid.injective_of_placed`); it
is recorded separately because choosing such injective secondary hashes is the task
of the FKS construction.
-/
public structure Valid (table : PerfectHashing α β primaryHash) : Prop where
  /-- Every binding sits at the slot its key hashes to at both levels. -/
  placed : ∀ (i : Fin table.bucketCount) (j : Fin (table.secondarySize i))
      (key : α) (value : β),
    (table.secondaryTable i).get j = some (key, value) →
      (⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩ :
        Fin table.bucketCount) = i ∧
        j.val = table.secondaryHash i key % table.secondarySize i
  /-- Each bucket's secondary hash does not collide on its stored keys. -/
  injective : ∀ (i : Fin table.bucketCount) (key₁ key₂ : α),
    (∃ (j : Fin (table.secondarySize i)) (value : β),
      (table.secondaryTable i).get j = some (key₁, value)) →
    (∃ (j : Fin (table.secondarySize i)) (value : β),
      (table.secondaryTable i).get j = some (key₂, value)) →
    table.secondaryHash i key₁ % table.secondarySize i =
      table.secondaryHash i key₂ % table.secondarySize i →
    key₁ = key₂

namespace Valid

/--
Placement implies secondary injectivity on stored keys: if two stored keys of one
bucket selected the same slot, both bindings would have to occupy that slot, so the
bindings, and in particular the keys, are equal.
-/
public theorem injective_of_placed {table : PerfectHashing α β primaryHash}
    (placed : ∀ (i : Fin table.bucketCount) (j : Fin (table.secondarySize i))
      (key : α) (value : β),
      (table.secondaryTable i).get j = some (key, value) →
        (⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩ :
          Fin table.bucketCount) = i ∧
          j.val = table.secondaryHash i key % table.secondarySize i) :
    ∀ (i : Fin table.bucketCount) (key₁ key₂ : α),
      (∃ (j : Fin (table.secondarySize i)) (value : β),
        (table.secondaryTable i).get j = some (key₁, value)) →
      (∃ (j : Fin (table.secondarySize i)) (value : β),
        (table.secondaryTable i).get j = some (key₂, value)) →
      table.secondaryHash i key₁ % table.secondarySize i =
        table.secondaryHash i key₂ % table.secondarySize i →
      key₁ = key₂ := by
  intro i key₁ key₂ h₁ h₂ hhash
  obtain ⟨j₁, value₁, hslot₁⟩ := h₁
  obtain ⟨j₂, value₂, hslot₂⟩ := h₂
  have hj₁ : j₁.val = table.secondaryHash i key₁ % table.secondarySize i :=
    (placed i j₁ key₁ value₁ hslot₁).2
  have hj₂ : j₂.val = table.secondaryHash i key₂ % table.secondarySize i :=
    (placed i j₂ key₂ value₂ hslot₂).2
  have hjeq : j₁ = j₂ := Fin.ext (by rw [hj₁, hj₂]; exact hhash)
  subst hjeq
  rw [hslot₁] at hslot₂
  have hpair : (key₁, value₁) = (key₂, value₂) := Option.some_inj.mp hslot₂
  exact congrArg Prod.fst hpair

/-- A table satisfying the placement clause is valid. -/
public theorem mk_of_placed {table : PerfectHashing α β primaryHash}
    (placed : ∀ (i : Fin table.bucketCount) (j : Fin (table.secondarySize i))
      (key : α) (value : β),
      (table.secondaryTable i).get j = some (key, value) →
        (⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩ :
          Fin table.bucketCount) = i ∧
          j.val = table.secondaryHash i key % table.secondarySize i) :
    Valid table :=
  ⟨placed, injective_of_placed placed⟩

end Valid

/-- The list abstraction `entries` contains exactly the stored bindings. -/
public theorem mem_entries_iff (table : PerfectHashing α β primaryHash) (key : α)
    (value : β) :
    (key, value) ∈ table.entries ↔ Stored table key value := by
  simp [entries, Stored]

/-- The empty table is valid: no slot is occupied, so both clauses are vacuous. -/
public theorem valid_empty (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount)
    (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) :
    Valid (empty primaryHash bucketCount bucketCount_pos secondarySize secondaryHash :
      PerfectHashing α β primaryHash) := by
  apply Valid.mk_of_placed
  intro i j _ _ h
  rw [empty_get] at h
  exact absurd h (by simp)

/-- Nothing is stored in the empty table. -/
public theorem not_stored_empty (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount)
    (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) (key : α) (value : β) :
    ¬ Stored (empty primaryHash bucketCount bucketCount_pos secondarySize secondaryHash :
      PerfectHashing α β primaryHash) key value := by
  rintro ⟨i, j, h⟩
  rw [empty_get] at h
  exact absurd h (by simp)

/--
Soundness of lookup, with no validity hypothesis: a successful lookup only returns a
value that is actually stored alongside the key in some secondary slot.
-/
public theorem stored_of_lookup_eq_some [DecidableEq α]
    {table : PerfectHashing α β primaryHash} {key : α} {value : β}
    (h : lookup key table = some value) : Stored table key value := by
  rw [lookup_def] at h
  by_cases hs : 0 < table.secondarySize (primaryIndex table key)
  · rw [dite_eq_left hs] at h
    cases hget : (table.secondaryTable (primaryIndex table key)).get
        ⟨table.secondaryHash (primaryIndex table key) key %
          table.secondarySize (primaryIndex table key), Nat.mod_lt _ hs⟩ with
    | none =>
        rw [hget] at h
        exact absurd h (by simp)
    | some kv =>
        obtain ⟨k', v'⟩ := kv
        rw [hget] at h
        by_cases hk : k' = key
        · simp only [hk, ite_true] at h
          have hv : v' = value := Option.some_inj.mp h
          have hpair : (k', v') = (key, value) := Prod.ext hk hv
          rw [hpair] at hget
          exact ⟨primaryIndex table key,
            ⟨table.secondaryHash (primaryIndex table key) key %
              table.secondarySize (primaryIndex table key), Nat.mod_lt _ hs⟩, hget⟩
        · simp only [hk, ite_false] at h
          exact absurd h (by simp)
  · rw [dite_eq_right hs] at h
    exact absurd h (by simp)

/--
Completeness of lookup under `Valid`: a stored binding is found, because placement
puts it in exactly the bucket and slot that lookup probes.
-/
public theorem lookup_eq_some_of_stored [DecidableEq α]
    {table : PerfectHashing α β primaryHash} (valid : Valid table) {key : α}
    {value : β} (h : Stored table key value) :
    lookup key table = some value := by
  obtain ⟨i, j, hj⟩ := h
  obtain ⟨hprim, hsec⟩ := valid.placed i j key value hj
  have hpi : i = primaryIndex table key := hprim.symm
  subst hpi
  rw [lookup_def]
  have hsize : 0 < table.secondarySize (primaryIndex table key) := by
    have hlt := j.isLt
    omega
  rw [dite_eq_left hsize]
  have hidx : (⟨table.secondaryHash (primaryIndex table key) key %
        table.secondarySize (primaryIndex table key), Nat.mod_lt _ hsize⟩ :
      Fin (table.secondarySize (primaryIndex table key))) = j :=
    Fin.ext hsec.symm
  rw [hidx, hj]
  simp

/-- Under `Valid`, the stored value for a key is unique when it exists. This is
a direct consequence of placement (both bindings would occupy the one slot their
shared key hashes to), so it needs no decidable equality on keys. -/
public theorem stored_unique
    {table : PerfectHashing α β primaryHash} (valid : Valid table) {key : α}
    {value₁ value₂ : β} (h₁ : Stored table key value₁)
    (h₂ : Stored table key value₂) : value₁ = value₂ := by
  obtain ⟨i₁, j₁, hj₁⟩ := h₁
  obtain ⟨i₂, j₂, hj₂⟩ := h₂
  obtain ⟨hp₁, hs₁⟩ := valid.placed i₁ j₁ key value₁ hj₁
  obtain ⟨hp₂, hs₂⟩ := valid.placed i₂ j₂ key value₂ hj₂
  have hi : i₁ = i₂ := hp₁.symm.trans hp₂
  subst hi
  have hj : j₁ = j₂ := Fin.ext (by rw [hs₁, hs₂])
  subst hj
  rw [hj₁] at hj₂
  exact (Prod.mk.injEq _ _ _ _).mp (Option.some_inj.mp hj₂) |>.2

/-- Under `Valid`, lookup fails exactly on keys that are not stored. -/
public theorem lookup_eq_none_iff [DecidableEq α]
    {table : PerfectHashing α β primaryHash} (valid : Valid table) (key : α) :
    lookup key table = none ↔ ∀ value : β, ¬ Stored table key value := by
  constructor
  · intro h value hstored
    rw [lookup_eq_some_of_stored valid hstored] at h
    exact absurd h (by simp)
  · intro h
    cases hlookup : lookup key table with
    | none => rfl
    | some value => exact absurd (stored_of_lookup_eq_some hlookup) (h value)

/-- Lookup completeness phrased against the list abstraction `entries`. -/
public theorem lookup_eq_some_of_mem_entries [DecidableEq α]
    {table : PerfectHashing α β primaryHash} (valid : Valid table) {key : α}
    {value : β} (h : (key, value) ∈ table.entries) :
    lookup key table = some value :=
  lookup_eq_some_of_stored valid ((mem_entries_iff table key value).mp h)

/-- Lookup soundness phrased against the list abstraction `entries`. -/
public theorem mem_entries_of_lookup_eq_some [DecidableEq α]
    {table : PerfectHashing α β primaryHash} {key : α} {value : β}
    (h : lookup key table = some value) : (key, value) ∈ table.entries :=
  (mem_entries_iff table key value).mpr (stored_of_lookup_eq_some h)

/-- Looking up any key in the empty table returns `none`. -/
@[simp]
public theorem lookup_empty [DecidableEq α] (bucketCount : Nat)
    (bucketCount_pos : 0 < bucketCount) (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) (key : α) :
    lookup key (empty primaryHash bucketCount bucketCount_pos secondarySize
      secondaryHash : PerfectHashing α β primaryHash) = none :=
  (lookup_eq_none_iff
    (valid_empty bucketCount bucketCount_pos secondarySize secondaryHash) key).mpr
    (fun value => not_stored_empty bucketCount bucketCount_pos secondarySize
      secondaryHash key value)

/-- The empty table has no entries. -/
@[simp]
public theorem entries_empty (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount)
    (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) :
    entries (empty primaryHash bucketCount bucketCount_pos secondarySize secondaryHash :
      PerfectHashing α β primaryHash) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨key, value⟩ hmem
  exact not_stored_empty bucketCount bucketCount_pos secondarySize secondaryHash
    key value ((mem_entries_iff _ key value).mp hmem)

/-- The number of occupied slots of bucket `i`, the `nᵢ` of the FKS analysis. -/
public def bucketSize (table : PerfectHashing α β primaryHash)
    (i : Fin table.bucketCount) : Nat :=
  ((List.finRange (table.secondarySize i)).filter fun j =>
    ((table.secondaryTable i).get j).isSome).length

/-- The total number of stored keys, `∑ i, nᵢ`. -/
public def totalKeys (table : PerfectHashing α β primaryHash) : Nat :=
  ∑ i : Fin table.bucketCount, bucketSize table i

/-- The total secondary space: the total number of secondary slots, `∑ i, mᵢ`. -/
public def totalSecondarySpace (table : PerfectHashing α β primaryHash) : Nat :=
  ∑ i : Fin table.bucketCount, table.secondarySize i

/--
The FKS sizing rule: every bucket's secondary table has size the square of the
number of keys in the bucket, `mᵢ = nᵢ²`.
-/
public def SquareSized (table : PerfectHashing α β primaryHash) : Prop :=
  ∀ i : Fin table.bucketCount, table.secondarySize i = (bucketSize table i) ^ 2

/-- A bucket cannot hold more bindings than it has slots. -/
public theorem bucketSize_le_secondarySize (table : PerfectHashing α β primaryHash)
    (i : Fin table.bucketCount) :
    bucketSize table i ≤ table.secondarySize i := by
  rw [bucketSize]
  calc ((List.finRange (table.secondarySize i)).filter fun j =>
        ((table.secondaryTable i).get j).isSome).length
      ≤ (List.finRange (table.secondarySize i)).length :=
        List.length_filter_le _ _
    _ = table.secondarySize i := List.length_finRange

/-- Each bucket's secondary size is dominated by the total secondary space. -/
public theorem secondarySize_le_totalSecondarySpace
    (table : PerfectHashing α β primaryHash) (i : Fin table.bucketCount) :
    table.secondarySize i ≤ totalSecondarySpace table :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Under the FKS sizing rule, the total secondary space is the sum of squares `∑ i, nᵢ²`. -/
public theorem totalSecondarySpace_eq_sum_sq
    {table : PerfectHashing α β primaryHash} (hsq : SquareSized table) :
    totalSecondarySpace table =
      ∑ i : Fin table.bucketCount, (bucketSize table i) ^ 2 :=
  Finset.sum_congr rfl fun i _ => hsq i

/--
Elementary space bound under the FKS sizing rule: the total secondary space
`∑ i, nᵢ²` is at most `(∑ i, nᵢ)²`, the square of the total number of keys. The
linear bound `∑ i, nᵢ² = O(n)` of FKS additionally requires a good primary hash
function, whose existence is a probabilistic statement not proved here.
-/
public theorem totalSecondarySpace_le_totalKeys_sq
    {table : PerfectHashing α β primaryHash} (hsq : SquareSized table) :
    totalSecondarySpace table ≤ (totalKeys table) ^ 2 := by
  rw [totalSecondarySpace_eq_sum_sq hsq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Nat.zero_le _)

end PerfectHashing

end Cslib.Algorithms.Lean
