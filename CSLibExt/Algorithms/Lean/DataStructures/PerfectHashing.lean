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
**Two-level perfect hash table.** Fix a type $\alpha$ of keys, a type $\beta$ of values and a
primary hash function $h : \alpha \to \mathbb{N}$. A two-level (FKS) perfect hash table consists
of a number $b > 0$ of buckets and, for each bucket $i < b$, a secondary size $m_i \in \mathbb{N}$,
a secondary hash function $h_i : \alpha \to \mathbb{N}$ and a secondary table of $m_i$ slots, each
of which is empty or holds one binding $(k, v)$ with $k \in \alpha$ and $v \in \beta$.

The intended position of a key $k$ is slot $h_i(k) \bmod m_i$ of bucket $i = h(k) \bmod b$. The
structure itself imposes no condition on the hash functions and does not require bindings to sit
at their intended positions; that requirement is the separate validity condition.
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
**Lookup in a perfect hash table.** To look up a key $k$ in a two-level perfect hash table with
$b$ buckets, primary hash $h$, secondary sizes $m_i$ and secondary hashes $h_i$, let
$i = h(k) \bmod b$. If $m_i = 0$, the lookup returns nothing. Otherwise it inspects the single slot
$h_i(k) \bmod m_i$ of the secondary table of bucket $i$: if that slot holds a binding $(k, v)$, the
lookup returns $v$; if the slot is empty or holds a binding with a different key, the lookup
returns nothing.
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

/-- **Empty perfect hash table.** Given a primary hash function $h$ from keys to natural
numbers, a number of buckets $b > 0$, and for each bucket $i < b$ a secondary table size $m_i$
and a secondary hash function $h_i$, the empty table is the two-level perfect hash table with
primary hash $h$, $b$ buckets, secondary sizes $m_i$ and secondary hashes $h_i$ in which every
slot of every secondary table is vacant. -/
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

/-- **Bindings stored in a perfect hash table.** A key $k$ and a value $v$ are stored in a
two-level perfect hash table $T$ when some secondary slot, in some bucket of $T$, holds the
binding $(k, v)$. -/
public def Stored (table : PerfectHashing α β primaryHash) (key : α) (value : β) :
    Prop :=
  ∃ (i : Fin table.bucketCount) (j : Fin (table.secondarySize i)),
    (table.secondaryTable i).get j = some (key, value)

/-- **Entries of a perfect hash table.** The entries of a two-level perfect hash table form
the list of the bindings $(k, v)$ held in its occupied secondary slots, listed bucket by bucket
in increasing bucket order and, within each bucket, in increasing slot order.

A pair $(k, v)$ is a member of this list exactly when it is held in some slot of the table. -/
public def entries (table : PerfectHashing α β primaryHash) : List (α × β) :=
  (List.finRange table.bucketCount).flatMap fun i =>
    (List.finRange (table.secondarySize i)).filterMap fun j =>
      (table.secondaryTable i).get j

/--
**Valid perfect hash table.** Let $T$ be a two-level perfect hash table with primary hash $h$,
$b$ buckets, secondary table sizes $m_i$ and secondary hashes $g_i$. Then $T$ is valid when two
conditions hold. Placement: whenever slot $j$ of bucket $i$ holds a binding $(k, v)$, we have
$i = h(k) \bmod b$ and $j = g_i(k) \bmod m_i$. Injectivity: for every bucket $i$, if keys $k_1$
and $k_2$ both occur in bindings stored in bucket $i$ and $g_i(k_1) \bmod m_i = g_i(k_2) \bmod m_i$,
then $k_1 = k_2$.

The injectivity condition follows from placement. It is recorded separately because choosing
secondary hash functions that are injective on each bucket's keys is the task of the FKS
construction.
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

/-- **Placement implies secondary injectivity.** Let $T$ be a two-level perfect hash table
with $b$ buckets and primary hash $h$, and for each bucket $i$ let $m_i$ be its secondary table
size and $h_i$ its secondary hash. Suppose every binding $(k, v)$ held in slot $j$ of bucket $i$
satisfies $h(k) \bmod b = i$ and $j = h_i(k) \bmod m_i$. Then for every bucket $i$ and all keys
$k_1, k_2$ that are each held, with some value, in some slot of bucket $i$, if
$h_i(k_1) \bmod m_i = h_i(k_2) \bmod m_i$, then $k_1 = k_2$. -/
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

/-- **Placement suffices for validity of a perfect hash table.** Let $T$ be a two-level perfect
hash table with $b$ buckets, primary hash $h$, secondary sizes $m_i$ and secondary hashes $h_i$.
If, whenever slot $j$ of the secondary table of bucket $i$ holds a binding $(k, v)$, we have
$h(k) \bmod b = i$ and $j = h_i(k) \bmod m_i$, then $T$ is valid. -/
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

/-- **Entries of a perfect hash table are its stored bindings.** For every two-level perfect hash
table, every key $k$ and every value $v$, the pair $(k, v)$ belongs to the list of entries of the
table (the contents of its occupied secondary slots, bucket by bucket) if and only if some
secondary slot of the table holds the binding $(k, v)$. -/
public theorem mem_entries_iff (table : PerfectHashing α β primaryHash) (key : α)
    (value : β) :
    (key, value) ∈ table.entries ↔ Stored table key value := by
  simp [entries, Stored]

/-- **The empty perfect hash table is valid.** For every primary hash function, every positive
number of buckets, and every choice of secondary table sizes and secondary hash functions, the
empty two-level perfect hash table with these parameters is valid: no slot is occupied, so both
conditions of validity hold vacuously. -/
public theorem valid_empty (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount)
    (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) :
    Valid (empty primaryHash bucketCount bucketCount_pos secondarySize secondaryHash :
      PerfectHashing α β primaryHash) := by
  apply Valid.mk_of_placed
  intro i j _ _ h
  rw [empty_get] at h
  exact absurd h (by simp)

/-- **The empty perfect hash table stores nothing.** For every primary hash function, every number
$b > 0$ of buckets, every choice of secondary sizes and secondary hash functions, every key $k$
and every value $v$, no secondary slot of the empty two-level perfect hash table with these data
holds the binding $(k, v)$. -/
public theorem not_stored_empty (bucketCount : Nat) (bucketCount_pos : 0 < bucketCount)
    (secondarySize : Fin bucketCount → Nat)
    (secondaryHash : Fin bucketCount → α → Nat) (key : α) (value : β) :
    ¬ Stored (empty primaryHash bucketCount bucketCount_pos secondarySize secondaryHash :
      PerfectHashing α β primaryHash) key value := by
  rintro ⟨i, j, h⟩
  rw [empty_get] at h
  exact absurd h (by simp)

/--
**Soundness of perfect-hash lookup.** For a two-level perfect hash table with decidable equality
on keys, and with no validity hypothesis, if looking up a key $k$ returns a value $v$, then some
secondary slot of the table holds the binding $(k, v)$.
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

/-- **Lookup finds every stored binding.** For a valid two-level perfect hash table, if the
binding $(k, v)$ is held in some slot of the table, then looking up $k$ returns $v$. -/
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

/-- **Stored values in a valid perfect hash table are unique.** In a valid two-level perfect hash
table, if some secondary slots hold bindings $(k, v_1)$ and $(k, v_2)$ with the same key $k$, then
$v_1 = v_2$.

This is a direct consequence of placement (both bindings would occupy the one slot their shared
key hashes to), so it needs no decidable equality on keys. -/
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

/-- **Lookup fails exactly on unstored keys.** For a valid two-level perfect hash table and
any key $k$, looking up $k$ returns no value if and only if there is no value $v$ such that the
binding $(k, v)$ is held in some slot of the table. -/
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

/-- **Lookup finds every entry.** For a valid two-level perfect hash table, if the pair
$(k, v)$ belongs to the list of entries of the table, then looking up $k$ returns $v$. -/
public theorem lookup_eq_some_of_mem_entries [DecidableEq α]
    {table : PerfectHashing α β primaryHash} (valid : Valid table) {key : α}
    {value : β} (h : (key, value) ∈ table.entries) :
    lookup key table = some value :=
  lookup_eq_some_of_stored valid ((mem_entries_iff table key value).mp h)

/-- **Successful perfect-hash lookups return entries.** For a two-level perfect hash table with
decidable equality on keys, if looking up a key $k$ returns a value $v$, then $(k, v)$ belongs to
the list of entries of the table. No validity hypothesis is needed. -/
public theorem mem_entries_of_lookup_eq_some [DecidableEq α]
    {table : PerfectHashing α β primaryHash} {key : α} {value : β}
    (h : lookup key table = some value) : (key, value) ∈ table.entries :=
  (mem_entries_iff table key value).mpr (stored_of_lookup_eq_some h)

/-- **Lookup in the empty perfect hash table fails.** For every primary hash function, every
number of buckets $b > 0$, all secondary table sizes and secondary hash functions, and every
key $k$, looking up $k$ in the empty table returns no value. -/
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

/-- **The empty perfect hash table has no entries.** For every primary hash function, every
number of buckets $b > 0$, and all secondary table sizes and secondary hash functions, the list
of entries of the empty table is the empty list. -/
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

/-- **Occupancy of a perfect-hashing bucket.** For a two-level perfect hash table and a bucket
$i$, the occupancy $n_i$ of bucket $i$ is the number of slots of the secondary table of bucket
$i$ that hold a binding. It is the $n_i$ of the Fredman–Komlós–Szemerédi analysis. -/
public def bucketSize (table : PerfectHashing α β primaryHash)
    (i : Fin table.bucketCount) : Nat :=
  ((List.finRange (table.secondarySize i)).filter fun j =>
    ((table.secondaryTable i).get j).isSome).length

/-- **Total number of keys of a perfect hash table.** For a two-level perfect hash table, write
$n_i$ for the number of occupied secondary slots of bucket $i$. The total number of keys of the
table is $\sum_i n_i$, the number of occupied secondary slots over all buckets. -/
public def totalKeys (table : PerfectHashing α β primaryHash) : Nat :=
  ∑ i : Fin table.bucketCount, bucketSize table i

/-- **Total secondary space of a perfect hash table.** For a two-level perfect hash table, write
$m_i$ for the number of slots of the secondary table of bucket $i$. The total secondary space of
the table is $\sum_i m_i$, the number of secondary slots over all buckets. -/
public def totalSecondarySpace (table : PerfectHashing α β primaryHash) : Nat :=
  ∑ i : Fin table.bucketCount, table.secondarySize i

/--
**FKS square sizing rule.** A two-level perfect hash table with $b$ buckets is square-sized when,
for every bucket $i < b$, the size $m_i$ of its secondary table equals $n_i^2$, where $n_i$ is the
number of occupied slots of that secondary table.
-/
public def SquareSized (table : PerfectHashing α β primaryHash) : Prop :=
  ∀ i : Fin table.bucketCount, table.secondarySize i = (bucketSize table i) ^ 2

/-- **Bucket occupancy is at most the secondary table size.** For every two-level perfect
hash table and every bucket $i$, the number $n_i$ of occupied slots of bucket $i$ is at most
the number $m_i$ of slots of the secondary table of bucket $i$. -/
public theorem bucketSize_le_secondarySize (table : PerfectHashing α β primaryHash)
    (i : Fin table.bucketCount) :
    bucketSize table i ≤ table.secondarySize i := by
  rw [bucketSize]
  calc ((List.finRange (table.secondarySize i)).filter fun j =>
        ((table.secondaryTable i).get j).isSome).length
      ≤ (List.finRange (table.secondarySize i)).length :=
        List.length_filter_le _ _
    _ = table.secondarySize i := List.length_finRange

/-- **Each secondary table fits in the total secondary space.** In a two-level perfect hash table
with $b$ buckets and secondary sizes $m_0, \dots, m_{b-1}$, every bucket $i < b$ satisfies
$m_i \le \sum_{j < b} m_j$, the total secondary space. -/
public theorem secondarySize_le_totalSecondarySpace
    (table : PerfectHashing α β primaryHash) (i : Fin table.bucketCount) :
    table.secondarySize i ≤ totalSecondarySpace table :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- **Total secondary space under square sizing.** Let $T$ be a two-level perfect hash table
satisfying the FKS sizing rule, and write $n_i$ for the number of occupied secondary slots of
bucket $i$. Then the total secondary space of $T$ equals $\sum_i n_i^2$, the sum over all
buckets $i$. -/
public theorem totalSecondarySpace_eq_sum_sq
    {table : PerfectHashing α β primaryHash} (hsq : SquareSized table) :
    totalSecondarySpace table =
      ∑ i : Fin table.bucketCount, (bucketSize table i) ^ 2 :=
  Finset.sum_congr rfl fun i _ => hsq i

/--
**Quadratic space bound under square sizing.** If a two-level perfect hash table satisfies the
FKS sizing rule, then its total secondary space is at most the square of its total number of
keys.

This is weaker than the linear space bound of Fredman, Komlós and Szemerédi, which also depends
on the choice of a good primary hash function.
-/
public theorem totalSecondarySpace_le_totalKeys_sq
    {table : PerfectHashing α β primaryHash} (hsq : SquareSized table) :
    totalSecondarySpace table ≤ (totalKeys table) ^ 2 := by
  rw [totalSecondarySpace_eq_sum_sq hsq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Nat.zero_le _)

end PerfectHashing

end Cslib.Algorithms.Lean
