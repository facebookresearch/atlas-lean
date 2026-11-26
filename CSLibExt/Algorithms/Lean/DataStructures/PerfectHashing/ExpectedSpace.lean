/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PerfectHashing
public import Mathlib.Analysis.SpecificLimits.Basic

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expected space of two-level perfect hashing

A uniformly sampled primary hash sends a static finite key set into as many buckets as there
are keys. A bucket with `k` keys gets `2 k²` slots and uses independent uniform draws to find
an injective secondary hash. We count allocated cells and lookup probes, not running time.

## References

* J. Erickson, *Algorithms*, Lecture 5: Hash Tables, §§5.6–5.7 (Spring 2017).
  <https://jeffe.cs.illinois.edu/teaching/algorithms/notes/05-hashing.pdf>
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

open Finset

universe u v w

namespace UniversalHashing

/-- **Indexed near-universal hash family.** A finite indexed family into $m > 0$ slots is
near-universal if its index set is nonempty and, for any distinct keys, at most a $2/m$ fraction
of its indices give a collision. Each index has equal weight even if several indices induce the
same function. The bound is written by cross multiplication, without natural-number division. -/
@[expose]
def IsNearUniversalOn {α : Type u} {ι : Type v} {m : ℕ}
    (sample : Finset ι) (h : ι → α → Fin m) : Prop :=
  0 < m ∧ sample.Nonempty ∧
    ∀ x y, x ≠ y → (sample.filter fun a => h a x = h a y).card * m ≤ 2 * sample.card

end UniversalHashing

namespace PerfectHashing

open UniversalHashing (IsNearUniversalOn)

variable {α : Type u} {ι : Type v} {m : ℕ}

/-- **Keys assigned to a hash bucket.** Given a finite key set and a hash into $m$ buckets,
the keys assigned to bucket $j$ are exactly the members of the set that hash to $j$. -/
@[expose]
def bucketKeys (keys : Finset α) (h : α → Fin m) (j : Fin m) : Finset α :=
  keys.filter fun x => h x = j

private def orderedCollisions [DecidableEq α] (keys : Finset α) (h : α → Fin m) : ℕ :=
  (keys.offDiag.filter fun xy => h xy.1 = h xy.2).card

private theorem orderedCollisions_eq_sum [DecidableEq α] (keys : Finset α) (h : α → Fin m) :
    orderedCollisions keys h =
      ∑ j, (bucketKeys keys h j).card * ((bucketKeys keys h j).card - 1) := by
  unfold orderedCollisions
  rw [card_eq_sum_card_fiberwise (f := fun xy : α × α => h xy.1) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun j _ => ?_
  have hfiber : ((keys.offDiag.filter fun xy => h xy.1 = h xy.2).filter
      fun xy => h xy.1 = j) = (bucketKeys keys h j).offDiag := by
    ext xy
    simp only [bucketKeys, mem_filter, mem_offDiag]
    constructor
    · rintro ⟨⟨⟨hx, hy, hne⟩, hxy⟩, hj⟩
      exact ⟨⟨hx, hj⟩, ⟨hy, hxy.symm.trans hj⟩, hne⟩
    · rintro ⟨⟨hx, hj⟩, ⟨hy, h'⟩, hne⟩
      exact ⟨⟨⟨hx, hy, hne⟩, hj.trans h'.symm⟩, hj⟩
  rw [hfiber, offDiag_card, Nat.mul_sub_one]

private theorem sum_bucketSq_eq [DecidableEq α] (keys : Finset α) (h : α → Fin m) :
    (∑ j, (bucketKeys keys h j).card ^ 2) = keys.card + orderedCollisions keys h := by
  have hsum : (∑ j, (bucketKeys keys h j).card) = keys.card :=
    (card_eq_sum_card_fiberwise (f := h) (t := univ) (fun _ _ => mem_univ _)).symm
  have hsq (k : ℕ) : k ^ 2 = k + k * (k - 1) := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  simp_rw [hsq]
  rw [sum_add_distrib, hsum, orderedCollisions_eq_sum]

private theorem sum_orderedCollisions_mul_le [DecidableEq α]
    (keys : Finset α) {sample : Finset ι} {h : ι → α → Fin m}
    (near : IsNearUniversalOn sample h) :
    (∑ a ∈ sample, orderedCollisions keys (h a)) * m ≤
      2 * sample.card * (keys.card * (keys.card - 1)) := by
  have hswap : (∑ a ∈ sample, orderedCollisions keys (h a)) =
      ∑ xy ∈ keys.offDiag, (sample.filter fun a => h a xy.1 = h a xy.2).card := by
    simp only [orderedCollisions, card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [hswap, sum_mul]
  calc
    _ ≤ ∑ _xy ∈ keys.offDiag, 2 * sample.card :=
      sum_le_sum fun xy hxy => near.2.2 xy.1 xy.2 (mem_offDiag.mp hxy).2.2
    _ = _ := by rw [sum_const, smul_eq_mul, offDiag_card, Nat.mul_sub_one, Nat.mul_comm]

private theorem mean_bucketSq_le (keys : Finset α) {sample : Finset ι}
    {h : ι → α → Fin keys.card} (near : IsNearUniversalOn sample h) :
    (∑ a ∈ sample, ∑ j, ((bucketKeys keys (h a) j).card : ℚ) ^ 2) / sample.card ≤
      3 * (keys.card : ℚ) - 2 := by
  classical
  have hn : (0 : ℚ) < keys.card := by exact_mod_cast near.1
  have hs : (0 : ℚ) < sample.card := by exact_mod_cast near.2.1.card_pos
  have hbound : (∑ a ∈ sample, (orderedCollisions keys (h a) : ℚ)) * keys.card ≤
      2 * (sample.card : ℚ) * ((keys.card : ℚ) * ((keys.card : ℚ) - 1)) := by
    have hnat := sum_orderedCollisions_mul_le keys near
    have hcast := Nat.cast_le (α := ℚ).2 hnat
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub (Nat.one_le_of_lt near.1)] using hcast
  have hmean : (∑ a ∈ sample, (orderedCollisions keys (h a) : ℚ)) ≤
      2 * (sample.card : ℚ) * ((keys.card : ℚ) - 1) := by
    apply le_of_mul_le_mul_right _ hn
    calc
      _ ≤ 2 * (sample.card : ℚ) * ((keys.card : ℚ) * ((keys.card : ℚ) - 1)) := hbound
      _ = _ := by ring
  have hsq (a : ι) : (∑ j, ((bucketKeys keys (h a) j).card : ℚ) ^ 2) =
      (keys.card : ℚ) + orderedCollisions keys (h a) := by
    exact_mod_cast sum_bucketSq_eq keys (h a)
  simp_rw [hsq]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, div_le_iff₀ hs]
  linarith only [hmean]

private theorem two_le_orderedCollisions [DecidableEq α] (keys : Finset α)
    (h : α → Fin m) (hbad : ¬ Set.InjOn h (keys : Set α)) : 2 ≤ orderedCollisions keys h := by
  unfold Set.InjOn at hbad
  push Not at hbad
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hbad
  have hpair : (x, y) ≠ (y, x) := fun e => hne (congrArg Prod.fst e)
  have hsub : {(x, y), (y, x)} ⊆ keys.offDiag.filter (fun xy => h xy.1 = h xy.2) := by
    intro xy hmem
    rcases mem_insert.mp hmem with rfl | hmem
    · exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hx, hy, hne⟩, hxy⟩
    · rw [mem_singleton.mp hmem]
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hy, hx, hne.symm⟩, hxy.symm⟩
  simpa only [orderedCollisions, card_pair hpair] using card_le_card hsub

open scoped Classical in
private theorem failureFraction_lt_half (keys : Finset α) {sample : Finset ι}
    {h : ι → α → Fin (2 * keys.card ^ 2)} (hk : keys.Nonempty)
    (near : IsNearUniversalOn sample h) :
    ((sample.filter fun a => ¬ Set.InjOn (h a) (keys : Set α)).card : ℚ) / sample.card <
      1 / 2 := by
  classical
  let bad := sample.filter fun a => ¬ Set.InjOn (h a) (keys : Set α)
  have hbad : 2 * bad.card ≤ ∑ a ∈ sample, orderedCollisions keys (h a) := by
    calc
      _ = ∑ a ∈ bad, (2 : ℕ) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := by
        rw [sum_filter]
        apply sum_le_sum
        intro a _
        split_ifs with ha
        · exact Nat.zero_le _
        · exact two_le_orderedCollisions keys (h a) ha
  have hn : (0 : ℚ) < keys.card := by exact_mod_cast hk.card_pos
  have hs : (0 : ℚ) < sample.card := by exact_mod_cast near.2.1.card_pos
  have hcount := (Nat.mul_le_mul_right (2 * keys.card ^ 2) hbad).trans
    (sum_orderedCollisions_mul_le keys near)
  have hcast : (2 * (bad.card : ℚ)) * (2 * (keys.card : ℚ) ^ 2) ≤
      2 * (sample.card : ℚ) * ((keys.card : ℚ) * ((keys.card : ℚ) - 1)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_sub (Nat.one_le_of_lt hk.card_pos)] using (Nat.cast_le (α := ℚ)).2 hcount
  have hcancel : 2 * (bad.card : ℚ) * keys.card ≤ (sample.card : ℚ) * (keys.card - 1) := by
    apply le_of_mul_le_mul_right _ (show (0 : ℚ) < 2 * keys.card by positivity)
    calc
      _ = (2 * (bad.card : ℚ)) * (2 * (keys.card : ℚ) ^ 2) := by ring
      _ ≤ 2 * (sample.card : ℚ) * ((keys.card : ℚ) * ((keys.card : ℚ) - 1)) := hcast
      _ = _ := by ring
  have hlt : 2 * (bad.card : ℚ) * keys.card < (sample.card : ℚ) * keys.card :=
    hcancel.trans_lt (by linarith only [hs])
  apply (div_lt_iff₀ hs).2
  have htwo := lt_of_mul_lt_mul_right hlt hn.le
  linarith only [htwo]

/-- **Tail of secondary-hash sampling.** For a nonempty finite set of $k$ keys, draw from a
finite indexed family of hashes into $2k^2$ slots. If $q$ is the fraction of family indices whose
hash is not injective on the keys, the chance of still needing a draw after $t$ independent
uniform draws with replacement is $q^t$. The fraction is computed in the rationals (with Lean's
zero denominator convention if given an empty index set, which is not a sampling distribution).
For an empty key set the procedure makes no draws and the tail is zero for every $t$, including
$t=0$; no secondary hash is needed for that branch. -/
noncomputable def secondaryAttemptTail (keys : Finset α) (sample : Finset ι)
    (h : keys.Nonempty → ι → α → Fin (2 * keys.card ^ 2)) (t : ℕ) : ℚ := by
  classical
  exact if hk : keys.Nonempty then
    (((sample.filter fun a => ¬ Set.InjOn (h hk a) (keys : Set α)).card : ℚ) / sample.card) ^ t
    else 0

open scoped Classical in
/-- **Success probability and expected draws for a secondary hash.** Suppose that for a
nonempty bucket of $k$ distinct keys the finite indexed family into $2k^2$ slots is near-universal.
There is an injective choice and the failure fraction $q$ is strictly below $1/2$. For every
$t$, the sampling tail is the fraction of length-$t$ strings of indices all of whose hashes
fail, out of all length-$t$ strings, as appropriate for independent uniform draws with replacement.
The real sum of the tails (expected number of draws, including the first) equals $1/(1-q)$ and
is strictly below $2$. For an empty bucket the expected number is zero, with no family assumption;
for a singleton it is one. -/
theorem secondary_sampling (keys : Finset α) (sample : Finset ι)
    (h : keys.Nonempty → ι → α → Fin (2 * keys.card ^ 2))
    (near : ∀ hk, IsNearUniversalOn sample (h hk)) :
    (∀ hk : keys.Nonempty,
      (∃ a ∈ sample, Set.InjOn (h hk a) (keys : Set α)) ∧
      secondaryAttemptTail keys sample h 1 < 1 / 2 ∧
      ∀ t, secondaryAttemptTail keys sample h t =
        (Fintype.card (Fin t → ↥(sample.filter fun a => ¬ Set.InjOn (h hk a) (keys : Set α))) : ℚ) /
          Fintype.card (Fin t → ↥sample)) ∧
    ∃ draws : ℝ, HasSum (fun t => (secondaryAttemptTail keys sample h t : ℝ)) draws ∧
      draws < 2 ∧ (¬ keys.Nonempty → draws = 0) ∧
      (∀ _hk : keys.Nonempty, draws = (1 - (secondaryAttemptTail keys sample h 1 : ℝ))⁻¹) ∧
      (keys.card = 1 → draws = 1) := by
  classical
  by_cases hk : keys.Nonempty
  · let bad := sample.filter fun a => ¬ Set.InjOn (h hk a) (keys : Set α)
    let q : ℚ := (bad.card : ℚ) / sample.card
    have htail (t : ℕ) : secondaryAttemptTail keys sample h t = q ^ t := by
      simp only [secondaryAttemptTail, dite_eq_left hk, q, bad]
    have hq : q < 1 / 2 := failureFraction_lt_half keys hk (near hk)
    have hs : (0 : ℚ) < sample.card := by exact_mod_cast (near hk).2.1.card_pos
    refine ⟨fun _ => ⟨?_, by simpa only [htail, pow_one] using hq, ?_⟩, ?_⟩
    · by_contra! hnone
      have heq : bad = sample := filter_eq_self.mpr fun a ha => hnone a ha
      have hqone : q = 1 := by simp [q, heq, hs.ne']
      rw [hqone] at hq
      norm_num at hq
    · intro t
      rw [htail]
      simp [q, bad, div_pow]
    · have hr : (q : ℝ) < 1 / 2 := by
        have hcast : (q : ℝ) < ((1 / 2 : ℚ) : ℝ) := Rat.cast_lt.mpr hq
        simpa using hcast
      have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) hs.le
      have hr0 : (0 : ℝ) ≤ q := by exact_mod_cast hq0
      refine ⟨(1 - (q : ℝ))⁻¹, ?_, ?_, fun hn => (hn hk).elim, ?_, ?_⟩
      · simpa only [htail, Rat.cast_pow] using
          hasSum_geometric_of_lt_one hr0 (by linarith only [hr])
      · simpa using (one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 / 2 by norm_num)
          (show 1 / 2 < 1 - (q : ℝ) by linarith only [hr]))
      · intro _
        rw [htail, pow_one]
      · intro hone
        have hinj (a : ι) : Set.InjOn (h hk a) (keys : Set α) := by
          intro x hx y hy _
          exact card_le_one.mp hone.le x hx y hy
        simp [q, bad, hinj]
  · refine ⟨fun hne => (hk hne).elim, 0, ?_, by norm_num, fun _ => rfl,
      fun hne => (hk hne).elim, ?_⟩
    · simp [secondaryAttemptTail, hk]
    · simp [not_nonempty_iff_eq_empty.mp hk]

section Table

variable {β : Type w}

private noncomputable def bucketCell (keys : Finset α) (values : α → β)
    (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ) (j : Fin keys.card)
    (slot : Fin (2 * (bucketKeys keys h j).card ^ 2)) : Option (α × β) := by
  classical
  exact if hex : ∃ x ∈ bucketKeys keys h j, g j x % (2 * (bucketKeys keys h j).card ^ 2) = ↑slot
    then some (hex.choose, values hex.choose) else none

/-- **Two-level layout with doubled square sizing.** For a nonempty finite key set of size $n$,
a value for each key, a primary hash into $n$ buckets, and a natural-valued secondary hash per
bucket, allocate $2k^2$ slots for a bucket assigned $k$ keys. A slot holds a binding chosen
from the keys assigned to that bucket whose secondary hash reduces to that slot modulo the
bucket's capacity; a slot with no such key is vacant. In particular an empty bucket has no
secondary slots. The choice describes the table, not an implementation of its construction. -/
noncomputable def ofBucketHashes (keys : Finset α) (values : α → β) (hn : 0 < keys.card)
    (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ) :
    PerfectHashing α β (fun x => (h x).val) where
  bucketCount := keys.card
  bucketCount_pos := hn
  secondarySize j := 2 * (bucketKeys keys h j).card ^ 2
  secondaryHash := g
  secondaryTable j := Vector.ofFn (bucketCell keys values h g j)

private theorem ofBucketHashes_get (keys : Finset α) (values : α → β) (hn : 0 < keys.card)
    (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ)
    (j : Fin (ofBucketHashes keys values hn h g).bucketCount)
    (slot : Fin ((ofBucketHashes keys values hn h g).secondarySize j)) :
    ((ofBucketHashes keys values hn h g).secondaryTable j).get slot =
      bucketCell keys values h g j slot :=
  Vector.getElem_ofFn (f := bucketCell keys values h g j) slot.isLt

private theorem bucketCell_eq_some_imp (keys : Finset α) (values : α → β)
    (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ) (j : Fin keys.card)
    (slot : Fin (2 * (bucketKeys keys h j).card ^ 2)) {x : α} {v : β}
    (hslot : bucketCell keys values h g j slot = some (x, v)) :
    x ∈ bucketKeys keys h j ∧ g j x % (2 * (bucketKeys keys h j).card ^ 2) = ↑slot ∧
      v = values x := by
  unfold bucketCell at hslot
  split at hslot
  · next hex =>
      obtain ⟨hx, hv⟩ := Prod.mk.inj (Option.some.inj hslot)
      subst x
      subst v
      exact ⟨hex.choose_spec.1, hex.choose_spec.2, rfl⟩
  · simp at hslot

private theorem ofBucketHashes_valid (keys : Finset α) (values : α → β) (hn : 0 < keys.card)
    (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ) :
    (ofBucketHashes keys values hn h g).Valid := by
  apply Valid.mk_of_placed
  intro j slot x v hget
  rw [ofBucketHashes_get keys values hn h g] at hget
  obtain ⟨hx, hslot, _⟩ := bucketCell_eq_some_imp keys values h g j slot hget
  refine ⟨?_, hslot.symm⟩
  apply Fin.ext
  change (h x).val % keys.card = j.val
  rw [Nat.mod_eq_of_lt (h x).isLt]
  simp only [bucketKeys, mem_filter] at hx
  exact congrArg Fin.val hx.2

private theorem ofBucketHashes_stored_iff (keys : Finset α) (values : α → β) (hn : 0 < keys.card)
    (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ)
    (hinj : ∀ j, Set.InjOn (fun x => g j x % (2 * (bucketKeys keys h j).card ^ 2))
      (bucketKeys keys h j : Set α)) (x : α) (v : β) :
    (ofBucketHashes keys values hn h g).Stored x v ↔ x ∈ keys ∧ v = values x := by
  constructor
  · rintro ⟨j, slot, hget⟩
    rw [ofBucketHashes_get keys values hn h g] at hget
    obtain ⟨hx, _, hv⟩ := bucketCell_eq_some_imp keys values h g j slot hget
    simp only [bucketKeys, mem_filter] at hx
    exact ⟨hx.1, hv⟩
  · rintro ⟨hx, rfl⟩
    let j := h x
    have hmem : x ∈ bucketKeys keys h j := mem_filter.mpr ⟨hx, rfl⟩
    have hpos : 0 < 2 * (bucketKeys keys h j).card ^ 2 := by
      have : 0 < (bucketKeys keys h j).card := Nonempty.card_pos ⟨x, hmem⟩
      positivity
    let slot : Fin (2 * (bucketKeys keys h j).card ^ 2) :=
      ⟨g j x % _, Nat.mod_lt _ hpos⟩
    refine ⟨j, slot, (ofBucketHashes_get keys values hn h g j slot).trans ?_⟩
    unfold bucketCell
    split
    · next hex =>
        have hx' := hinj j hex.choose_spec.1 hmem hex.choose_spec.2
        rw [hx']
    · next hnone => exact (hnone ⟨x, hmem, rfl⟩).elim

/-- **Lookup with a cell-probe count.** Probe the primary bucket descriptor and, only if its
secondary capacity is positive, the one secondary slot selected by its hash. Return the value
exactly if that slot holds a binding with the query key, and return no value otherwise. The
second component counts one probe for a zero-capacity bucket and two for any other bucket.
Hash computation and key comparison are not charged as cell probes. -/
@[expose]
def lookupWithProbes [DecidableEq α] {primaryHash : α → ℕ} (key : α)
    (table : PerfectHashing α β primaryHash) : Option β × ℕ :=
  let j : Fin table.bucketCount :=
    ⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩
  if hs : 0 < table.secondarySize j then
    let binding := (table.secondaryTable j).get
      ⟨table.secondaryHash j key % table.secondarySize j, Nat.mod_lt _ hs⟩
    (match binding with
      | some (storedKey, v) => if storedKey = key then some v else none
      | none => none, 2)
  else (none, 1)

/-- **The result and probe bound of perfect-hash lookup.** For any two-level table, the lookup
with probes gives the same result as ordinary lookup. It probes one primary descriptor and at
most one secondary cell: one probe and no result when the selected bucket has zero capacity,
and two probes when its capacity is positive. This statement does not require table validity. -/
theorem lookupWithProbes_spec [DecidableEq α] {primaryHash : α → ℕ}
    (key : α) (table : PerfectHashing α β primaryHash) :
    let j : Fin table.bucketCount :=
      ⟨primaryHash key % table.bucketCount, Nat.mod_lt _ table.bucketCount_pos⟩
    (lookupWithProbes key table).1 = lookup key table ∧
      (lookupWithProbes key table).2 = (if 0 < table.secondarySize j then 2 else 1) ∧
      (lookupWithProbes key table).2 ≤ 2 ∧
      (table.secondarySize j = 0 → lookupWithProbes key table = (none, 1)) := by
  dsimp only [lookupWithProbes, lookup]
  split_ifs with h <;> simp_all [ne_of_gt]
  split <;> simp_all

private theorem ofBucketHashes_lookup [DecidableEq α] (keys : Finset α) (values : α → β)
    (hn : 0 < keys.card) (h : α → Fin keys.card) (g : Fin keys.card → α → ℕ)
    (hinj : ∀ j, Set.InjOn (fun x => g j x % (2 * (bucketKeys keys h j).card ^ 2))
      (bucketKeys keys h j : Set α)) (x : α) :
    lookupWithProbes x (ofBucketHashes keys values hn h g) =
      (if x ∈ keys then some (values x) else none,
        if (bucketKeys keys h (h x)).Nonempty then 2 else 1) := by
  let table := ofBucketHashes keys values hn h g
  have hv : table.Valid := ofBucketHashes_valid keys values hn h g
  have hlookup : lookup x table = if x ∈ keys then some (values x) else none := by
    split_ifs with hx
    · exact lookup_eq_some_of_stored hv
        ((ofBucketHashes_stored_iff keys values hn h g hinj x (values x)).2 ⟨hx, rfl⟩)
    · exact (lookup_eq_none_iff hv x).2 fun v hstored =>
        hx ((ofBucketHashes_stored_iff keys values hn h g hinj x v).1 hstored).1
  have hprobes := lookupWithProbes_spec x table
  apply Prod.ext
  · exact hprobes.1.trans hlookup
  · refine hprobes.2.1.trans ?_
    let j : Fin keys.card := ⟨(h x).val % keys.card, Nat.mod_lt _ hn⟩
    have hj : j = h x := Fin.ext (Nat.mod_eq_of_lt (h x).isLt)
    refine (congrArg (fun i => if 0 < 2 * (bucketKeys keys h i).card ^ 2 then 2 else 1) hj).trans ?_
    change (if 0 < 2 * (bucketKeys keys h (h x)).card ^ 2 then 2 else 1) =
      if (bucketKeys keys h (h x)).Nonempty then 2 else 1
    by_cases hk : (bucketKeys keys h (h x)).Nonempty
    · have hpos := hk.card_pos
      rw [ite_eq_left (by positivity), ite_eq_left hk]
    · simp [not_nonempty_iff_eq_empty.mp hk]

/-- **Two-level perfect hashing uses linear expected space.** Fix a nonempty finite set of $n$
keys with values, and choose a primary index uniformly from a finite near-universal family into
$n$ buckets. Suppose each nonempty bucket, conditional on the primary index, has a finite
near-universal secondary family into $2k^2$ slots, where $k$ is its occupancy. One can select an
injective member of each such family and build valid two-level tables with $n$ primary descriptors
and $2k^2$ secondary cells per bucket. The rational mean of the sum of squared occupancies is at
most $3n-2$, and the rational mean of the actual total allocated cell count is at most $7n-4$.
For every primary choice and every query, ordinary lookup returns its value if it belongs to the
key set and nothing otherwise. Lookup with probes gives the same result and counts one primary
probe and one additional secondary probe exactly when the selected bucket is nonempty. -/
theorem two_level_expected_space [DecidableEq α] {κ : Type*}
    (keys : Finset α) (values : α → β) {sample : Finset ι} {h : ι → α → Fin keys.card}
    (near : IsNearUniversalOn sample h) (secondarySample : ι → Fin keys.card → Finset κ)
    (g : ∀ a j, (bucketKeys keys (h a) j).Nonempty → κ → α →
      Fin (2 * (bucketKeys keys (h a) j).card ^ 2))
    (secondaryNear : ∀ a ∈ sample, ∀ j hk, IsNearUniversalOn (secondarySample a j) (g a j hk)) :
    ∃ selected : ι → Fin keys.card → α → ℕ,
      (∀ a ∈ sample, ∀ j hk, ∃ b ∈ secondarySample a j,
        Set.InjOn (g a j hk b) (bucketKeys keys (h a) j : Set α) ∧
          selected a j = fun x => (g a j hk b x).val) ∧
      (∑ a ∈ sample, ∑ j, ((bucketKeys keys (h a) j).card : ℚ) ^ 2) / sample.card ≤
        3 * (keys.card : ℚ) - 2 ∧
      let table a := ofBucketHashes keys values near.1 (h a) (selected a)
      (∑ a ∈ sample, (((table a).bucketCount + (table a).totalSecondarySpace : ℕ) : ℚ)) /
          sample.card ≤ 7 * (keys.card : ℚ) - 4 ∧
      ∀ a ∈ sample, (table a).Valid ∧ ∀ x,
        lookup x (table a) = (if x ∈ keys then some (values x) else none) ∧
          lookupWithProbes x (table a) =
            (if x ∈ keys then some (values x) else none,
              if (bucketKeys keys (h a) (h a x)).Nonempty then 2 else 1) := by
  classical
  have hex a (ha : a ∈ sample) j hk :=
    (secondary_sampling (bucketKeys keys (h a) j) (secondarySample a j) (g a j)
      (secondaryNear a ha j)).1 hk |>.1
  let selected a j : α → ℕ :=
    if ha : a ∈ sample then
      if hk : (bucketKeys keys (h a) j).Nonempty then
        fun x => (g a j hk (hex a ha j hk).choose x).val
      else fun _ => 0
    else fun _ => 0
  have hselected (a : ι) (ha : a ∈ sample) (j : Fin keys.card)
      (hk : (bucketKeys keys (h a) j).Nonempty) :
      ∃ b ∈ secondarySample a j, Set.InjOn (g a j hk b) (bucketKeys keys (h a) j : Set α) ∧
        selected a j = fun x => (g a j hk b x).val := by
    exact ⟨_, (hex a ha j hk).choose_spec.1, (hex a ha j hk).choose_spec.2,
      by simp only [selected, dite_eq_left ha, dite_eq_left hk]⟩
  have hmean := mean_bucketSq_le keys near
  refine ⟨selected, hselected, hmean, ?_, ?_⟩
  · have hs : (0 : ℚ) < sample.card := by exact_mod_cast near.2.1.card_pos
    have hcells a : (((ofBucketHashes keys values near.1 (h a) (selected a)).bucketCount +
        (ofBucketHashes keys values near.1 (h a) (selected a)).totalSecondarySpace : ℕ) : ℚ) =
        (keys.card : ℚ) + 2 * (∑ j, ((bucketKeys keys (h a) j).card : ℚ) ^ 2) := by
      change ((keys.card + ∑ j, 2 * (bucketKeys keys (h a) j).card ^ 2 : ℕ) : ℚ) = _
      push_cast
      rw [mul_sum]
    simp_rw [hcells]
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, div_le_iff₀ hs]
    have hbound := (div_le_iff₀ hs).mp hmean
    linarith only [hbound]
  · intro a ha
    have hinj (j : Fin keys.card) :
        Set.InjOn (fun x => selected a j x % (2 * (bucketKeys keys (h a) j).card ^ 2))
          (bucketKeys keys (h a) j : Set α) := by
      intro x hx y hy hxy
      obtain ⟨b, _, hb, hg⟩ := hselected a ha j ⟨x, hx⟩
      change selected a j x % _ = selected a j y % _ at hxy
      rw [hg, Nat.mod_eq_of_lt (g a j ⟨x, hx⟩ b x).isLt,
        Nat.mod_eq_of_lt (g a j ⟨x, hx⟩ b y).isLt] at hxy
      exact hb hx hy (Fin.ext hxy)
    refine ⟨ofBucketHashes_valid keys values near.1 (h a) (selected a), fun x => ?_⟩
    have hp := ofBucketHashes_lookup keys values near.1 (h a) (selected a) hinj x
    have hs := lookupWithProbes_spec x (ofBucketHashes keys values near.1 (h a) (selected a))
    exact ⟨hs.1.symm.trans (congrArg Prod.fst hp), hp⟩

end Table

end PerfectHashing

end Cslib.Algorithms.Lean
