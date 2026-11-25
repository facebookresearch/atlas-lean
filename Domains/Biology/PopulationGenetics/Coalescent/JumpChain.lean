/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
public import Mathlib.Data.List.Destutter
import Mathlib.Data.List.OfFn

/-!
# Consistency of Kingman's jump chains

`sum_pathProb_restrict` proves that restricting a full merger path to the first
`n` genes and deleting repeated states preserves the jump-chain law.
-/

@[expose] public section

open Finset

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescentWanted

local notation "SamplePartition " n:arg => Finpartition (univ : Finset (Fin n))

open scoped Classical in
/-- The probability that the jump chain of Kingman's `n`-coalescent, started from the partition
into singletons, follows the list of partitions `l`: `0` unless `l` starts at the partition
into singletons, and otherwise the product of the one-step transition probabilities
`jumpMatrix n` along `l`. The empty list has probability `0`. -/
noncomputable def pathProb (n : ℕ) : List (SamplePartition n) → ℝ
  | [] => 0
  | π :: l => (if π = ⊥ then 1 else 0) *
      (List.zipWith (Finpartition.pairMergeMatrix univ) (π :: l) l).prod

open PartitionCoalescent
open Matrix

variable {n : ℕ}

/-- Expected value of a function of the next `k` states, starting at `π`. -/
private noncomputable def walk :
    ℕ → SamplePartition n → (List (SamplePartition n) → ℝ) → ℝ
  | 0, _, f => f []
  | k + 1, π, f => ∑ q, jumpMatrix n π q * walk k q (fun l => f (q :: l))

/-- The remaining walk, stopped upon reaching one block. -/
private noncomputable def remaining (π : SamplePartition n)
    (f : List (SamplePartition n) → ℝ) : ℝ :=
  walk (#π.parts - 1) π f

private theorem merge_of_jump_ne_zero {π q : SamplePartition n}
    (hπ : 2 ≤ #π.parts) (h : jumpMatrix n π q ≠ 0) : IsMerge π q := by
  by_contra hM
  simp [jumpMatrix, Finpartition.pairMergeMatrix, hπ, hM] at h

private theorem ne_of_merge {π q : SamplePartition n} (h : IsMerge π q) : π ≠ q := by
  rintro rfl
  have := h.2
  omega

/-- Applying the generator at a state is its exit rate times its jump-chain increment. -/
private theorem rate_mulVec (π : SamplePartition n) (g : SamplePartition n → ℝ) :
    (partitionRate n *ᵥ g) π =
      ((#π.parts).choose 2 : ℝ) * ((jumpMatrix n *ᵥ g) π - g π) := by
  have entry (q : SamplePartition n) : partitionRate n π q =
      ((#π.parts).choose 2 : ℝ) * (jumpMatrix n π q - if π = q then 1 else 0) := by
    by_cases hπ : 2 ≤ #π.parts
    · have hc : ((#π.parts).choose 2 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hπ).ne'
      by_cases hm : IsMerge π q
      · simp [partitionRate, jumpMatrix, Finpartition.pairMergeMatrix, hπ, hm, ne_of_merge hm, hc]
      · simp [partitionRate, jumpMatrix, Finpartition.pairMergeMatrix, hπ, hm]
        split <;> simp
    · have hc := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hπ)
      by_cases hm : IsMerge π q
      · have hcard := hm.2
        have hq : q.parts = ∅ := card_eq_zero.mp (by omega)
        have hp := π.parts_eq_empty_iff.mpr (q.parts_eq_empty_iff.mp hq)
        simp [hp, hq] at hcard
      · simp [partitionRate, hm, hc]
  simp only [mulVec_apply_eq_sum, entry, mul_assoc, ← mul_sum, sub_mul, sum_sub_distrib,
    ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

local notation "res" => Finpartition.comap Fin.castSucc

private theorem restrict_mulVec (g : SamplePartition n → ℝ) :
    restrictMatrix n *ᵥ g = fun π => g (res π) := by
  funext π
  simp [mulVec_apply_eq_sum, restrictMatrix, ite_mul]

private theorem rate_restrict (π : SamplePartition (n + 1)) (g : SamplePartition n → ℝ) :
    (partitionRate (n + 1) *ᵥ (fun q => g (res q))) π = (partitionRate n *ᵥ g) (res π) := by
  rw [← restrict_mulVec, mulVec_mulVec, partitionRate_mul_restrictMatrix, ← mulVec_mulVec,
    restrict_mulVec]

/-- The continuation value after a transition, recording the new state only if it changed. -/
private noncomputable def nextValue (π : SamplePartition n)
    (f : List (SamplePartition n) → ℝ) (q : SamplePartition n) : ℝ :=
  if π = q then remaining q f else remaining q (fun l => f (q :: l))

private theorem rate_nextValue (π : SamplePartition n) (f : List (SamplePartition n) → ℝ) :
    (partitionRate n *ᵥ nextValue π f) π = 0 := by
  rw [rate_mulVec]
  by_cases hπ : 2 ≤ #π.parts
  · apply mul_eq_zero_of_right
    apply sub_eq_zero.mpr
    have hk : #π.parts - 1 = (#π.parts - 2) + 1 := by omega
    simp only [nextValue, ite_true, remaining, hk, walk, mulVec_apply_eq_sum]
    apply sum_congr rfl
    intro q _
    by_cases h : jumpMatrix n π q = 0
    · simp [h]
    · have hm := merge_of_jump_ne_zero hπ h
      have hkq : #q.parts - 1 = #π.parts - 2 := by have := hm.2; omega
      simp [ne_of_merge hm, hkq]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hπ)]

/-- The changes in the tail of a list with initial state `a`. -/
private def changes {α : Type*} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | b :: l => if a = b then changes b l else b :: changes b l

private theorem destutter_eq_cons_changes {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    (a :: l).destutter (· ≠ ·) = a :: changes a l := by
  change l.destutter' _ a = _
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    by_cases h : a = b
    · subst b
      simp [changes, ih]
    · simp [changes, h, ih]

/-- Restricting all remaining mergers gives the law of the remaining small-sample walk.
The generator identity transfers the first-step equation through restriction. -/
private theorem walk_restrict (k : ℕ) (π : SamplePartition (n + 1)) (hk : #π.parts = k + 1)
    (f : List (SamplePartition n) → ℝ) :
    walk k π (fun l => f (changes (res π) (l.map res))) = remaining (res π) f := by
  induction k generalizing π f with
  | zero =>
    have hle : #(res π).parts ≤ #π.parts := card_erase_le.trans card_image_le
    have hzero : #(res π).parts - 1 = 0 := by omega
    simp [remaining, hzero, walk, changes]
  | succ k ih =>
    have hπ : 2 ≤ #π.parts := by omega
    have hc : ((#π.parts).choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hπ).ne'
    have hrate := (rate_restrict π (nextValue (res π) f)).trans (rate_nextValue (res π) f)
    rw [rate_mulVec, mul_eq_zero, or_iff_right hc, sub_eq_zero] at hrate
    calc
      _ = ∑ q, jumpMatrix (n + 1) π q * nextValue (res π) f (res q) := by
        rw [walk]
        apply sum_congr rfl
        intro q _
        by_cases h : jumpMatrix (n + 1) π q = 0
        · simp [h]
        · have hm := (merge_of_jump_ne_zero hπ h).2
          have hq : #q.parts = k + 1 := by omega
          congr 1
          by_cases he : res π = res q
          · simpa only [List.map_cons, changes, nextValue, he, ite_true] using ih q hq f
          · simpa only [List.map_cons, changes, nextValue, he, ite_false] using
              ih q hq (fun l => f (res q :: l))
      _ = _ := by simpa [mulVec_apply_eq_sum, nextValue] using hrate

private theorem sum_tuples_succ {α : Type*} [Fintype α] (k : ℕ) (F : List α → ℝ) :
    ∑ p : Fin (k + 1) → α, F (List.ofFn p) =
      ∑ a, ∑ t : Fin k → α, F (a :: List.ofFn t) := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]

private theorem walk_eq_sum (k : ℕ) (π : SamplePartition n) (f : List (SamplePartition n) → ℝ) :
    walk k π f = ∑ t : Fin k → SamplePartition n,
      (List.zipWith (jumpMatrix n) (π :: List.ofFn t) (List.ofFn t)).prod * f (List.ofFn t) := by
  induction k generalizing π f with
  | zero => simp [walk, List.zipWith]
  | succ k ih =>
    rw [walk, sum_tuples_succ k (fun l => (List.zipWith (jumpMatrix n) (π :: l) l).prod * f l)]
    apply sum_congr rfl
    intro q _
    rw [ih, mul_sum]
    apply sum_congr rfl
    intro t _
    exact (mul_assoc _ _ _).symm

private theorem sum_pathProb_apply (k : ℕ) (f : List (SamplePartition n) → ℝ) :
    ∑ p : Fin (k + 1) → SamplePartition n, pathProb n (List.ofFn p) * f (List.ofFn p) =
      walk k ⊥ (fun l => f (⊥ :: l)) := by
  rw [sum_tuples_succ k (fun l => pathProb n l * f l), walk_eq_sum]
  simp [pathProb, jumpMatrix, ite_mul, sum_ite_eq']

private theorem restrict_bot : res (⊥ : SamplePartition (n + 1)) = ⊥ := by
  apply le_bot_iff.mp
  intro B hB
  obtain ⟨⟨a, ha⟩, C, hC, rfl⟩ := Finpartition.mem_comap_parts.mp hB
  obtain ⟨x, _, rfl⟩ := Finpartition.mem_bot_iff.mp hC
  have hx : a.castSucc = x := mem_singleton.mp (mem_filter.mp ha).2
  subst x
  exact ⟨{a}, Finpartition.mem_bot_iff.mpr ⟨a, mem_univ a, rfl⟩,
    fun b hb => by simpa using (mem_filter.mp hb).2⟩

private theorem pathProb_eq_sum (k : ℕ) (l : List (SamplePartition n)) (hl : l.length = k + 1) :
    pathProb n l = ∑ p : Fin (k + 1) → SamplePartition n,
      pathProb n (List.ofFn p) * (if List.ofFn p = l then 1 else 0) := by
  obtain ⟨t, rfl⟩ : ∃ t : Fin (k + 1) → SamplePartition n, List.ofFn t = l := by
    rw [← hl]
    exact ⟨l.get, List.ofFn_get _⟩
  simp only [List.ofFn_inj, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]

open scoped Classical in
/-- **Consistency of the jump chains** (Kingman 1982): for `n ≥ 1`, restricting each
partition of a path of the `(n + 1)`-jump chain (a list of `n + 1` partitions) to the first `n`
genes and deleting consecutive repetitions gives a list of `n` partitions of `Fin n` distributed
as the path of the `n`-jump chain.

Source: Kingman (1982); Durrett (2008), ch. 1. -/
theorem sum_pathProb_restrict (n : ℕ) (hn : 1 ≤ n) (ρs : List (SamplePartition n))
    (hρs : ρs.length = n) :
    ∑ p : Fin (n + 1) → SamplePartition (n + 1)
        with ((List.ofFn p).map (Finpartition.comap Fin.castSucc)).destutter (· ≠ ·) = ρs,
      pathProb (n + 1) (List.ofFn p) = pathProb n ρs := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let event (l : List (SamplePartition (k + 1))) : ℝ := if l = ρs then 1 else 0
  have hbot : #(⊥ : SamplePartition (k + 1 + 1)).parts = k + 1 + 1 := by simp
  rw [sum_filter]
  calc
    _ = walk (k + 1) ⊥ (fun l => event (((⊥ :: l).map res).destutter (· ≠ ·))) := by
      simpa [event, mul_ite] using sum_pathProb_apply (n := k + 1 + 1) (k + 1)
        (fun l => event ((l.map res).destutter (· ≠ ·)))
    _ = remaining (⊥ : SamplePartition (k + 1)) (fun l => event (⊥ :: l)) := by
      simpa only [List.map_cons, destutter_eq_cons_changes, restrict_bot] using
        walk_restrict (k + 1) ⊥ hbot (fun l => event (res (⊥ : SamplePartition (k + 1 + 1)) :: l))
    _ = pathProb (k + 1) ρs := by
      rw [pathProb_eq_sum k ρs hρs]
      simpa [remaining, Finpartition.card_bot, event] using (sum_pathProb_apply k event).symm

end MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescentWanted
