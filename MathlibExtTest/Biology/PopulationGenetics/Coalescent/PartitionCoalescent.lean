/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent

/-!
# Tests for Kingman's partition-valued coalescent

Kingman's formula on concrete partitions (`1/3` for each two-block partition of three genes,
probability one for the singletons at the start and the one-block partition after `n - 1`
jumps), exchangeability on a relabeled partition, the boundary sample sizes `n = 0, 1`, the
absorbing behavior outside the range `m < n` of `jumpLaw_eq`, and the time-`t` marginal of a
sample of two (`P(one block at time t) = 1 - e^{-t}`), normalization, and consistency.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.PartitionCoalescent

open MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-- The partition `{{0, 1}, {2}}` of three genes. -/
def π₁ : SamplePartition 3 :=
  @Finpartition.ofSetoid _ _ _ (Setoid.ker ![(0 : Fin 2), 0, 1])
    (fun _ _ => inferInstanceAs (Decidable (_ = _)))

/-- `{{0, 1}, {2}}` has two blocks, of sizes `2` and `1`. -/
example : #π₁.parts = 2 ∧ π₁.cardProd Nat.factorial = 2 := by
  decide

/-- **Kingman's formula** for three genes: after one coalescence the partition `{{0, 1}, {2}}`
has probability `1! 2! 1! · 2! 1! / (3! 2!) = 1/3`. -/
example : jumpLaw 3 1 π₁ = 1 / 3 := by
  have h : #π₁.parts = 2 ∧ π₁.cardProd Nat.factorial = 2 := by decide
  rw [jumpLaw_eq (by norm_num), ite_eq_left (by rw [h.1]), kingmanProb, h.1, h.2]
  norm_num [Nat.factorial]

/-- **Exchangeability**: relabeling `{{0, 1}, {2}}` by the transposition of `1` and `2` gives
`{{0, 2}, {1}}`, a different partition with the same probability `1/3`. -/
example : π₁.comap (Equiv.swap (1 : Fin 3) 2) ≠ π₁ ∧
    jumpLaw 3 1 (π₁.comap (Equiv.swap (1 : Fin 3) 2)) = 1 / 3 := by
  refine ⟨by decide, ?_⟩
  have h : #π₁.parts = 2 ∧ π₁.cardProd Nat.factorial = 2 := by decide
  rw [jumpLaw_comap_perm (by norm_num), jumpLaw_eq (by norm_num), ite_eq_left (by rw [h.1]),
    kingmanProb, h.1, h.2]
  norm_num [Nat.factorial]

/-- After `n - 1 = 3` coalescences a sample of four genes is in one block with probability one. -/
example : jumpLaw 4 3 ⊤ = 1 := by
  have h : #(⊤ : SamplePartition 4).parts = 1 ∧
      (⊤ : SamplePartition 4).cardProd Nat.factorial = 24 := by decide
  rw [jumpLaw_eq (by norm_num), ite_eq_left (by rw [h.1]), kingmanProb, h.1, h.2]
  norm_num [Nat.factorial]

/-- At the start the chain is at the partition into singletons. -/
example : jumpLaw 5 0 ⊥ = 1 := by
  rw [jumpLaw_eq (by norm_num), ite_eq_left (by simp), kingmanProb_bot]

/-- A partition with two blocks has probability `0` after two coalescences of three genes. -/
example : jumpLaw 3 2 π₁ = 0 := by
  have h : #π₁.parts = 2 := by decide
  rw [jumpLaw_eq (by norm_num), ite_eq_right (by rw [h]; norm_num)]

/-- Outside the range `m < n` of `jumpLaw_eq` the chain has been absorbed: one gene stays in its
single block forever (`jumpLaw 1 1 ⊥ = 1`), although the block-count condition
`#⊥.parts + 1 = 1` of Kingman's formula fails. -/
example : jumpLaw 1 1 ⊥ = 1 ∧ ¬ (#(⊥ : SamplePartition 1).parts + 1 = 1) := by
  refine ⟨?_, by simp⟩
  simp [jumpLaw, jumpMatrix]

/-- Boundary case `n = 0`: the empty sample has the single (empty) partition, with Kingman
probability one and time-`t` probability one. -/
example (t : ℝ) : kingmanProb 0 ⊥ = 1 ∧ timeLaw 0 t ⊥ = 1 := by
  refine ⟨kingmanProb_bot, ?_⟩
  rw [timeLaw_eq, kingmanProb_bot, mul_one]
  have : blockCountingGenerator 0 = 0 := by
    ext i j
    fin_cases i; fin_cases j
    simp [blockCountingGenerator]
  rw [this, smul_zero, NormedSpace.exp_zero]
  rfl

/-- At time `0` the coalescent is at the partition into singletons. -/
example (π : SamplePartition 3) : timeLaw 3 0 π = if ⊥ = π then 1 else 0 := by
  rw [timeLaw, zero_smul, NormedSpace.exp_zero, Matrix.one_apply]

/-- **Two genes**: they have coalesced by time `t` with probability `1 - e^{-t}` (the coalescence
time is exponential with rate `1`), and are still apart with probability `e^{-t}`. -/
example (t : ℝ) : timeLaw 2 t ⊤ = 1 - Real.exp (-t) ∧ timeLaw 2 t ⊥ = Real.exp (-t) := by
  have h : #(⊤ : SamplePartition 2).parts = 1 ∧
      (⊤ : SamplePartition 2).cardProd Nat.factorial = 2 := by decide
  constructor
  · rw [timeLaw_eq_tavareProb (by norm_num), kingmanProb, h.1, h.2]
    norm_num [tavareProb, Finset.sum_Icc_succ_top, Nat.factorial, Nat.ascFactorial,
      Nat.descFactorial]
    ring_nf
  · rw [timeLaw_eq_tavareProb (by norm_num), kingmanProb_bot]
    simp only [Finpartition.card_bot, card_univ, Fintype.card_fin]
    norm_num [tavareProb, Nat.factorial, Nat.ascFactorial, Nat.descFactorial]
    ring_nf

/-- The jump-chain transition matrix of three genes is row-stochastic. -/
example : jumpMatrix 3 ∈ Matrix.rowStochastic ℝ (SamplePartition 3) :=
  jumpMatrix_mem_rowStochastic

/-- Kingman's formula sums to one over the two-block partitions of three genes (three
partitions of probability `1/3` each). -/
example : ∑ π with #π.parts = 2, kingmanProb 3 π = 1 :=
  sum_kingmanProb (by norm_num) (by norm_num)

/-- The time-`t` marginal of four genes sums to one, for every real `t`. -/
example (t : ℝ) : ∑ π, timeLaw 4 t π = 1 :=
  sum_timeLaw t

/-- For `t ≥ 0` the time-`t` marginal is a probability distribution. -/
example {t : ℝ} (ht : 0 ≤ t) : (∀ π, 0 ≤ timeLaw 4 t π) ∧ ∑ π, timeLaw 4 t π = 1 :=
  ⟨timeLaw_nonneg ht, sum_timeLaw t⟩

example : ProbabilityTheory.IsRateMatrix (partitionRate 3) := isRateMatrix_partitionRate

/-- Consistency of the time-`t` marginals under restriction, for a sample of `2 + 1` genes. -/
example (t : ℝ) (ρ : SamplePartition 2) :
    ∑ π with π.comap Fin.castSucc = ρ, timeLaw 3 t π = timeLaw 2 t ρ :=
  sum_timeLaw_restrict t ρ

#print axioms jumpLaw_eq
#print axioms timeLaw_eq
#print axioms sum_timeLaw_restrict

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
