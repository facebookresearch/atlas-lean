/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialRestrictedMLE

@[expose] public section

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial

namespace MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialRestrictedMLE

/-! ### The log mass function is nonpositive -/

/-- Computed from the definition: `nbLogPmf 1 0 0 = log (1 / 2) = -log 2 < 0`. -/
example : nbLogPmf 1 0 0 = -log 2 := by
  norm_num [nbLogPmf, nbKernel]

example : nbLogPmf 1 0 0 < 0 := by
  have : nbLogPmf 1 0 0 = -log 2 := by norm_num [nbLogPmf, nbKernel]
  rw [this]
  exact neg_neg_of_pos (log_pos one_lt_two)

example : nbLogPmf 1 0 0 ≤ 0 := nbLogPmf_nonpos one_pos 0 0

/-! ### Restricted and profile likelihood on a one-count design -/

/-- One observation, one coefficient, design entry `0`, offset `0`, count `0`. -/
noncomputable abbrev X0 : Matrix (Fin 1) (Fin 1) ℝ := 0

/-- The restricted log-likelihood of the zero design is the log mass at `η = 0`, computed
from the definitions. -/
example (θ : ℝ) (β₀ : Fin 1 → ℝ) :
    nbRestrictedLogLik X0 0 0 β₀ θ = nbLogPmf θ 0 0 := by
  simp [nbRestrictedLogLik, nbJointLogLik, X0]

/-- With the zero design every section is constant in `β`, so the profile is the section value;
computed from the definition with `ciSup_const`, not through `nbProfileLogLik_eq_of_isMaxOn`. -/
example (θ : ℝ) : nbProfileLogLik X0 0 0 θ = nbLogPmf θ 0 0 := by
  have h : (fun β : Fin 1 → ℝ => nbJointLogLik X0 0 0 (β, θ)) = fun _ => nbLogPmf θ 0 0 := by
    funext β
    simp [nbJointLogLik, X0]
  rw [nbProfileLogLik, h, ciSup_const]

/-- The same value through `nbProfileLogLik_eq_of_isMaxOn` (every `β` is a section maximizer). -/
example (θ : ℝ) : nbProfileLogLik X0 0 0 θ = nbJointLogLik X0 0 0 (0, θ) := by
  refine nbProfileLogLik_eq_of_isMaxOn X0 0 0 fun β _ => ?_
  simp [nbJointLogLik, X0]

/-- At `θ = 1` the profile of the zero design is `-log 2`. -/
example : nbProfileLogLik X0 0 0 1 = -log 2 := by
  have h : (fun β : Fin 1 → ℝ => nbJointLogLik X0 0 0 (β, 1)) = fun _ => -log 2 := by
    funext β
    norm_num [nbJointLogLik, X0, nbLogPmf, nbKernel]
  rw [nbProfileLogLik, h, ciSup_const]

/-! ### The composite likelihood-ratio statistic -/

/-- If the joint and restricted fits coincide, the composite statistic is `0`. -/
example (θ : ℝ) (β₀ : Fin 1 → ℝ) : nbCompositeLRStat X0 0 0 (β₀, θ) β₀ θ = 0 := by
  simp [nbCompositeLRStat, nbRestrictedLogLik]

/-- A nonzero value computed from the definitions: zero design, count `0`, joint shape `1`,
restricted shape `2`. `nbLogPmf 1 0 0 = -log 2` and `nbLogPmf 2 0 0 = 2 log 2 - 2 log 3`, so the
statistic is `2 (2 log 3 - 3 log 2) = 2 log (9 / 8) > 0`. -/
example (β₀ : Fin 1 → ℝ) :
    nbCompositeLRStat X0 0 0 (β₀, 1) β₀ 2 = 2 * (2 * log 3 - 3 * log 2) := by
  have h3 : log (2 + 1 : ℝ) = log 3 := by norm_num
  simp only [nbCompositeLRStat, nbRestrictedLogLik, nbJointLogLik, X0, nbLogPmf, nbKernel]
  norm_num [h3]
  ring

example : 0 < 2 * (2 * log 3 - 3 * log 2) := by
  have h : log 8 < log 9 := log_lt_log (by norm_num) (by norm_num)
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]; norm_num
  have h9 : log 9 = 2 * log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]; norm_num
  linarith

/-! ### Block-diagonal quadratic forms -/

/-- Computed from the definitions: `[[2, 0], [0, 3]]` with `s = (1, 2)` gives
`1 · 2 · 1 + 3 · 2² = 14`. -/
example : Sum.elim ![(1 : ℝ)] (fun _ : Unit => 2) ⬝ᵥ
    (fromBlocks !![(2 : ℝ)] 0 0 (of fun _ _ : Unit => 3) *ᵥ
      Sum.elim ![(1 : ℝ)] (fun _ : Unit => 2)) = 14 := by
  simp [dotProduct, mulVec, fromBlocks, Fintype.sum_sum_type]
  norm_num

/-- The same value through `sumElim_dotProduct_fromBlocks_mulVec`. -/
example : Sum.elim ![(1 : ℝ)] (fun _ : Unit => 2) ⬝ᵥ
    (fromBlocks !![(2 : ℝ)] 0 0 (of fun _ _ : Unit => 3) *ᵥ
      Sum.elim ![(1 : ℝ)] (fun _ : Unit => 2)) = 14 := by
  rw [sumElim_dotProduct_fromBlocks_mulVec]
  simp [dotProduct, mulVec]
  norm_num

/-- The inverse form at `A = 1`, `d = 2`, `s = (1, 2)`: `1 + 2² / 2 = 3`. -/
example : Sum.elim ![(1 : ℝ)] (fun _ : Unit => 2) ⬝ᵥ
    ((fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (of fun _ _ : Unit => 2))⁻¹ *ᵥ
      Sum.elim ![(1 : ℝ)] (fun _ : Unit => 2)) = 3 := by
  rw [sumElim_dotProduct_inv_fromBlocks_mulVec isUnit_one two_ne_zero]
  simp [dotProduct]
  norm_num

/-! ### The cross term behind `hcross` has mean zero -/

/-- The mean of the cross term `nbCross θ y η` under `NB(θ, e^η)` is zero for every `θ > 0`
(merged `hasSum_nbCross_mul_negBinomialReal`): this is why the uniform law of large numbers in
`tendstoInMeasure_nbCoefScore_restricted_sub` has limit zero. -/
example : HasSum (fun k : ℕ => nbCross 1 k 0 * negBinomialReal 1 (exp 0) k) 0 :=
  hasSum_nbCross_mul_negBinomialReal one_pos 0

end MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialRestrictedMLE
