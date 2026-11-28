/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Immunology.HeteroscedasticAffinity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Tests for the heteroscedastic Gaussian likelihood of measured binding affinities.

* one example: the term of a measurement, a violated and a satisfied bound of each direction, a
  mean on the bound, and the convention at a zero variance;
* a training set of three examples under an intercept model `μ_θ(x) = θ` with the
  input-dependent variances `1`, `4` and `9`: a measurement `2`; an upper bound `0` and the
  presentation label `false`; and an unobserved affinity with the presentation label `true`. At
  `θ = 1` the bound is violated and the affinity loss is `5/8 + log 2`; with a predicted
  presentation probability `1/2` the joint loss adds `log 2` for each presentation label. At
  `θ = 0` the bound is satisfied and only the measurement counts;
* the results on these data: the Gaussian negative log-likelihood, maximum likelihood as minimum
  loss (whose variance hypothesis these data satisfy), the least-squares reduction under a constant
  variance, and the stationary variance `(a - m) ^ 2`. -/

open Real ProbabilityTheory
open scoped NNReal
open Domains.Biology.Immunology.HeteroscedasticAffinity

namespace DomainsTest.Biology.Immunology.HeteroscedasticAffinity

/-! ### One example -/

/-- A measurement `3` under the mean `1` and the variance `4`: `((3 - 1) ^ 2 / 4 + log 4) / 2`. -/
example : affinityTerm 1 4 (.exact 3) = (1 + log 4) / 2 := by
  norm_num [affinityTerm]

/-- An upper bound `0` that the mean `1` violates counts as a measurement at the bound. -/
example : affinityTerm 1 4 (.atMost 0) = (1 / 4 + log 4) / 2 := by
  norm_num [affinityTerm]

/-- An upper bound `2` that the mean `1` satisfies contributes nothing. -/
example : affinityTerm 1 4 (.atMost 2) = 0 := by
  norm_num [affinityTerm]

/-- A lower bound `3` that the mean `1` violates counts as a measurement at the bound. -/
example : affinityTerm 1 4 (.atLeast 3) = (1 + log 4) / 2 := by
  norm_num [affinityTerm]

/-- A lower bound `0` that the mean `1` satisfies contributes nothing. -/
example : affinityTerm 1 4 (.atLeast 0) = 0 := by
  norm_num [affinityTerm]

/-- The bounds are inclusive: a mean on the bound satisfies it, from either side. -/
example (v : ℝ≥0) : affinityTerm 1 v (.atMost 1) = 0 ∧ affinityTerm 1 v (.atLeast 1) = 0 :=
  ⟨affinityTerm_atMost_of_le v le_rfl, affinityTerm_atLeast_of_le v le_rfl⟩

/-- The general lemmas give the same violated bounds. -/
example : affinityTerm 1 4 (.atMost 0) = affinityTerm 1 4 (.exact 0) ∧
    affinityTerm 1 4 (.atLeast 3) = affinityTerm 1 4 (.exact 3) :=
  ⟨affinityTerm_atMost_of_lt 4 (by norm_num), affinityTerm_atLeast_of_lt 4 (by norm_num)⟩

/-- At a zero variance the term takes Lean's conventions `r / 0 = 0` and `log 0 = 0`. -/
example (m a : ℝ) : affinityTerm m 0 (.exact a) = 0 := by
  simp [affinityTerm]

/-- The term of a measurement is its Gaussian negative log-likelihood less `log (2π) / 2`: for the
standard Gaussian at its mean the term is `0`, so the density there is `(2π)^(-1/2)`. -/
example : -log (gaussianPDFReal 0 1 0) = log (2 * π) / 2 := by
  have h := affinityTerm_exact_eq_neg_log_gaussianPDFReal 0 one_ne_zero 0
  norm_num [affinityTerm] at h
  linarith

/-- The cross-entropy of a presentation label is the textbook `-(y log p + (1 - y) log (1 - p))`
with `y ∈ {0, 1}`. -/
example (b : Bool) (p : ℝ) :
    -log (if b then p else 1 - p) =
      -((if b then 1 else 0) * log p + (1 - if b then 1 else 0) * log (1 - p)) := by
  cases b <;> simp

/-! ### The stationary variance

For the measurement `3` under the mean `1`, the squared residual is `4`. -/

/-- The term is stationary in the variance at `4`. -/
example : deriv (fun s : ℝ => affinityTerm 1 s.toNNReal (.exact 3)) 4 = 0 :=
  (deriv_affinityTerm_exact_var_eq_zero_iff 1 3 (by norm_num)).2 (by norm_num)

/-- It is not stationary at the variance `1`. -/
example : deriv (fun s : ℝ => affinityTerm 1 s.toNNReal (.exact 3)) 1 ≠ 0 := by
  rw [Ne, deriv_affinityTerm_exact_var_eq_zero_iff 1 3 one_pos]
  norm_num

/-- The variance `4` minimises the term over the positive variances, here against the variance
`1`, whose term is `2`. -/
example : affinityTerm 1 4 (.exact 3) ≤ affinityTerm 1 1 (.exact 3) := by
  have h := isMinOn_affinityTerm_exact_var 1 (a := 3) (by norm_num)
  have h4 : ((3 - 1 : ℝ) ^ 2).toNNReal = 4 := by
    rw [show ((3 - 1 : ℝ) ^ 2) = ((4 : ℝ≥0) : ℝ) by norm_num, Real.toNNReal_coe]
  rw [h4] at h
  exact h (show (1 : ℝ≥0) ≠ 0 from one_ne_zero)

/-- At the variance `1` the term is `2`, and at the variance `4` it is `(1 + log 4) / 2`. -/
example : affinityTerm 1 1 (.exact 3) = 2 := by
  norm_num [affinityTerm]

/-! ### A training set of three examples -/

/-- The intercept model: the predicted mean is the parameter. -/
def mean : ℝ → Fin 3 → ℝ := fun θ _ => θ

/-- The input-dependent predicted variances `1`, `4` and `9`. -/
noncomputable def var : ℝ → Fin 3 → ℝ≥0 := fun _ => ![1, 4, 9]

/-- The predicted presentation probability `1/2`. -/
noncomputable def prob : ℝ → Fin 3 → ℝ := fun _ _ => 1 / 2

/-- The affinity labels: a measurement `2`, an upper bound `0`, and an unobserved affinity. -/
noncomputable def labels : Fin 3 → Option AffinityLabel := ![some (.exact 2), some (.atMost 0), none]

/-- The presentation labels: unobserved, not a ligand, a ligand. -/
def presented : Fin 3 → Option Bool := ![none, some false, some true]

/-- At `θ = 1` the bound `0` is violated: `1/2 + (1/4 + log 4) / 2 = 5/8 + log 2`. -/
example : affinityLoss mean var id labels 1 = 5 / 8 + log 2 := by
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  simp [affinityLoss, Fin.sum_univ_three, labels, mean, var, affinityTerm, h4]
  ring

/-- At `θ = 0` the bound `0` is satisfied, and only the measurement counts: `(4 + log 1) / 2`. -/
example : affinityLoss mean var id labels 0 = 2 := by
  norm_num [affinityLoss, Fin.sum_univ_three, labels, mean, var, affinityTerm]

/-- The joint loss at `θ = 1` adds `-log (1 - 1/2) = log 2` for the label `false` and
`-log (1/2) = log 2` for the label `true`. -/
example : jointLoss mean var prob id labels presented 1 = 5 / 8 + 3 * log 2 := by
  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  simp [jointLoss, affinityLoss, Fin.sum_univ_three, labels, presented, mean, var, prob,
    affinityTerm, h4]
  rw [show (1 - 2⁻¹ : ℝ) = 2⁻¹ by norm_num, log_inv]
  ring

/-- Without presentation labels the joint loss is the affinity loss. -/
example (θ : ℝ) :
    jointLoss mean var prob id labels (fun _ => none) θ = affinityLoss mean var id labels θ :=
  jointLoss_of_forall_eq_none mean var prob id labels (fun _ => rfl) θ

/-! ### Measured affinities -/

/-- The variances of the training set are positive, as the likelihood results ask. -/
theorem var_ne_zero (θ : ℝ) (i : Fin 3) : var θ i ≠ 0 := by
  fin_cases i <;> simp [var]

/-- The measured affinities `2`, `0` and `5`. -/
def measured : Fin 3 → ℝ := ![2, 0, 5]

/-- On measurements, the affinity loss is the Gaussian negative log-likelihood less
`3 log (2π) / 2`. -/
example (θ : ℝ) :
    affinityLoss mean var id (fun i => some (.exact (measured i))) θ =
      -log (∏ i, gaussianPDFReal (mean θ i) (var θ i) (measured i)) - 3 * log (2 * π) / 2 := by
  simpa using affinityLoss_exact_eq_neg_log_prod_gaussianPDFReal (x := id) measured
    (var_ne_zero θ)

/-- Maximum likelihood over all parameters is minimum affinity loss. -/
example (θ₀ : ℝ) :
    IsMaxOn (fun θ => ∏ i, gaussianPDFReal (mean θ i) (var θ i) (measured i)) Set.univ θ₀ ↔
      IsMinOn (affinityLoss mean var id fun i => some (.exact (measured i))) Set.univ θ₀ :=
  isMaxOn_prod_gaussianPDFReal_iff_isMinOn_affinityLoss (x := id) measured (Set.mem_univ θ₀)
    fun θ _ => var_ne_zero θ

/-- Under the constant variance `4`, the affinity loss is the sum of squared residuals over `8`
plus `3 log 4 / 2`. -/
example (θ : ℝ) :
    affinityLoss mean (fun _ _ => 4) id (fun i => some (.exact (measured i))) θ =
      ((2 - θ) ^ 2 + (0 - θ) ^ 2 + (5 - θ) ^ 2) / 8 + 3 * log 4 / 2 := by
  rw [affinityLoss_const_var]
  norm_num [Fin.sum_univ_three, measured, mean]

/-- Under the constant variance `4`, the affinity loss of the intercept model is minimised at the
mean `7/3` of the measurements, the least-squares estimate. -/
example :
    IsMinOn (affinityLoss mean (fun _ _ => 4) id fun i => some (.exact (measured i)))
      Set.univ (7 / 3) := by
  rw [isMinOn_affinityLoss_const_var_iff (by norm_num)]
  intro θ _
  simp only [Set.mem_ofPred_eq, Fin.sum_univ_three, measured, mean, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (θ - 7 / 3)]

end DomainsTest.Biology.Immunology.HeteroscedasticAffinity
