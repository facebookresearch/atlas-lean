/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.TajimaDNormalized
import Mathlib.Tactic.NormNum

/-!
# Tests for normalized Tajima's `D`

Boundary and non-vacuity checks computed from the definitions: the bound on `1 / √V` is attained
at `S = 1` and has junk value `0` at `S = 0`; the counterexample refutes `E[N] = 0 → E[D] = 0`;
the denominator term of the derivative of `x / √y` is nonzero off `x = 0`; the delta-method
variance is `1` when `Var N` equals the centring value; the hypotheses of the asymptotic-normality
theorem are jointly satisfiable; and the bounded-range hypotheses hold on realizable data.
-/

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaDNormalized

open MeasureTheory ProbabilityTheory Filter
open MathlibExt.Biology.PopulationGenetics.Coalescent

private theorem a1_four : tajimaA1 4 = 11 / 6 := by
  simp [tajimaA1, Finset.sum_Ico_succ_top]
  norm_num

/-- `c₁ θ + c₂ θ² > 0` at the smallest nondegenerate sample size. -/
example : 0 < tajimaC1 4 * 1 + tajimaC2 4 * 1 ^ 2 := tajimaVariance_pos le_rfl one_pos

/-- The bound `1 / √V ≤ 1 / √e₁` is attained at `S = 1`. -/
example : (Real.sqrt (tajimaE1 4 * 1 + tajimaE2 4 * (1 * (1 - 1))))⁻¹ =
    (Real.sqrt (tajimaE1 4))⁻¹ := by
  simp

/-- At `S = 0` the reciprocal denominator takes Lean's junk value `0`. -/
example : (Real.sqrt (tajimaE1 4 * 0 + tajimaE2 4 * (0 * (0 - 1))))⁻¹ = 0 := by
  simp

/-- Two segregating sites satisfy the hypothesis of the bound. -/
example : (Real.sqrt (tajimaE1 4 * 2 + tajimaE2 4 * (2 * (2 - 1))))⁻¹ ≤
    (Real.sqrt (tajimaE1 4))⁻¹ :=
  inv_sqrt_tajimaVarEstimator_le le_rfl (Or.inr (by norm_num))

/-- A mean-zero numerator does not force a mean-zero `D`. -/
example : ¬ ∀ (μ : Measure Bool) [IsProbabilityMeasure μ] (π S : Bool → ℝ),
    μ[fun b => π b - S b / tajimaA1 4] = 0 → μ[fun b => tajimaD 4 (π b) (S b)] = 0 := by
  intro h
  obtain ⟨μ, π, S, hμ, -, hN, -, hD⟩ := exists_integral_tajimaD_ne
  exact hD.ne' (h μ π S hN)

/-- Off `x₀ = 0` the denominator does enter the derivative: at `(1, 4)` the `dy` coefficient is
`-1 / (2 · 4 · 2) = -1/16`. -/
example : ((Real.sqrt 4)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (1 / (2 * 4 * Real.sqrt 4)) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((0 : ℝ), (1 : ℝ)) =
    -1 / 16 := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [h]
  norm_num

/-- The derivative theorem applies at `(1, 4)`. -/
example : HasFDerivAt (fun p : ℝ × ℝ => p.1 / Real.sqrt p.2)
    ((Real.sqrt 4)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ -
      (1 / (2 * 4 * Real.sqrt 4)) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((1 : ℝ), (4 : ℝ)) :=
  hasFDerivAt_div_sqrt (by norm_num)

/-- The delta-method variance is `1` when `Var N` equals the centring value `v`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (N V : Ω → ℝ)
    (h : Var[N; μ] = 4) :
    Var[fun ω => ((Real.sqrt 4)⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) (N ω, V ω - 4); μ] = 1 := by
  rw [variance_linearization_div_sqrt μ N V (by norm_num), h]
  norm_num

/-- The hypotheses of `tendstoInDistribution_tajimaD_gaussian` are jointly satisfiable: with
`n = 4`, `S = 1`, `r = 1 / √e₁` and `π = 1 / a₁ + √e₁ Z` for a standard Gaussian `Z`, the scaled
numerator is `Z` and `r² V = 1`. -/
example : TendstoInDistribution (fun (_ : ℕ) (x : ℝ) =>
      tajimaD 4 (1 / tajimaA1 4 + Real.sqrt (tajimaE1 4) * x) 1) atTop id
      (fun _ => gaussianReal 0 1) (gaussianReal 0 1) := by
  have he1 : 0 < tajimaE1 4 := by
    have := tajimaVarEstimator_pos (n := 4) le_rfl (S := 1) le_rfl
    simpa using this
  have hs : Real.sqrt (tajimaE1 4) ≠ 0 := (Real.sqrt_pos.2 he1).ne'
  have hlaw : HasLaw (id : ℝ → ℝ) (gaussianReal 0 1) (gaussianReal 0 1) := HasLaw.id
  refine tendstoInDistribution_tajimaD_gaussian (n := fun _ => 4)
    (S := fun _ _ => 1) (r := fun _ => (Real.sqrt (tajimaE1 4))⁻¹) (σ2 := 1) one_ne_zero
    (fun _ => by positivity) ?_ (Z := id) hlaw ?_ (fun _ => measurable_const.aemeasurable) hlaw
  · refine (tendstoInDistribution_const (l := atTop) measurable_id.aemeasurable).congr
      (fun _ => ae_of_all _ fun x => ?_) (ae_of_all _ fun _ => rfl)
    simp only [id, one_div]
    field_simp
    ring
  · rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_const_nhds.congr fun _ => ?_
    have : (Real.sqrt (tajimaE1 4))⁻¹ ^ 2 * (tajimaE1 4 * 1 + tajimaE2 4 * (1 * (1 - 1))) =
        ((1 : NNReal) : ℝ) := by
      rw [inv_pow, Real.sq_sqrt he1.le]
      simp [he1.ne']
    simp only [this, dist_self]
    simp [hε.not_ge]

/-- Realizable data (two singleton sites, `n = 4`) satisfy the bounded-range hypothesis with
`β = 1/22`. -/
example : |tajimaD 4 1 2| ≤ 1 / 22 / Real.sqrt (min (tajimaE1 4) (tajimaE2 4) / 2) :=
  abs_tajimaD_le le_rfl (by norm_num) (by rw [a1_four]; norm_num [abs_of_neg])

/-- The non-Gaussianity hypotheses are satisfiable: a degenerate data law with `S = 1`,
`π = 1 / a₁` (so `D = 0`) is not `N(0, 1)`. -/
example : ¬ HasLaw (fun _ : ℝ => tajimaD 4 (1 / tajimaA1 4) 1) (gaussianReal 0 1)
    (Measure.dirac (0 : ℝ)) :=
  not_hasLaw_tajimaD_gaussianReal (β := 0) le_rfl (ae_of_all _ fun _ => Or.inr le_rfl)
    (ae_of_all _ fun _ => by simp) 0 one_ne_zero

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.TajimaDNormalized
