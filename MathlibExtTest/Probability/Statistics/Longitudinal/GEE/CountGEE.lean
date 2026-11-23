/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.CountGEE

/-!
# Tests for the longitudinal count GEE

Everything is on one occasion (`T = Unit`) with a scalar regression parameter (`E = ℝ`), the
covariate `x₀ = 1` and `β₀ = 0`, so the model mean is `μ = exp 0 = 1` whatever the covariates.

* Definitions: `α = 0` is the Poisson variance; with working independence (`Q = 1`) and Poisson
  variance the score is `(y - μ) x`; the NB weight turns the coefficient into `1 / (1 + α μ)`,
  so a positive dispersion down-weights the cluster.
* Boundary `Q = 0`: the score and the information vanish, so the bread is singular and the
  nonsingularity hypothesis of the asymptotic theorems fails.
* Non-degenerate bread: for `Q = 1`, `α = 0`, `x₀ = 1`, `β = 0` the information is the identity.
* Unbiasedness: under the two-point count law `½ δ₀ + ½ δ₂` (mean `1 = μ`) the hypotheses of
  `integral_countGEEScore_eq_zero` hold, and the conditional mean of the score is computed to
  be `0` directly from the definitions. Under `δ₂` (mean `2 ≠ μ`, a misspecified mean) the
  conditional mean of the score is `1 ≠ 0`.
* Model-based meat: the same two-point law has variance `1 = v(μ)` for `α = 0`, so the
  hypotheses of `integral_inner_countGEEScore_sq` hold with `Q = R = 1`; both sides are also
  computed directly and equal `u²`.
* Integrated bread and meat on the joint law `δ_{x₀} ⊗ₘ twoPoint`: the hypotheses of
  `integral_fderiv_countGEEScore` and `integral_inner_countGEEScore_sq_compProd` hold, the
  expected information is `1` (so the bread is nonsingular), the expected Jacobian is `-1`, and
  `E ⟪ψ, u⟫² = u²` both through the theorem and directly over the two atoms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
open MathlibExt.Probability.Statistics.Longitudinal.GEE.CountGEE

namespace MathlibExtTest.Probability.Statistics.Longitudinal.GEE.CountGEE

/-! ### Definitions on one occasion -/

/-- `α = 0` is the Poisson variance. -/
example (m : ℝ) : nbVariance 0 m = m := by simp [nbVariance]

/-- At `β = 0` the log-link mean is `1` for every covariate. -/
theorem countMean_zero (x : Unit → ℝ) (t : Unit) : countMean (0 : ℝ) x t = 1 := by
  simp [countMean]

/-- The coefficient of the score on one occasion with `Q = 1` is `μ / v(μ) = 1 / (1 + α μ)`. -/
theorem countGEECoeff_one {α : ℝ} (hα : 0 ≤ α) (β : ℝ) (x : Unit → ℝ) :
    countGEECoeff (1 : Matrix Unit Unit ℝ) α β x () () = 1 / (1 + α * countMean β x ()) := by
  have hm := countMean_pos β x ()
  have hv := nbVariance_pos hα hm
  have h1 : 0 < 1 + α * countMean β x () := by positivity
  simp only [countGEECoeff, nbInvSqrtVar, Matrix.one_apply_eq, one_mul]
  rw [← mul_inv, Real.mul_self_sqrt hv.le]
  unfold nbVariance at hv ⊢
  field_simp

/-- Working independence with Poisson variance: the coefficient is `1`. -/
theorem countGEECoeff_poisson (β : ℝ) (x : Unit → ℝ) :
    countGEECoeff (1 : Matrix Unit Unit ℝ) 0 β x () () = 1 := by
  simp [countGEECoeff_one le_rfl]

/-- Working independence with Poisson variance: the score is `(y - μ) x`. -/
theorem countGEEScore_poisson (β : ℝ) (x y : Unit → ℝ) :
    countGEEScore (1 : Matrix Unit Unit ℝ) 0 β (x, y) = (y () - countMean β x ()) * x () := by
  simp [countGEEScore, countGEECoeff_poisson]

/-- The NB weight with `α = 1` halves the Poisson coefficient at `μ = 1`. -/
example : countGEECoeff (1 : Matrix Unit Unit ℝ) 1 (0 : ℝ) (fun _ => 1) () () = 1 / 2 := by
  rw [countGEECoeff_one zero_le_one, countMean_zero]
  norm_num

/-! ### Boundary: `Q = 0` makes the bread singular -/

example (α β : ℝ) (z : (Unit → ℝ) × (Unit → ℝ)) :
    countGEEScore (0 : Matrix Unit Unit ℝ) α β z = 0 := by
  simp [countGEEScore, countGEECoeff]

theorem countGEEInfo_zero (α β : ℝ) (x : Unit → ℝ) :
    countGEEInfo (0 : Matrix Unit Unit ℝ) α β x = 0 := by
  simp [countGEEInfo, countGEECoeff]

example (α β : ℝ) (μ : Measure ((Unit → ℝ) × (Unit → ℝ))) :
    ¬IsUnit (∫ z, countGEEInfo (0 : Matrix Unit Unit ℝ) α β z.1 ∂μ) := by
  simp [countGEEInfo_zero]

/-! ### A non-degenerate bread -/

/-- The covariate `x₀ = 1` on the single occasion. -/
def x₀ : Unit → ℝ := fun _ => 1

theorem countGEEInfo_x₀ : countGEEInfo (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) x₀ = 1 := by
  refine ContinuousLinearMap.ext fun h => ?_
  rw [countGEEInfo_apply]
  simp [countGEECoeff_poisson, countMean_zero, x₀]

example : IsUnit (countGEEInfo (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) x₀) := by
  rw [countGEEInfo_x₀]
  exact isUnit_one

/-! ### A two-point count law with mean `1` and variance `1` -/

/-- The counts `0` and `2` with probability `½` each. -/
noncomputable def twoPoint : Measure (Unit → ℝ) :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac (fun _ => 0) + Measure.dirac (fun _ => 2))

instance : IsProbabilityMeasure twoPoint :=
  ⟨by simp [twoPoint, ← two_mul]; exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

theorem integral_twoPoint {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : (Unit → ℝ) → F) :
    ∫ y, f y ∂twoPoint = (2⁻¹ : ℝ) • (f (fun _ => 0) + f (fun _ => 2)) := by
  rw [twoPoint, integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]
  simp

theorem memLp_twoPoint (t : Unit) : MemLp (fun y : Unit → ℝ => y t) 2 twoPoint :=
  ((memLp_dirac enorm_lt_top).add_measure (memLp_dirac enorm_lt_top)).smul_measure (by simp)

theorem integrable_twoPoint (t : Unit) : Integrable (fun y : Unit → ℝ => y t) twoPoint :=
  (memLp_twoPoint t).integrable one_le_two

/-- The two-point law has the model mean `μ = 1` at `β₀ = 0`. -/
theorem integral_twoPoint_eq_countMean (x : Unit → ℝ) (t : Unit) :
    ∫ y, y t ∂twoPoint = countMean (0 : ℝ) x t := by
  rw [integral_twoPoint, countMean_zero]
  norm_num

/-! ### Unbiasedness: the hypotheses hold, and a misspecified mean breaks it -/

/-- The conditional mean hypothesis of `integral_countGEEScore_eq_zero` holds for the
covariate law `δ_{x₀}` and the count kernel constant at `twoPoint`. -/
theorem hy_twoPoint : ∀ᵐ x ∂(Measure.dirac x₀), ∀ t,
    Integrable (fun y : Unit → ℝ => y t) (Kernel.const (Unit → ℝ) twoPoint x) ∧
      ∫ y, y t ∂(Kernel.const (Unit → ℝ) twoPoint x) = countMean (0 : ℝ) x t :=
  ae_of_all _ fun x t => by
    simp only [Kernel.const_apply]
    exact ⟨integrable_twoPoint t, integral_twoPoint_eq_countMean x t⟩

/-- The joint law of one cluster is the two-point law `½ δ_{(x₀, 0)} + ½ δ_{(x₀, 2)}`. -/
theorem compProd_twoPoint : Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint =
    (2⁻¹ : ℝ≥0∞) • (Measure.dirac (x₀, fun _ => 0) + Measure.dirac (x₀, fun _ => 2)) := by
  rw [Measure.compProd_const, Measure.dirac_prod, twoPoint, Measure.map_smul,
    Measure.map_add _ _ measurable_prodMk_left, Measure.map_dirac' measurable_prodMk_left,
    Measure.map_dirac' measurable_prodMk_left]
  exact measurable_prodMk_left.aemeasurable

/-- Every function is integrable for the two-atom joint law. -/
theorem integrable_compProd_twoPoint {F : Type*} [NormedAddCommGroup F]
    (f : (Unit → ℝ) × (Unit → ℝ) → F) :
    Integrable f (Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) := by
  rw [compProd_twoPoint]
  exact ((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).smul_measure
    (by simp)

theorem integral_compProd_twoPoint {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : (Unit → ℝ) × (Unit → ℝ) → F) :
    ∫ z, f z ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) =
      (2⁻¹ : ℝ) • (f (x₀, fun _ => 0) + f (x₀, fun _ => 2)) := by
  rw [compProd_twoPoint, integral_smul_measure,
    integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top),
    integral_dirac, integral_dirac]
  simp

theorem integrable_countGEEScore_twoPoint :
    Integrable (countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ))
      (Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) :=
  integrable_compProd_twoPoint _

/-- Non-vacuity of `integral_countGEEScore_eq_zero`: every hypothesis holds. -/
example : ∫ z, countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) z
    ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) = 0 :=
  integral_countGEEScore_eq_zero _ _ hy_twoPoint integrable_countGEEScore_twoPoint

/-- The same conclusion computed from the definitions: the score is `-1` at `y = 0` and `1` at
`y = 2`, so its conditional mean is `0`. -/
example : ∫ y, countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) (x₀, y) ∂twoPoint = 0 := by
  rw [integral_twoPoint]
  simp [countGEEScore_poisson, countMean_zero, x₀]
  norm_num

/-- **Boundary: a misspecified mean.** If the counts are `2` almost surely (conditional mean
`2`, while the model says `1`), the conditional mean of the score is `1 ≠ 0`. -/
example : ∫ y, countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) (x₀, y)
    ∂(Measure.dirac fun _ => 2) = 1 := by
  rw [integral_dirac]
  simp [countGEEScore_poisson, countMean_zero, x₀]
  norm_num

/-! ### The meat under a correct working covariance -/

/-- The second moment of the two-point law about the model mean is `1 = v(1)` for `α = 0`,
the NB working covariance with correlation `R = 1`. -/
theorem hcov_twoPoint (x : Unit → ℝ) (s t : Unit) :
    ∫ y, (y s - countMean (0 : ℝ) x s) * (y t - countMean (0 : ℝ) x t) ∂twoPoint =
      √(nbVariance 0 (countMean (0 : ℝ) x s)) * √(nbVariance 0 (countMean (0 : ℝ) x t)) *
        (1 : Matrix Unit Unit ℝ) s t := by
  rw [integral_twoPoint]
  simp [countMean_zero, nbVariance]
  norm_num

/-- Non-vacuity of `integral_inner_countGEEScore_sq`: every hypothesis holds. -/
example (u : ℝ) : ∫ y, ⟪countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) (x₀, y), u⟫ ^ 2
    ∂twoPoint = ⟪countGEEInfo (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) x₀ u, u⟫ :=
  integral_inner_countGEEScore_sq le_rfl 1 1 (mul_one 1) 0 x₀ memLp_twoPoint (hcov_twoPoint x₀) u

/-- Both sides computed from the definitions: `E ⟪ψ, u⟫² = u²`. -/
example (u : ℝ) : ∫ y, ⟪countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) (x₀, y), u⟫ ^ 2
    ∂twoPoint = u ^ 2 := by
  rw [integral_twoPoint]
  simp [countGEEScore_poisson, countMean_zero, x₀]
  ring

example (u : ℝ) : ⟪countGEEInfo (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) x₀ u, u⟫ = u ^ 2 := by
  rw [countGEEInfo_x₀]
  simp [sq]

/-! ### The integrated bread and meat on the joint law

On `δ_{x₀} ⊗ₘ twoPoint` the hypotheses `hy`, `hinfo`, `hψ'_int` and `hA` that the count GEE adds
to the Z-estimator theorem all hold. -/

/-- The expected model-based information on the joint law is `1`, computed from the
definitions; in particular the bread is nonsingular (`hA`). -/
theorem integral_countGEEInfo_twoPoint :
    ∫ z, countGEEInfo (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) z.1
      ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) = 1 := by
  rw [integral_compProd_twoPoint]
  simp only [countGEEInfo_x₀]
  rw [← two_smul ℝ (1 : ℝ →L[ℝ] ℝ), smul_smul]
  norm_num

example : IsUnit (∫ z, countGEEInfo (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) z.1
    ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint)) := by
  rw [integral_countGEEInfo_twoPoint]
  exact isUnit_one

/-- Non-vacuity of `integral_fderiv_countGEEScore` (the bread): every hypothesis holds, and
with the information computed above the expected Jacobian is `-1`. -/
example : ∫ z, fderiv ℝ (fun b => countGEEScore (1 : Matrix Unit Unit ℝ) 0 b z) (0 : ℝ)
    ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) = -1 := by
  rw [integral_fderiv_countGEEScore le_rfl 1 hy_twoPoint (integrable_compProd_twoPoint _)
    (integrable_compProd_twoPoint _), integral_countGEEInfo_twoPoint]

/-- Non-vacuity of `integral_inner_countGEEScore_sq_compProd` (meat equals bread, integrated):
every hypothesis holds, and both sides equal `u²`. -/
example (u : ℝ) : ∫ z, ⟪countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) z, u⟫ ^ 2
    ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) = u ^ 2 := by
  rw [integral_inner_countGEEScore_sq_compProd le_rfl 1 1 (mul_one 1)
    (ae_of_all _ fun x t => by simpa only [Kernel.const_apply] using memLp_twoPoint t)
    (ae_of_all _ fun x s t => by simpa only [Kernel.const_apply] using hcov_twoPoint x s t) u
    (integrable_compProd_twoPoint _) (integrable_compProd_twoPoint _),
    integral_countGEEInfo_twoPoint]
  simp [sq]

/-- The left side computed from the definitions over the two atoms. -/
example (u : ℝ) : ∫ z, ⟪countGEEScore (1 : Matrix Unit Unit ℝ) 0 (0 : ℝ) z, u⟫ ^ 2
    ∂(Measure.dirac x₀ ⊗ₘ Kernel.const (Unit → ℝ) twoPoint) = u ^ 2 := by
  rw [integral_compProd_twoPoint]
  simp [countGEEScore_poisson, countMean_zero, x₀]
  ring

end MathlibExtTest.Probability.Statistics.Longitudinal.GEE.CountGEE
