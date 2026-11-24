/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FisherInformation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Cramér–Rao bound for a finite-dimensional parameter

For a parameter `θ ∈ ℝ^k` with positive definite Fisher information matrix `I(θ)`, a real-valued
unbiased estimator `T` of a real function `g(θ)` satisfies `Var_θ T ≥ ∇g(θ)ᵀ I(θ)⁻¹ ∇g(θ)`
(C. R. Rao, "Information and the accuracy attainable in the estimation of statistical
parameters", *Bull. Calcutta Math. Soc.* 37 (1945) 81–91). This is the form for one real
estimator. The matrix form `Cov_θ(T) ⪰ J I(θ)⁻¹ Jᵀ` for a vector of estimators follows by
applying it to every linear combination `cᵀ T`, but it is not stated here.

The proof reduces to the one-parameter inequality
`MathlibExt.Probability.Statistics.FisherInformation.sq_deriv_le_fisherInformation_mul` along the
line `t ↦ θ + t a`, whose Fisher information is the quadratic form `aᵀ I(θ) a`, and then takes
`a = I(θ)⁻¹ ∇g(θ)`.

## Main results

* `sq_inner_le_quadForm_mul`: the directional bound `⟨a, ∇g(θ)⟩² ≤ (aᵀ I(θ) a) Var_θ T`.
* `cramerRao_multiparameter`: `∇g(θ)ᵀ I(θ)⁻¹ ∇g(θ) ≤ Var_θ T`.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix
open scoped Matrix

namespace MathlibExt.Probability.Statistics.MultiparameterCramerRao

open MathlibExt.Probability.Statistics.FisherInformation

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- A linear functional on `ℝ^k` is determined by its values on the standard basis. -/
private theorem clm_apply_eq_sum (f : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin k)) : f v = ∑ i, v i * f (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply]

/-- A linear functional on `ℝ^k` as a combination of the coordinate projections. -/
private theorem clm_eq_sum (f : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    f = ∑ i, f (EuclideanSpace.single i 1) •
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) := by
  ext v
  rw [clm_apply_eq_sum f v]
  simp [mul_comm]

private theorem aux_abs_le (s q : ℝ) (hq : 0 < q) : |s| ≤ (s ^ 2 / q + q) / 2 := by
  rw [← sq_abs s, div_add' _ _ _ hq.ne', div_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|s| - q)]

private theorem aux_abs_mul_le (t s q : ℝ) (hq : 0 < q) :
    |t * s| ≤ (t ^ 2 * q + s ^ 2 / q) / 2 := by
  rw [abs_mul, ← sq_abs t, ← sq_abs s, add_div' _ _ _ hq.ne', div_div,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (|t| * q - |s|)]

private theorem aux_abs_div_le (s r q : ℝ) (hq : 0 < q) :
    |s * r / q| ≤ (s ^ 2 / q + r ^ 2 / q) / 2 := by
  rw [abs_div, abs_of_pos hq, abs_mul, ← sq_abs s, ← sq_abs r, ← add_div, div_div,
    div_le_div_iff₀ hq (by positivity)]
  nlinarith [sq_nonneg (|s| - |r|), hq]

/-- **Directional Cramér–Rao inequality.** Under the hypotheses of `cramerRao_multiparameter`
except positive definiteness, for every direction `a ∈ ℝ^k`,
`⟨a, ∇g(θ)⟩² ≤ (aᵀ I(θ) a) Var_θ T`, where `I(θ)_{ij} = ∫ ∂_i p_θ ∂_j p_θ / p_θ dν` is the
Fisher information matrix: the one-parameter Cramér–Rao inequality along the line
`t ↦ θ + t a` (C. R. Rao, *Bull. Calcutta Math. Soc.* 37 (1945) 81–91). -/
theorem sq_inner_le_quadForm_mul {ν : Measure 𝓧} {p : EuclideanSpace ℝ (Fin k) → 𝓧 → ℝ}
    {T : 𝓧 → ℝ} {g : EuclideanSpace ℝ (Fin k) → ℝ} {θ : EuclideanSpace ℝ (Fin k)}
    (hp_nonneg : ∀ θ' x, 0 ≤ p θ' x)
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun θ' => p θ' x) θ)
    (hs_meas : ∀ i, AEStronglyMeasurable
      (fun x => fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1)) ν)
    (hI_int : ∀ i, Integrable
      (fun x => fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) ^ 2 / p θ x) ν)
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (h_deriv_one : HasFDerivAt (fun θ' => ∫ x, p θ' x ∂ν)
      (∫ x, fderiv ℝ (fun θ' => p θ' x) θ ∂ν) θ)
    (h_deriv_T : HasFDerivAt (fun θ' => ∫ x, T x * p θ' x ∂ν)
      (∫ x, T x • fderiv ℝ (fun θ' => p θ' x) θ ∂ν) θ)
    (a : EuclideanSpace ℝ (Fin k)) :
    ((a : Fin k → ℝ) ⬝ᵥ fun i => fderiv ℝ g θ (EuclideanSpace.single i 1)) ^ 2 ≤
      ((a : Fin k → ℝ) ⬝ᵥ (Matrix.of fun i j : Fin k =>
          ∫ x, fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) *
            fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single j 1) / p θ x ∂ν) *ᵥ
          (a : Fin k → ℝ)) *
        ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν := by
  set D : 𝓧 → EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ := fun x => fderiv ℝ (fun θ' => p θ' x) θ
    with hD
  set s : Fin k → 𝓧 → ℝ := fun i x => D x (EuclideanSpace.single i 1) with hs
  -- `p θ` is integrable since its integral is `1`.
  have hp1 : ∫ x, p θ x ∂ν = 1 := hp_int.self_of_nhds
  have hpI : Integrable (p θ) ν := by
    by_contra h
    rw [integral_undef h] at hp1
    exact zero_ne_one hp1
  -- the gradient vanishes where the density does
  have hzero : ∀ x, p θ x = 0 → D x = 0 := fun x h0 => by
    have hmin : IsLocalMin (fun θ' => p θ' x) θ :=
      Eventually.of_forall fun θ' => by
        change p θ x ≤ p θ' x
        rw [h0]; exact hp_nonneg θ' x
    exact hmin.fderiv_eq_zero
  have hs0 : ∀ i x, p θ x = 0 → s i x = 0 := fun i x h0 => by
    simp [hs, hzero x h0]
  -- integrability of the scores and of their products divided by the density
  have hsI : ∀ i, Integrable (s i) ν := by
    intro i
    refine Integrable.mono' ((((hI_int i).add hpI).div_const 2)) (hs_meas i) ?_
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs]
    rcases (hp_nonneg θ x).eq_or_lt with h0 | hpos
    · rw [hs0 i x h0.symm, abs_zero]
      have : 0 ≤ s i x ^ 2 / p θ x := div_nonneg (sq_nonneg _) (hp_nonneg θ x)
      change 0 ≤ (s i x ^ 2 / p θ x + p θ x) / 2
      linarith [hp_nonneg θ x]
    · exact aux_abs_le _ _ hpos
  have hTsI : ∀ i, Integrable (fun x => T x * s i x) ν := by
    intro i
    refine Integrable.mono' ((hT_sq.add (hI_int i)).div_const 2)
      (hT_meas.mul (hs_meas i)) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    rcases (hp_nonneg θ x).eq_or_lt with h0 | hpos
    · change |T x * s i x| ≤ (T x ^ 2 * p θ x + s i x ^ 2 / p θ x) / 2
      rw [hs0 i x h0.symm, ← h0]
      simp
    · exact aux_abs_mul_le _ _ _ hpos
  have hqI : ∀ i j, Integrable (fun x => s i x * s j x / p θ x) ν := by
    intro i j
    have hm : AEStronglyMeasurable (fun x => s i x * s j x / p θ x) ν := by
      have e : (fun x => s i x * s j x / p θ x) =
          fun x => s i x ^ 2 / p θ x * s j x / s i x := by
        funext x
        rcases eq_or_ne (s i x) 0 with h | h
        · simp [h]
        · field_simp
      rw [e]
      exact (((hI_int i).aemeasurable.mul (hs_meas j).aemeasurable).div
        (hs_meas i).aemeasurable).aestronglyMeasurable
    refine Integrable.mono' (((hI_int i).add (hI_int j)).div_const 2) hm
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    change |s i x * s j x / p θ x| ≤ (s i x ^ 2 / p θ x + s j x ^ 2 / p θ x) / 2
    rcases (hp_nonneg θ x).eq_or_lt with h0 | hpos
    · simp [← h0]
    · exact aux_abs_div_le _ _ _ hpos
  -- the gradient of `p` as a combination of coordinate projections
  have hDsum : ∀ x, D x = ∑ i, s i x •
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) := fun x => clm_eq_sum (D x)
  have hDI : Integrable D ν := by
    have e : D = fun x => ∑ i, s i x •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) := funext hDsum
    rw [e]
    exact integrable_finsetSum (f := fun i x => s i x •
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)) _
      fun i _ => (hsI i).smul_const _
  have hTDI : Integrable (fun x => T x • D x) ν := by
    have e : (fun x => T x • D x) = fun x => ∑ i, (T x * s i x) •
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) := by
      funext x
      rw [hDsum x, Finset.smul_sum]
      simp only [smul_smul]
    rw [e]
    exact integrable_finsetSum (f := fun i x => (T x * s i x) •
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)) _
      fun i _ => (hTsI i).smul_const _
  have hDa : ∀ x, D x a = ∑ i, a i * s i x := fun x => clm_apply_eq_sum (D x) a
  -- the line `t ↦ θ + t a`
  set q : ℝ → 𝓧 → ℝ := fun t x => p (θ + t • a) x with hq
  have hline0 : θ = θ + (0 : ℝ) • a := by simp
  have hline : HasDerivAt (fun t : ℝ => θ + t • a) a 0 := by
    simpa using HasDerivAt.const_add θ (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) a)
  have htend : Tendsto (fun t : ℝ => θ + t • a) (𝓝 0) (𝓝 θ) := by
    have := (HasDerivAt.continuousAt hline).tendsto
    rwa [← hline0] at this
  have hq0 : ∀ x, q 0 x = p θ x := fun x => by simp [hq]
  have hderq : ∀ x, deriv (fun t => q t x) 0 = D x a := fun x =>
    HasDerivAt.deriv
      (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hp_diff x).hasFDerivAt hline hline0)
  have hsq_expand : ∀ x, deriv (fun t => q t x) 0 ^ 2 / q 0 x =
      ∑ i, ∑ j, a i * a j * (s i x * s j x / p θ x) := by
    intro x
    rw [hderq, hDa, hq0, sq, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- hypotheses of the one-parameter inequality along the line
  have hs_meas' : AEStronglyMeasurable (fun x => deriv (fun t => q t x) 0) ν := by
    have e : (fun x => deriv (fun t => q t x) 0) = fun x => ∑ i, a i * s i x := by
      funext x; rw [hderq, hDa]
    rw [e]
    exact (integrable_finsetSum (f := fun i x => a i * s i x) _
      fun i _ => (hsI i).const_mul (a i)).aestronglyMeasurable
  have hI_int' : Integrable (fun x => deriv (fun t => q t x) 0 ^ 2 / q 0 x) ν := by
    simp_rw [hsq_expand]
    exact integrable_finsetSum (f := fun i x => ∑ j, a i * a j * (s i x * s j x / p θ x)) _
      fun i _ => integrable_finsetSum (f := fun j x => a i * a j * (s i x * s j x / p θ x)) _
        fun j _ => (hqI i j).const_mul _
  have hT_sq' : Integrable (fun x => T x ^ 2 * q 0 x) ν := by
    simp_rw [hq0]; exact hT_sq
  have h_d1' : HasDerivAt (fun t => ∫ x, q t x ∂ν) (∫ x, deriv (fun t => q t x) 0 ∂ν) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h_deriv_one hline hline0
    rw [ContinuousLinearMap.integral_apply hDI] at h
    simp_rw [hderq]
    exact h
  have h_dT' : HasDerivAt (fun t => ∫ x, T x * q t x ∂ν)
      (∫ x, T x * deriv (fun t => q t x) 0 ∂ν) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h_deriv_T hline hline0
    rw [ContinuousLinearMap.integral_apply hTDI] at h
    simp only [_root_.smul_apply, smul_eq_mul] at h
    simp_rw [hderq]
    exact h
  have key := sq_deriv_le_fisherInformation_mul (p := q) (T := T)
    (g := fun t => g (θ + t • a)) (θ := 0) (fun t x => hp_nonneg _ x)
    (htend.eventually hp_int) hs_meas' hI_int' hT_meas hT_sq'
    (htend.eventually h_unbiased) h_d1' h_dT'
  -- identify the three quantities
  have hg : HasFDerivAt g (∫ x, T x • D x ∂ν) θ :=
    HasFDerivAt.congr_of_eventuallyEq h_deriv_T (h_unbiased.mono fun _ h => h.symm)
  have hgline : deriv (fun t : ℝ => g (θ + t • a)) 0 =
      (a : Fin k → ℝ) ⬝ᵥ fun i => fderiv ℝ g θ (EuclideanSpace.single i 1) := by
    have hc : deriv (fun t : ℝ => g (θ + t • a)) 0 = fderiv ℝ g θ a := by
      rw [HasFDerivAt.fderiv hg]
      exact HasDerivAt.deriv (HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hg hline hline0)
    rw [hc, clm_apply_eq_sum (fderiv ℝ g θ) a]
    rfl
  have hfish : fisherInformation ν q 0 =
      (a : Fin k → ℝ) ⬝ᵥ (Matrix.of fun i j : Fin k =>
          ∫ x, fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) *
            fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single j 1) / p θ x ∂ν) *ᵥ
          (a : Fin k → ℝ) := by
    rw [fisherInformation]
    simp_rw [hsq_expand]
    rw [integral_finsetSum _ fun i _ =>
      integrable_finsetSum (f := fun j x => a i * a j * (s i x * s j x / p θ x)) _
        fun j _ => (hqI i j).const_mul _]
    simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hqI i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring
  rw [hgline, hfish] at key
  simpa [hq0] using key

/-- **Cramér–Rao inequality for a real estimand of a vector parameter** (C. R. Rao, *Bull.
Calcutta Math. Soc.* 37 (1945) 81–91). Let `p θ'` (`θ' ∈ ℝ^k`) be nonnegative probability
densities with respect to `ν` for `θ'` near `θ`, differentiable in the parameter at `θ`, with
square-integrable partial scores `∂_i p θ / p θ` and positive definite Fisher information matrix
`I(θ)_{ij} = ∫ ∂_i p θ ∂_j p θ / p θ dν`. Let `T` be an estimator with finite second moment
under `p θ` that is unbiased for `g θ'` near `θ`, and suppose `∫ p θ' dν` and `∫ T p θ' dν`
can be differentiated under the integral sign at `θ`. Then
`∇g(θ)ᵀ I(θ)⁻¹ ∇g(θ) ≤ Var_θ T = ∫ (T - g θ)² p θ dν`. This is the bound for one real-valued
estimator `T`; the matrix form `Cov_θ(T) ⪰ J I(θ)⁻¹ Jᵀ` for vector estimators follows by applying
it to each `cᵀ T` but is not stated. For `k = 1` it corresponds to `FisherInformation.cramerRao`
under the identification of `ℝ¹` with `ℝ`. -/
theorem cramerRao_multiparameter {ν : Measure 𝓧} {p : EuclideanSpace ℝ (Fin k) → 𝓧 → ℝ}
    {T : 𝓧 → ℝ} {g : EuclideanSpace ℝ (Fin k) → ℝ} {θ : EuclideanSpace ℝ (Fin k)}
    (hp_nonneg : ∀ θ' x, 0 ≤ p θ' x)
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun θ' => p θ' x) θ)
    (hs_meas : ∀ i, AEStronglyMeasurable
      (fun x => fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1)) ν)
    (hI_int : ∀ i, Integrable
      (fun x => fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) ^ 2 / p θ x) ν)
    (hI_pos : (Matrix.of fun i j : Fin k =>
      ∫ x, fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) *
        fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single j 1) / p θ x ∂ν).PosDef)
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (h_deriv_one : HasFDerivAt (fun θ' => ∫ x, p θ' x ∂ν)
      (∫ x, fderiv ℝ (fun θ' => p θ' x) θ ∂ν) θ)
    (h_deriv_T : HasFDerivAt (fun θ' => ∫ x, T x * p θ' x ∂ν)
      (∫ x, T x • fderiv ℝ (fun θ' => p θ' x) θ ∂ν) θ) :
    (fun i => fderiv ℝ g θ (EuclideanSpace.single i 1)) ⬝ᵥ
        ((Matrix.of fun i j : Fin k =>
          ∫ x, fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) *
            fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single j 1) / p θ x ∂ν)⁻¹ *ᵥ
          (fun i => fderiv ℝ g θ (EuclideanSpace.single i 1))) ≤
      ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν := by
  set I : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j : Fin k =>
    ∫ x, fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single i 1) *
      fderiv ℝ (fun θ' => p θ' x) θ (EuclideanSpace.single j 1) / p θ x ∂ν with hI
  set G : Fin k → ℝ := fun i => fderiv ℝ g θ (EuclideanSpace.single i 1) with hG
  set V := ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν with hV
  set c := G ⬝ᵥ (I⁻¹ *ᵥ G) with hc
  have hV0 : 0 ≤ V := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hp_nonneg θ x)
  have hdet : IsUnit I.det := (Matrix.isUnit_iff_isUnit_det I).mp hI_pos.isUnit
  have key := sq_inner_le_quadForm_mul hp_nonneg hp_int hp_diff hs_meas hI_int hT_meas hT_sq
    h_unbiased h_deriv_one h_deriv_T (WithLp.toLp 2 (I⁻¹ *ᵥ G))
  have h1 : (I⁻¹ *ᵥ G) ⬝ᵥ G = c := by rw [hc, dotProduct_comm]
  have h2 : (I⁻¹ *ᵥ G) ⬝ᵥ (I *ᵥ (I⁻¹ *ᵥ G)) = c := by
    rw [mulVec_mulVec, mul_nonsing_inv I hdet, one_mulVec, h1]
  rw [h1, h2] at key
  rcases le_or_gt c 0 with hc0 | hc0
  · exact hc0.trans hV0
  · nlinarith

end MathlibExt.Probability.Statistics.MultiparameterCramerRao
