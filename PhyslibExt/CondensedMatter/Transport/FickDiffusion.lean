/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Continuum diffusion (Fick's laws) in one spatial dimension.

Overview
: Fick's first law with constant diffusivity `D`, the continuity equation, and
  the diffusion equation they imply; the full-line Gaussian and the semi-infinite
  complementary-error-function profiles; uniqueness on a bounded interval with
  Dirichlet data via the energy method; scaling similarity; the steady membrane
  flux; and the finite-slab Fourier sine series (coefficients, termwise bounds,
  and uniform convergence for positive time).

Key results
: `fick_continuity_imply_diffusion` (C1), `gauss_pde`, `gauss_mass`,
  `gauss_weak_limit`, `erfcProfile_pde`, `erfcProfile_surface`,
  `erfcProfile_farfield`, `erfcProfile_initial`, `erfcProfile_mass_strictMono`
  (C2), `diffusion_unique_dirichlet`, `similarity_pde`, `simVar_invariant` (C3),
  `steady_flux`, `fourierCoeff_formula`, `fourier_uniform_convergent` (C4).

References
: MIT OCW 3.21 Kinetic Processes in Materials, Spring 2006, lecture notes:
  "The Diffusion Equation", "Solutions to the Diffusion Equation I-III".
  DoITPoMS (Cambridge) TLP Library, "Diffusion" TLP.
  Balluffi, Allen & Carter, Kinetics of Materials (unverified standard text).

Units note
: Diffusivity units (m^2/s vs cm^2/s) are a conversion factor only; no
  unit-conversion theorem is stated. Mass/mole identifications below assume
  constant density wherever a mass appears; no wt% conversions are proved.

Non-goals
: General PDE existence; concentration-dependent `D`; multi-component or
  cross-diffusion; termwise differentiation of the Fourier series.
-/

open MeasureTheory Set Filter Topology Real

open scoped intervalIntegral

@[expose]
public section

namespace CondensedMatter.Diffusion

/-- Fick's first law in 1-D: `J = -D * ∂c/∂x` with constant `D`. -/
noncomputable def fickFlux (D : ℝ) (c : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ :=
  -D * deriv (fun x' => c x' t) x

/-- C1: Fick's first law with constant `D`, together with continuity
`∂c/∂t + ∂J/∂x = 0`, implies the diffusion equation `∂c/∂t = D * ∂²c/∂x²`.
Regularity is stated explicitly via `HasDerivAt` on the partial maps. The
conclusion is not claimed from Fick's law alone. -/
theorem fick_continuity_imply_diffusion (D : ℝ) (c : ℝ → ℝ → ℝ) (x t cxx' ct' : ℝ)
    (H2 : HasDerivAt (fun x' => deriv (fun x'' => c x'' t) x') cxx' x)
    (Ht : HasDerivAt (fun t' => c x t') ct' t)
    (Hcont : ct' + deriv (fun x' => fickFlux D c x' t) x = 0) :
    deriv (fun t' => c x t') t = D * cxx' := by
  have hJ : deriv (fun x' => fickFlux D c x' t) x = -D * cxx' :=
    (H2.const_mul (-D)).deriv
  rw [Ht.deriv]
  rw [hJ] at Hcont
  linarith

/-- Full-line finite-mass Gaussian with total mass `M` (a real parameter). -/
noncomputable def gauss (M D x t : ℝ) : ℝ :=
  (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-x ^ 2 / (4 * D * t))

/-- C2: first `x`-partial of the Gaussian. -/
theorem gauss_xderiv_value (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => gauss M D x t) (gauss M D x t * (-x / (2 * D * t))) x := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hs : (4 * D * t : ℝ) ≠ 0 := by positivity
  have hs2 : (2 * D * t : ℝ) ≠ 0 := by positivity
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hu : HasDerivAt (fun x : ℝ => -x ^ 2 / (4 * D * t)) (-(2 * x) / (4 * D * t)) x :=
    hpow.neg.div_const _
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2 / (4 * D * t)))
      (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t))) x := by
    simpa using hu.exp
  have hraw : HasDerivAt (fun x : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t)))
      ((M / Real.sqrt (4 * Real.pi * D * t)) *
        (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t)))) x := by
    simpa using hexp.const_mul _
  have hval : ((M / Real.sqrt (4 * Real.pi * D * t)) *
      (Real.exp (-x ^ 2 / (4 * D * t)) * (-(2 * x) / (4 * D * t))))
      = gauss M D x t * (-x / (2 * D * t)) := by
    simp only [gauss]
    field_simp
    ring
  rwa [hval] at hraw

/-- C2: second `x`-partial of the Gaussian. -/
theorem gauss_xxderiv_value (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => deriv (fun x' => gauss M D x' t) x)
      (gauss M D x t * (x ^ 2 / (4 * D ^ 2 * t ^ 2) - 1 / (2 * D * t))) x := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hs2 : (2 * D * t : ℝ) ≠ 0 := by positivity
  have h4D2t2 : (4 * D ^ 2 * t ^ 2 : ℝ) ≠ 0 := by positivity
  have hfun : (fun x => deriv (fun x' => gauss M D x' t) x)
      = (fun x => gauss M D x t * (-x / (2 * D * t))) := by
    funext x'
    exact (gauss_xderiv_value M D x' t hD ht).deriv
  rw [hfun]
  have hlin : HasDerivAt (fun x : ℝ => -x / (2 * D * t)) (-1 / (2 * D * t)) x := by
    simpa using (hasDerivAt_id' x).neg.div_const _
  have hmul : HasDerivAt (fun x : ℝ => gauss M D x t * (-x / (2 * D * t)))
      ((gauss M D x t * (-x / (2 * D * t))) * (-x / (2 * D * t))
        + gauss M D x t * (-1 / (2 * D * t))) x := by
    convert (gauss_xderiv_value M D x t hD ht).mul hlin using 1
  have hval : ((gauss M D x t * (-x / (2 * D * t))) * (-x / (2 * D * t))
      + gauss M D x t * (-1 / (2 * D * t)))
      = gauss M D x t * (x ^ 2 / (4 * D ^ 2 * t ^ 2) - 1 / (2 * D * t)) := by
    field_simp
    ring
  rwa [hval] at hmul

/-- C2: `t`-partial of the Gaussian. -/
theorem gauss_tderiv_value (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun t => gauss M D x t)
      (gauss M D x t * (x ^ 2 / (4 * D * t ^ 2) - 1 / (2 * t))) t := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hQ' : (4 * Real.pi * D * t : ℝ) ≠ 0 := ne_of_gt hQ
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have hden : HasDerivAt (fun t : ℝ => 4 * D * t) (4 * D) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * D)
  have hden' : (4 * D * t : ℝ) ≠ 0 := by positivity
  have hden2 : (4 * D * t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hden'
  have h2t : (2 * t : ℝ) ≠ 0 := by positivity
  have h4Dt2 : (4 * D * t ^ 2 : ℝ) ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht'
  have hS : HasDerivAt (fun t : ℝ => 4 * Real.pi * D * t) (4 * Real.pi * D) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * Real.pi * D)
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (4 * Real.pi * D * t))
      ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))) t :=
    hS.sqrt hQ'
  have hA : HasDerivAt (fun t : ℝ => M / Real.sqrt (4 * Real.pi * D * t))
      ((0 * Real.sqrt (4 * Real.pi * D * t)
        - M * ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))))
        / (Real.sqrt (4 * Real.pi * D * t)) ^ 2) t := by
    convert (hasDerivAt_const t M).div hsqrt hsq using 1
  have hexp_arg : HasDerivAt (fun t : ℝ => -x ^ 2 / (4 * D * t))
      ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2) t := by
    convert (hasDerivAt_const t (-x ^ 2)).div hden hden' using 1
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-x ^ 2 / (4 * D * t)))
      (Real.exp (-x ^ 2 / (4 * D * t))
        * ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2)) t := by
    simpa using hexp_arg.exp
  have hmul : HasDerivAt (fun t : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t)))
      (((0 * Real.sqrt (4 * Real.pi * D * t)
        - M * ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))))
        / (Real.sqrt (4 * Real.pi * D * t)) ^ 2) * Real.exp (-x ^ 2 / (4 * D * t))
        + (M / Real.sqrt (4 * Real.pi * D * t)) * (Real.exp (-x ^ 2 / (4 * D * t))
        * ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2))) t := by
    convert hA.mul hE using 1
  have hsqrt_inv : (Real.sqrt (4 * Real.pi * D * t))⁻¹
      = Real.sqrt (4 * Real.pi * D * t) / (4 * Real.pi * D * t) := by
    have hmul2 : Real.sqrt (4 * Real.pi * D * t) * Real.sqrt (4 * Real.pi * D * t)
        = 4 * Real.pi * D * t := by
      rw [← sq, Real.sq_sqrt hQ.le]
    rw [eq_div_iff hQ']
    calc (Real.sqrt (4 * Real.pi * D * t))⁻¹ * (4 * Real.pi * D * t)
        = (Real.sqrt (4 * Real.pi * D * t))⁻¹
          * (Real.sqrt (4 * Real.pi * D * t) * Real.sqrt (4 * Real.pi * D * t)) := by
          rw [hmul2]
      _ = Real.sqrt (4 * Real.pi * D * t) := by
          rw [← mul_assoc, inv_mul_cancel₀ hsq, one_mul]
  have hval : (((0 * Real.sqrt (4 * Real.pi * D * t)
      - M * ((4 * Real.pi * D) / (2 * Real.sqrt (4 * Real.pi * D * t))))
      / (Real.sqrt (4 * Real.pi * D * t)) ^ 2) * Real.exp (-x ^ 2 / (4 * D * t))
      + (M / Real.sqrt (4 * Real.pi * D * t)) * (Real.exp (-x ^ 2 / (4 * D * t))
      * ((0 * (4 * D * t) - (-x ^ 2) * (4 * D)) / (4 * D * t) ^ 2)))
      = gauss M D x t * (x ^ 2 / (4 * D * t ^ 2) - 1 / (2 * t)) := by
    simp only [gauss]
    rw [Real.sq_sqrt hQ.le]
    simp only [div_eq_mul_inv, mul_inv]
    rw [hsqrt_inv]
    field_simp
    ring
  have hgauss_eq : (fun t : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t))) = (fun t => gauss M D x t) := by
    funext t
    rfl
  rw [hval, hgauss_eq] at hmul
  exact hmul

/-- C2: the Gaussian satisfies the diffusion equation for `D > 0`, `t > 0`. -/
theorem gauss_pde (M D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun t => gauss M D x t) t
      = D * deriv (fun x => deriv (fun x' => gauss M D x' t) x) x := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have h2t : (2 * t : ℝ) ≠ 0 := by positivity
  have h2Dt : (2 * D * t : ℝ) ≠ 0 := by positivity
  have h4Dt2 : (4 * D * t ^ 2 : ℝ) ≠ 0 := by positivity
  have h4D2t2 : (4 * D ^ 2 * t ^ 2 : ℝ) ≠ 0 := by positivity
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht'
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD'
  rw [(gauss_tderiv_value M D x t hD ht).deriv, (gauss_xxderiv_value M D x t hD ht).deriv]
  field_simp

/-- C2: the Gaussian is nonnegative for positive mass. -/
theorem gauss_nonneg (M D x t : ℝ) (hM : 0 < M) (hD : 0 < D) (ht : 0 < t) :
    0 ≤ gauss M D x t := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have h1 : (0 : ℝ) ≤ M / Real.sqrt (4 * Real.pi * D * t) :=
    div_nonneg hM.le (Real.sqrt_pos.mpr hQ).le
  have h2 : (0 : ℝ) ≤ Real.exp (-x ^ 2 / (4 * D * t)) := (Real.exp_pos _).le
  simp only [gauss]
  exact mul_nonneg h1 h2

/-- C2: mass conservation on the full line, via Mathlib's Gaussian integral. -/
theorem gauss_mass (M D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    ∫ x, gauss M D x t = M := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
  have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  have h4Dt : (4 * D * t : ℝ) ≠ 0 := by positivity
  have hb : (0 : ℝ) < 1 / (4 * D * t) := by positivity
  have hker : ∀ x : ℝ, (-x ^ 2 / (4 * D * t)) = (-(1 / (4 * D * t)) * x ^ 2) := by
    intro x
    field_simp
  have hsmul : (fun x : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) *
      Real.exp (-x ^ 2 / (4 * D * t)))
      = (fun x : ℝ => (M / Real.sqrt (4 * Real.pi * D * t)) •
        Real.exp (-x ^ 2 / (4 * D * t))) := by
    funext x
    rw [smul_eq_mul]
  simp only [gauss]
  rw [hsmul, integral_smul, smul_eq_mul]
  simp_rw [hker]
  rw [integral_gaussian _]
  have hQ2 : Real.pi / (1 / (4 * D * t)) = 4 * Real.pi * D * t := by
    field_simp
  rw [hQ2]
  exact div_mul_cancel₀ M hsq

/-- C2: weak initial limit of the Gaussian against bounded continuous tests.
Proved for `M > 0`, the physical total-mass regime. The siblings `gauss_pde`
and `gauss_mass` hold for all `M` with no positivity needed; the limit itself
would extend to `M ≤ 0` by linearity, which is not proved here. -/
theorem gauss_weak_limit (M D : ℝ) (hM : 0 < M) (hD : 0 < D) (φ : ℝ → ℝ)
    (hφc : Continuous φ) (hφb : ∃ C, ∀ x, |φ x| ≤ C) :
    Tendsto (fun t => ∫ x, gauss M D x t * φ x) (𝓝[>] (0 : ℝ)) (𝓝 (M * φ 0)) := by
  obtain ⟨C, hC⟩ := hφb
  have hM' : M ≠ 0 := ne_of_gt hM
  have hD' : D ≠ 0 := ne_of_gt hD
  have hC' : ∀ x, |φ x| ≤ |C| + 1 := fun x => le_trans (hC x) (by
    calc C ≤ |C| := le_abs_self C
    _ ≤ |C| + 1 := by linarith)
  have hKint : ∀ (t : ℝ) (ht : 0 < t),
      Integrable (fun x => Real.exp (-(1 / (4 * D * t)) * x ^ 2)) := by
    intro t ht
    apply integrable_exp_neg_mul_sq
    positivity
  have hKt : ∀ (t : ℝ) (ht : 0 < t), Integrable (fun x => gauss M D x t) := by
    intro t ht
    have h4Dt : (4 * D * t : ℝ) ≠ 0 := by positivity
    have hker : ∀ x : ℝ, gauss M D x t
        = (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-(1 / (4 * D * t)) * x ^ 2) := by
      intro x
      simp only [gauss]
      have he : (-x ^ 2 / (4 * D * t)) = (-(1 / (4 * D * t)) * x ^ 2) := by
        field_simp
      rw [he]
    simp_rw [hker]
    simpa [smul_eq_mul] using (hKint t ht).const_mul _
  have hφ0K : ∀ (t : ℝ) (ht : 0 < t), Integrable (fun x => φ 0 * gauss M D x t) := by
    intro t ht
    simpa [smul_eq_mul] using (hKt t ht).const_mul _
  have hφKt : ∀ (t : ℝ) (ht : 0 < t), Integrable (fun x => gauss M D x t * φ x) := by
    intro t ht
    have hmeas : AEStronglyMeasurable φ volume := hφc.aestronglyMeasurable
    have hbdd : ∀ᵐ x ∂volume, ‖φ x‖ ≤ |C| + 1 := by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact hC' x
    have h : Integrable (fun x => φ x • gauss M D x t) := (hKt t ht).bdd_mul hmeas hbdd
    have heq : (fun x => φ x • gauss M D x t) = (fun x => gauss M D x t * φ x) := by
      funext x
      rw [smul_eq_mul, mul_comm]
    rwa [heq] at h
  have hfullint : ∀ (t : ℝ) (ht : 0 < t),
      Integrable (fun x => gauss M D x t * (φ x - φ 0)) := by
    intro t ht
    have h1 := hφKt t ht
    have h2 := hφ0K t ht
    have hsub : Integrable (fun x : ℝ => gauss M D x t * φ x - φ 0 * gauss M D x t) :=
      h1.sub h2
    have heq : (fun x : ℝ => gauss M D x t * φ x - φ 0 * gauss M D x t)
        = (fun x => gauss M D x t * (φ x - φ 0)) := by
      funext x
      ring
    rwa [heq] at hsub
  have hmass : ∀ (t : ℝ) (ht : 0 < t), ∫ x, gauss M D x t = M :=
    fun t ht => gauss_mass M D t hD ht
  have hdecomp : ∀ (t : ℝ) (ht : 0 < t),
      (∫ x, gauss M D x t * φ x) - M * φ 0
        = ∫ x, gauss M D x t * (φ x - φ 0) := by
    intro t ht
    have h1 := hφKt t ht
    have h2 := hφ0K t ht
    have hsub : (∫ x, gauss M D x t * φ x - φ 0 * gauss M D x t)
        = (∫ x, gauss M D x t * φ x) - ∫ x, φ 0 * gauss M D x t :=
      integral_sub h1 h2
    have hmassφ : (∫ x, φ 0 * gauss M D x t) = φ 0 * M := by
      have hsmul : (fun x : ℝ => φ 0 * gauss M D x t)
          = (fun x => φ 0 • gauss M D x t) := by
        funext x
        rw [smul_eq_mul]
      rw [hsmul, integral_smul, smul_eq_mul, hmass t ht]
    have hcongr : (∫ x, gauss M D x t * φ x - φ 0 * gauss M D x t)
        = ∫ x, gauss M D x t * (φ x - φ 0) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [← hcongr, hsub, hmassφ, mul_comm M (φ 0)]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεM : (0 : ℝ) < ε / (2 * M) := by positivity
  have hcont0 : ContinuousAt φ 0 := hφc.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousAt_iff.mp hcont0 (ε / (2 * M)) hεM
  have hsplit : ∀ (t : ℝ) (ht : 0 < t), (∫ x, gauss M D x t * (φ x - φ 0))
      = (∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))
        + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0) := by
    intro t ht
    exact (integral_add_compl measurableSet_Ioo (hfullint t ht)).symm
  have hnear : ∀ (t : ℝ) (ht : 0 < t),
      ‖(∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))‖ ≤ ε / 2 := by
    intro t ht
    have hpt : ∀ x ∈ Ioo (-δ) δ,
        ‖gauss M D x t * (φ x - φ 0)‖ ≤ gauss M D x t * (ε / (2 * M)) := by
      intro x hx
      have hxδ : |x| < δ := abs_lt.mpr (mem_Ioo.mp hx)
      have hdist : dist x 0 < δ := by
        rw [Real.dist_eq, sub_zero]
        exact hxδ
      have hφ := hδ hdist
      rw [Real.dist_eq] at hφ
      have hKnn : 0 ≤ gauss M D x t := gauss_nonneg M D x t hM hD ht
      calc ‖gauss M D x t * (φ x - φ 0)‖
          = |gauss M D x t| * |φ x - φ 0| := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ = gauss M D x t * |φ x - φ 0| := by rw [abs_of_nonneg hKnn]
        _ ≤ gauss M D x t * (ε / (2 * M)) :=
            mul_le_mul_of_nonneg_left (le_of_lt hφ) hKnn
    have hae : (fun x => ‖gauss M D x t * (φ x - φ 0)‖)
        ≤ᵐ[volume.restrict (Ioo (-δ) δ)]
        (fun x => gauss M D x t * (ε / (2 * M))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact hpt x hx
    have hInt : Integrable (fun x => gauss M D x t * (φ x - φ 0))
        (volume.restrict (Ioo (-δ) δ)) := (hfullint t ht).integrableOn
    have hnorm : IntegrableOn (fun x => ‖gauss M D x t * (φ x - φ 0)‖) (Ioo (-δ) δ) :=
      ((hfullint t ht).integrableOn : Integrable _ (volume.restrict (Ioo (-δ) δ))).norm
    have hconst : Integrable (fun x => gauss M D x t * (ε / (2 * M))) (volume.restrict (Ioo (-δ) δ)) := by
      have h := (((hKt t ht).integrableOn : Integrable _ (volume.restrict (Ioo (-δ) δ))).const_mul
        (ε / (2 * M)))
      have heq : (fun x : ℝ => (ε / (2 * M)) * gauss M D x t)
          = (fun x => gauss M D x t * (ε / (2 * M))) := by
        funext x
        ring
      simpa [smul_eq_mul, heq] using h
    have hpull : (∫ x in Ioo (-δ) δ, gauss M D x t * (ε / (2 * M)))
        = (ε / (2 * M)) * ∫ x in Ioo (-δ) δ, gauss M D x t := by
      have heq : (fun x : ℝ => gauss M D x t * (ε / (2 * M)))
          = (fun x => (ε / (2 * M)) • gauss M D x t) := by
        funext x
        rw [smul_eq_mul, mul_comm]
      rw [heq, integral_smul, smul_eq_mul]
    have hKle : (∫ x in Ioo (-δ) δ, gauss M D x t) ≤ M := by
      have hsp : (∫ x in Ioo (-δ) δ, gauss M D x t)
          + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t = ∫ x, gauss M D x t :=
        integral_add_compl measurableSet_Ioo (hKt t ht)
      have hnn : (0 : ℝ) ≤ ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t := by
        have hae0 : ∀ᵐ x ∂(volume.restrict ((Ioo (-δ) δ)ᶜ)),
            (0 : ℝ) ≤ gauss M D x t := by
          filter_upwards with x
          exact gauss_nonneg M D x t hM hD ht
        exact MeasureTheory.integral_nonneg_of_ae hae0
      rw [hmass t ht] at hsp
      linarith
    have hεMnn : (0 : ℝ) ≤ ε / (2 * M) := le_of_lt hεM
    calc ‖∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0)‖
        ≤ ∫ x in Ioo (-δ) δ, ‖gauss M D x t * (φ x - φ 0)‖ := by
          apply norm_integral_le_integral_norm <;> assumption
      _ ≤ ∫ x in Ioo (-δ) δ, gauss M D x t * (ε / (2 * M)) := by
          apply integral_mono_ae <;> assumption
      _ = (ε / (2 * M)) * ∫ x in Ioo (-δ) δ, gauss M D x t := hpull
      _ ≤ (ε / (2 * M)) * M := mul_le_mul_of_nonneg_left hKle hεMnn
      _ = ε / 2 := by
          field_simp
  have htail : ∀ (t : ℝ) (ht : 0 < t),
      (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t)
        ≤ M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
    intro t ht
    have hspos : (0 : ℝ) < 4 * D * t := by positivity
    have hs' : (4 * D * t : ℝ) ≠ 0 := ne_of_gt hspos
    have h2s' : (2 * (4 * D * t) : ℝ) ≠ 0 := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have hQ : (0 : ℝ) < 4 * Real.pi * D * t := by positivity
    have hsq : Real.sqrt (4 * Real.pi * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
    have hA : (0 : ℝ) ≤ M / Real.sqrt (4 * Real.pi * D * t) :=
      div_nonneg hM.le (Real.sqrt_pos.mpr hQ).le
    have hker2s : ∀ x : ℝ, (-x ^ 2 / (2 * (4 * D * t)))
        = (-(1 / (2 * (4 * D * t))) * x ^ 2) := by
      intro x
      field_simp
    have hb : (0 : ℝ) < 1 / (2 * (4 * D * t)) := by positivity
    have hbase : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
      simp_rw [hker2s]
      exact integrable_exp_neg_mul_sq hb
    have hpt : ∀ x ∈ (Ioo (-δ) δ)ᶜ, gauss M D x t
        ≤ (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
          * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      intro x hx
      simp only [Set.mem_compl_iff] at hx
      have hxδ : δ ≤ |x| := by
        by_contra hcon
        push Not at hcon
        exact hx (mem_Ioo.mpr (abs_lt.mp hcon))
      have hx2δ : δ ^ 2 ≤ x ^ 2 := by
        have h : δ ^ 2 ≤ |x| ^ 2 := by gcongr
        rwa [sq_abs x] at h
      have hexp_le : -x ^ 2 / (4 * D * t)
          ≤ (-δ ^ 2 + -x ^ 2) / (2 * (4 * D * t)) := by
        have h2s : (0 : ℝ) < 2 * (4 * D * t) := by positivity
        rw [le_div_iff₀ h2s]
        have hmul : (-x ^ 2 / (4 * D * t)) * (2 * (4 * D * t)) = -2 * x ^ 2 := by
          field_simp
        rw [hmul]
        linarith [hx2δ]
      have harg : -x ^ 2 / (4 * D * t)
          ≤ (-δ ^ 2 / (2 * (4 * D * t))) + (-x ^ 2 / (2 * (4 * D * t))) := by
        rw [← add_div]
        exact hexp_le
      have hexp_split : Real.exp (-x ^ 2 / (4 * D * t))
          ≤ Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
        calc Real.exp (-x ^ 2 / (4 * D * t))
            ≤ Real.exp ((-δ ^ 2 / (2 * (4 * D * t))) + (-x ^ 2 / (2 * (4 * D * t)))) :=
              Real.exp_le_exp.mpr harg
          _ = Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))) :=
              Real.exp_add _ _
      simp only [gauss]
      calc (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-x ^ 2 / (4 * D * t))
          ≤ (M / Real.sqrt (4 * Real.pi * D * t)) *
            (Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) :=
            mul_le_mul_of_nonneg_left hexp_split hA
        _ = (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
            * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by ring
    have hae : (fun x => gauss M D x t)
        ≤ᵐ[volume.restrict ((Ioo (-δ) δ)ᶜ)]
        (fun x => (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
          * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with x hx
      exact hpt x hx
    have hInt : IntegrableOn (fun x => gauss M D x t) ((Ioo (-δ) δ)ᶜ) :=
      (hKt t ht).integrableOn
    have hdom : Integrable
        (fun x => (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
          * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) (volume.restrict ((Ioo (-δ) δ)ᶜ)) := by
      have h := ((hbase.integrableOn : Integrable _ (volume.restrict ((Ioo (-δ) δ)ᶜ))).const_mul
        ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))))
      have heq : (fun x : ℝ => ((M / Real.sqrt (4 * Real.pi * D * t))
          * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))))
          = (fun x => (M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))
            * Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
        funext x
        ring
      simpa [smul_eq_mul, heq] using h
    have hmono : (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t)
        ≤ ∫ x in (Ioo (-δ) δ)ᶜ, (M / Real.sqrt (4 * Real.pi * D * t))
          * Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      apply integral_mono_ae <;> assumption
    have hpull : (∫ x in (Ioo (-δ) δ)ᶜ, (M / Real.sqrt (4 * Real.pi * D * t))
        * Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))))
        = ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t))))
          * ∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      have heq : (fun x : ℝ => (M / Real.sqrt (4 * Real.pi * D * t))
          * Real.exp (-δ ^ 2 / (2 * (4 * D * t))) * Real.exp (-x ^ 2 / (2 * (4 * D * t))))
          = (fun x => ((M / Real.sqrt (4 * Real.pi * D * t))
            * Real.exp (-δ ^ 2 / (2 * (4 * D * t)))) • Real.exp (-x ^ 2 / (2 * (4 * D * t)))) := by
        funext x
        rw [smul_eq_mul]
      rw [heq, integral_smul, smul_eq_mul]
    have hsub : (∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t))))
        ≤ ∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
      have hsp : (∫ x in Ioo (-δ) δ, Real.exp (-x ^ 2 / (2 * (4 * D * t))))
          + ∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t)))
          = ∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))) :=
        integral_add_compl measurableSet_Ioo hbase
      have hnn : (0 : ℝ) ≤ ∫ x in Ioo (-δ) δ, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
        have hae0 : ∀ᵐ x ∂(volume.restrict (Ioo (-δ) δ)),
            (0 : ℝ) ≤ Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
          filter_upwards with x
          exact (Real.exp_pos _).le
        exact MeasureTheory.integral_nonneg_of_ae hae0
      linarith
    have hgauss : (∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))))
        = Real.sqrt (2 * (4 * Real.pi * D * t)) := by
      simp_rw [hker2s]
      rw [integral_gaussian _]
      have hQ2 : Real.pi / (1 / (2 * (4 * D * t))) = 2 * (4 * Real.pi * D * t) := by
        field_simp
      rw [hQ2]
    have hEδ : Real.exp (-δ ^ 2 / (2 * (4 * D * t))) = Real.exp (-δ ^ 2 / (8 * D * t)) := by
      have h8 : (2 * (4 * D * t) : ℝ) = 8 * D * t := by ring
      rw [h8]
    have hsqrt8 : Real.sqrt (2 * (4 * Real.pi * D * t))
        = Real.sqrt 2 * Real.sqrt (4 * Real.pi * D * t) := by
      apply Real.sqrt_mul <;> positivity
    calc (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t)
        ≤ ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t))))
          * ∫ x in (Ioo (-δ) δ)ᶜ, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
          rwa [← hpull]
      _ ≤ ((M / Real.sqrt (4 * Real.pi * D * t)) * Real.exp (-δ ^ 2 / (2 * (4 * D * t))))
          * ∫ x, Real.exp (-x ^ 2 / (2 * (4 * D * t))) := by
          refine mul_le_mul_of_nonneg_left hsub ?_
          exact mul_nonneg hA (Real.exp_pos _).le
      _ = M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
          rw [hgauss, hEδ, hsqrt8]
          field_simp
  have htail_lim : Tendsto
      (fun t => 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have hpos : (0 : ℝ) < δ ^ 2 / (8 * D) := by positivity
    have hneg : (-δ ^ 2 / (8 * D)) < 0 := by
      rw [show (-δ ^ 2 / (8 * D)) = -(δ ^ 2 / (8 * D)) by ring]
      exact neg_lt_zero.mpr hpos
    have hmul := hinv.const_mul_atTop_of_neg hneg
    have heq : (fun t : ℝ => (-δ ^ 2 / (8 * D)) * t⁻¹)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun t => -δ ^ 2 / (8 * D * t)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : (0 : ℝ) < t := Set.mem_Ioi.mp ht
      have ht' : t ≠ 0 := ne_of_gt htpos
      have h8D : (8 * D : ℝ) ≠ 0 := by positivity
      have h8Dt : (8 * D * t : ℝ) ≠ 0 := by positivity
      field_simp
    have hatBot : Tendsto (fun t : ℝ => -δ ^ 2 / (8 * D * t)) (𝓝[>] (0 : ℝ)) atBot :=
      hmul.congr' heq
    have hexp0 := Real.tendsto_exp_atBot.comp hatBot
    have hfull := hexp0.const_mul (2 * (|C| + 1) * M * Real.sqrt 2)
    have heq2 : (fun t : ℝ => 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)))
        = (fun t => (2 * (|C| + 1) * M * Real.sqrt 2)
          * ((Real.exp ∘ (fun t => -δ ^ 2 / (8 * D * t))) t)) := by
      funext t
      rfl
    rw [heq2]
    simpa using hfull
  have hev := (Metric.tendsto_nhds.mp htail_lim) (ε / 2) (half_pos hε)
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff_ball.mp hev
  rw [eventually_nhdsWithin_iff]
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨η, hηpos, fun t htmem => ?_⟩
  intro htIoi
  have ht : (0 : ℝ) < t := Set.mem_Ioi.mp htIoi
  have hfar_lt : ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖ < ε / 2 := by
    have hfar_le : ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖
        ≤ 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
      have hpt2 : ∀ x ∈ (Ioo (-δ) δ)ᶜ,
          ‖gauss M D x t * (φ x - φ 0)‖ ≤ gauss M D x t * (2 * (|C| + 1)) := by
        intro x hx
        have hKnn : 0 ≤ gauss M D x t := gauss_nonneg M D x t hM hD ht
        have hφ2 : |φ x - φ 0| ≤ 2 * (|C| + 1) := by
          calc |φ x - φ 0| = |φ x + (-φ 0)| := by rw [sub_eq_add_neg]
            _ ≤ |φ x| + |-φ 0| := abs_add_le _ _
            _ = |φ x| + |φ 0| := by rw [abs_neg]
            _ ≤ 2 * (|C| + 1) := by linarith [hC' x, hC' 0]
        calc ‖gauss M D x t * (φ x - φ 0)‖
            = |gauss M D x t| * |φ x - φ 0| := by
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ = gauss M D x t * |φ x - φ 0| := by rw [abs_of_nonneg hKnn]
          _ ≤ gauss M D x t * (2 * (|C| + 1)) :=
              mul_le_mul_of_nonneg_left hφ2 hKnn
      have hae2 : (fun x => ‖gauss M D x t * (φ x - φ 0)‖)
          ≤ᵐ[volume.restrict ((Ioo (-δ) δ)ᶜ)]
          (fun x => gauss M D x t * (2 * (|C| + 1))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with x hx
        exact hpt2 x hx
      have hInt2 : Integrable (fun x => gauss M D x t * (φ x - φ 0))
          (volume.restrict ((Ioo (-δ) δ)ᶜ)) := (hfullint t ht).integrableOn
      have hnorm2 : IntegrableOn (fun x => ‖gauss M D x t * (φ x - φ 0)‖) ((Ioo (-δ) δ)ᶜ) :=
        ((hfullint t ht).integrableOn : Integrable _ (volume.restrict ((Ioo (-δ) δ)ᶜ))).norm
      have hconst2 : Integrable (fun x => gauss M D x t * (2 * (|C| + 1)))
          (volume.restrict ((Ioo (-δ) δ)ᶜ)) := by
        have h := (((hKt t ht).integrableOn : Integrable _ (volume.restrict ((Ioo (-δ) δ)ᶜ))).const_mul
          (2 * (|C| + 1)))
        have heq : (fun x : ℝ => (2 * (|C| + 1)) * gauss M D x t)
            = (fun x => gauss M D x t * (2 * (|C| + 1))) := by
          funext x
          ring
        simpa [smul_eq_mul, heq] using h
      have hpull2 : (∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (2 * (|C| + 1)))
          = (2 * (|C| + 1)) * ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t := by
        have heq : (fun x : ℝ => gauss M D x t * (2 * (|C| + 1)))
            = (fun x => (2 * (|C| + 1)) • gauss M D x t) := by
          funext x
          rw [smul_eq_mul, mul_comm]
        rw [heq, integral_smul, smul_eq_mul]
      calc ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖
          ≤ ∫ x in (Ioo (-δ) δ)ᶜ, ‖gauss M D x t * (φ x - φ 0)‖ := by
            apply norm_integral_le_integral_norm <;> assumption
        _ ≤ ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (2 * (|C| + 1)) := by
            apply integral_mono_ae <;> assumption
        _ = (2 * (|C| + 1)) * ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t := hpull2
        _ ≤ (2 * (|C| + 1)) * (M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t))) :=
            mul_le_mul_of_nonneg_left (htail t ht) (by positivity)
        _ = 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by ring
    have hbound_lt : dist (2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t))) 0
        < ε / 2 := hη t htmem htIoi
    have hbound_nn : (0 : ℝ)
        ≤ 2 * (|C| + 1) * M * Real.sqrt 2 * Real.exp (-δ ^ 2 / (8 * D * t)) := by
      positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbound_nn] at hbound_lt
    linarith [hfar_le, hbound_lt]
  have hnear_le := hnear t ht
  have hdecomp' : (∫ x, gauss M D x t * φ x) - M * φ 0
      = (∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))
        + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0) := by
    rw [hdecomp t ht, hsplit t ht]
  rw [Real.dist_eq, hdecomp']
  calc |(∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))
      + ∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)|
      ≤ |(∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0))|
        + |∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)| := abs_add_le _ _
    _ = ‖∫ x in Ioo (-δ) δ, gauss M D x t * (φ x - φ 0)‖
        + ‖∫ x in (Ioo (-δ) δ)ᶜ, gauss M D x t * (φ x - φ 0)‖ := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hnear_le hfar_lt
    _ = ε := add_halves ε

/-- Complementary error function, defined via the Gaussian integral
(Mathlib has no `erfc`; basic properties are proved from this definition). -/
noncomputable def erfc (x : ℝ) : ℝ :=
  1 - (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)

/-- First-derivative function of `erfc`. -/
noncomputable def erfcDeriv (x : ℝ) : ℝ :=
  -(2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2)

/-- Second-derivative function of `erfc`. -/
noncomputable def erfcDeriv2 (x : ℝ) : ℝ :=
  (4 * x / Real.sqrt Real.pi) * Real.exp (-x ^ 2)

/-- C2: `erfc 0 = 1`. -/
theorem erfc_zero : erfc 0 = 1 := by
  simp only [erfc, intervalIntegral.integral_same, mul_zero, sub_zero]

/-- C2: first derivative of `erfc` (fundamental theorem of calculus). -/
theorem hasDerivAt_erfc (x : ℝ) : HasDerivAt erfc (erfcDeriv x) x := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-t ^ 2)) :=
    Real.continuous_exp.comp ((continuous_id.pow 2).neg)
  have hFTC := hcont.integral_hasStrictDerivAt 0 x
  have h := (hFTC.hasDerivAt.const_mul (2 / Real.sqrt Real.pi)).const_sub 1
  have hval : (-((2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2))) = erfcDeriv x := by
    simp only [erfcDeriv]
    ring
  rwa [hval] at h

/-- C2: second derivative of `erfc`. -/
theorem hasDerivAt_erfcDeriv (x : ℝ) : HasDerivAt erfcDeriv (erfcDeriv2 x) x := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hu : HasDerivAt (fun x : ℝ => -x ^ 2) (-(2 * x)) x := hpow.neg
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x ^ 2))
      (Real.exp (-x ^ 2) * (-(2 * x))) x := by
    simpa using hu.exp
  have hraw : HasDerivAt (fun x : ℝ => -(2 / Real.sqrt Real.pi) * Real.exp (-x ^ 2))
      ((-(2 / Real.sqrt Real.pi)) * (Real.exp (-x ^ 2) * (-(2 * x)))) x := by
    simpa using hexp.const_mul (-(2 / Real.sqrt Real.pi))
  have hval : ((-(2 / Real.sqrt Real.pi)) * (Real.exp (-x ^ 2) * (-(2 * x))))
      = erfcDeriv2 x := by
    simp only [erfcDeriv2]
    ring
  rwa [hval] at hraw

/-- C2: `erfc` satisfies `erfc'' + 2x * erfc' = 0` (used for the PDE check). -/
theorem erfc_ode (x : ℝ) : erfcDeriv2 x + 2 * x * erfcDeriv x = 0 := by
  simp only [erfcDeriv, erfcDeriv2]
  ring

/-- C2: `erfc` is strictly decreasing on the whole line. -/
theorem erfc_strictAnti : StrictAntiOn erfc Set.univ := by
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), deriv erfc x < 0 := by
    intro x _
    have h := (hasDerivAt_erfc x).deriv
    rw [h]
    simp only [erfcDeriv]
    have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have he : (0 : ℝ) < Real.exp (-x ^ 2) := Real.exp_pos _
    have h2 : (0 : ℝ) < 2 / Real.sqrt Real.pi := div_pos (by norm_num) hpi
    have hAlt : (-(2 / Real.sqrt Real.pi)) < 0 := by linarith
    exact mul_neg_of_neg_of_pos hAlt he
  have hderiv' : ∀ x ∈ interior (Set.univ : Set ℝ), deriv erfc x < 0 := by
    intro x hx
    rw [interior_univ] at hx
    exact hderiv x hx
  have hconv : Convex ℝ (Set.univ : Set ℝ) := convex_univ
  have hcont : ContinuousOn erfc (Set.univ : Set ℝ) :=
    fun x _ => (hasDerivAt_erfc x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ erfc (Set.univ : Set ℝ) :=
    fun x _ => (hasDerivAt_erfc x).differentiableAt.differentiableWithinAt
  apply strictAntiOn_of_deriv_neg <;> assumption

/-- C2: the half-line Gaussian integral equals `√π / 2`. -/
theorem erfc_halfline :
    (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 := by
  have hker : ∀ t : ℝ, (-t ^ 2) = (-(1 : ℝ) * t ^ 2) := fun t => by ring
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hfull : (∫ t : ℝ, Real.exp (-t ^ 2)) = Real.sqrt Real.pi := by
    simp_rw [hker]
    have h := integral_gaussian (1 : ℝ)
    rw [div_one] at h
    exact h
  have hint : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hsymm : ∀ R : ℝ, (∫ x in -R..(0 : ℝ), Real.exp (-x ^ 2))
      = ∫ x in (0 : ℝ)..R, Real.exp (-x ^ 2) := by
    intro R
    have hcomp : (∫ x in -R..(0 : ℝ), Real.exp (-x ^ 2))
        = ∫ x in -R..(0 : ℝ), Real.exp (-(-x) ^ 2) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x
      intro _
      rw [neg_sq]
    rw [hcomp]
    have h : (∫ x in -R..(0 : ℝ), Real.exp (-(-x) ^ 2))
        = ∫ x in -(0 : ℝ)..-(-R), Real.exp (-x ^ 2) :=
      intervalIntegral.integral_comp_neg (fun x => Real.exp (-x ^ 2))
    simpa using h
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi 0) := hint.integrableOn
  have hIic : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Iic 0) := hint.integrableOn
  have hlimR : Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.exp (-x ^ 2)) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))) := by
    apply intervalIntegral_tendsto_integral_Ioi
    · assumption
    · exact tendsto_id
  have hlimL : Tendsto (fun R : ℝ => ∫ x in -R..(0 : ℝ), Real.exp (-x ^ 2)) atTop
      (𝓝 (∫ t in Set.Iic (0 : ℝ), Real.exp (-t ^ 2))) := by
    have h : Tendsto (fun R : ℝ => ∫ x in R..(0 : ℝ), Real.exp (-x ^ 2)) atBot
        (𝓝 (∫ t in Set.Iic (0 : ℝ), Real.exp (-t ^ 2))) := by
      apply intervalIntegral_tendsto_integral_Iic
      · assumption
      · exact tendsto_id
    have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
    have hc := h.comp hneg
    have heq : (fun R : ℝ => ∫ x in -R..(0 : ℝ), Real.exp (-x ^ 2))
        = ((fun R : ℝ => ∫ x in R..(0 : ℝ), Real.exp (-x ^ 2)) ∘ (fun R : ℝ => -R)) := by
      funext R
      rfl
    rwa [heq]
  have heq : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))
      = ∫ t in Set.Iic (0 : ℝ), Real.exp (-t ^ 2) := by
    have hfun : (fun R : ℝ => ∫ x in -R..(0 : ℝ), Real.exp (-x ^ 2))
        = (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.exp (-x ^ 2)) := funext hsymm
    rw [hfun] at hlimL
    exact tendsto_nhds_unique hlimR hlimL
  have hsplit : (∫ t in Set.Iic (0 : ℝ), Real.exp (-t ^ 2))
      + ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2) = ∫ t : ℝ, Real.exp (-t ^ 2) := by
    have h : (∫ t in Set.Iic (0 : ℝ), Real.exp (-t ^ 2))
        + ∫ t in (Set.Iic (0 : ℝ))ᶜ, Real.exp (-t ^ 2) = ∫ t : ℝ, Real.exp (-t ^ 2) :=
      integral_add_compl (s := Set.Iic (0 : ℝ)) (measurableSet_Iic (a := (0 : ℝ))) hint
    rwa [compl_Iic] at h
  rw [hfull] at hsplit
  linarith [heq, hsplit]

/-- C2: `erfc x → 0` as `x → ∞`. -/
theorem erfc_tendsto_atTop : Tendsto erfc atTop (𝓝 0) := by
  have hker : ∀ t : ℝ, (-t ^ 2) = (-(1 : ℝ) * t ^ 2) := fun t => by ring
  have hint : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi 0) := hint.integrableOn
  have hlim : Tendsto (fun x : ℝ => ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))) := by
    apply intervalIntegral_tendsto_integral_Ioi
    · assumption
    · exact tendsto_id
  have hmul := hlim.const_mul (2 / Real.sqrt Real.pi)
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub := h1.sub hmul
  have hcongr : Tendsto erfc atTop (𝓝 (1 - (2 / Real.sqrt Real.pi)
      * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))) := by
    have heq : erfc =ᶠ[atTop] ((fun _ : ℝ => 1) - fun x => (2 / Real.sqrt Real.pi)
        * ∫ t in (0 : ℝ)..x, Real.exp (-t ^ 2)) := by
      filter_upwards with x
      rfl
    exact hsub.congr' heq
  rw [erfc_halfline] at hcongr
  have hval : (1 : ℝ) - (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 0 := by
    have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
    ring
  rwa [hval] at hcongr

/-- Semi-infinite maintained-surface profile with surface concentration `cs`. -/
noncomputable def erfcProfile (cs D x t : ℝ) : ℝ :=
  cs * erfc (x / Real.sqrt (4 * D * t))

/-- C2: first `x`-partial of the `erfc` profile. -/
theorem erfcProfile_xderiv_value (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => erfcProfile cs D x t)
      ((cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))) x := by
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hu := (hasDerivAt_id' x).div_const (Real.sqrt (4 * D * t))
  have hcomp := (hasDerivAt_erfc (x / Real.sqrt (4 * D * t))).comp x hu
  have hchain := hcomp.const_mul cs
  change HasDerivAt (fun x => cs * erfc (x / Real.sqrt (4 * D * t)))
    ((cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))) x
  have hderiv : (cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))
      = cs * (erfcDeriv (x / Real.sqrt (4 * D * t)) * (1 / Real.sqrt (4 * D * t))) := by
    ring
  rw [hderiv]
  exact hchain

/-- C2: second `x`-partial of the `erfc` profile. -/
theorem erfcProfile_xxderiv_value (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun x => deriv (fun x' => erfcProfile cs D x' t) x)
      (cs * erfcDeriv2 (x / Real.sqrt (4 * D * t)) / (Real.sqrt (4 * D * t)) ^ 2) x := by
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs2 : (Real.sqrt (4 * D * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hs'
  have hfun : (fun x => deriv (fun x' => erfcProfile cs D x' t) x)
      = (fun x => (cs / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t))) := by
    funext x'
    exact (erfcProfile_xderiv_value cs D x' t hD ht).deriv
  rw [hfun]
  have hu := (hasDerivAt_id' x).div_const (Real.sqrt (4 * D * t))
  have hcomp := (hasDerivAt_erfcDeriv (x / Real.sqrt (4 * D * t))).comp x hu
  have hchain := hcomp.const_mul (cs / Real.sqrt (4 * D * t))
  have hderiv : cs * erfcDeriv2 (x / Real.sqrt (4 * D * t)) / (Real.sqrt (4 * D * t)) ^ 2
      = (cs / Real.sqrt (4 * D * t)) * (erfcDeriv2 (x / Real.sqrt (4 * D * t)) * (1 / Real.sqrt (4 * D * t))) := by
    field_simp [hs', hs2]
  rw [hderiv]
  exact hchain

/-- C2: `t`-partial of the `erfc` profile. -/
theorem erfcProfile_tderiv_value (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    HasDerivAt (fun t => erfcProfile cs D x t)
      (cs * (erfcDeriv (x / Real.sqrt (4 * D * t))
        * ((0 * Real.sqrt (4 * D * t) - x * ((4 * D) / (2 * Real.sqrt (4 * D * t))))
          / (Real.sqrt (4 * D * t)) ^ 2))) t := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have ht' : t ≠ 0 := ne_of_gt ht
  have h4Dt : (0 : ℝ) < 4 * D * t := by positivity
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h4Dt)
  have hs2 : (Real.sqrt (4 * D * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hs'
  have h2s : (2 * Real.sqrt (4 * D * t) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hs'
  have hlin : HasDerivAt (fun t : ℝ => 4 * D * t) (4 * D) t := by
    simpa using (hasDerivAt_id' t).const_mul (4 * D)
  have hsqrt := hlin.sqrt (show (fun t : ℝ => 4 * D * t) t ≠ 0 from ne_of_gt h4Dt)
  have hxi := (hasDerivAt_const t x).div hsqrt
    (show (fun t : ℝ => Real.sqrt (4 * D * t)) t ≠ 0 from hs')
  have hcomp := (hasDerivAt_erfc (x / Real.sqrt (4 * D * t))).comp t hxi
  have hchain := hcomp.const_mul cs
  show HasDerivAt (fun t => cs * erfc (x / Real.sqrt (4 * D * t)))
    (cs * (erfcDeriv (x / Real.sqrt (4 * D * t))
      * ((0 * Real.sqrt (4 * D * t) - x * ((4 * D) / (2 * Real.sqrt (4 * D * t))))
        / (Real.sqrt (4 * D * t)) ^ 2))) t
  convert hchain using 1 <;> (try rfl; try funext y; try simp only [Function.comp_apply, smul_eq_mul]; try rfl; push_cast; field_simp; ring)

/-- C2: the `erfc` profile satisfies the diffusion equation for `t > 0`. -/
theorem erfcProfile_pde (cs D x t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    deriv (fun t => erfcProfile cs D x t) t
      = D * deriv (fun x => deriv (fun x' => erfcProfile cs D x' t) x) x := by
  have hs' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hs2 : (Real.sqrt (4 * D * t)) ^ 2 ≠ 0 := pow_ne_zero 2 hs'
  have h2s : (2 * Real.sqrt (4 * D * t) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hs'
  have hD' : D ≠ 0 := ne_of_gt hD
  rw [(erfcProfile_tderiv_value cs D x t hD ht).deriv,
    (erfcProfile_xxderiv_value cs D x t hD ht).deriv]
  have hE2 : erfcDeriv2 (x / Real.sqrt (4 * D * t))
      = -2 * (x / Real.sqrt (4 * D * t)) * erfcDeriv (x / Real.sqrt (4 * D * t)) := by
    have hode := erfc_ode (x / Real.sqrt (4 * D * t))
    linarith
  rw [hE2]
  field_simp
  ring

/-- C2: maintained surface concentration. -/
theorem erfcProfile_surface (cs D t : ℝ) (ht : 0 < t) (hD : 0 < D) :
    erfcProfile cs D 0 t = cs := by
  simp only [erfcProfile]
  have h0 : (0 : ℝ) / Real.sqrt (4 * D * t) = 0 := zero_div _
  rw [h0, erfc_zero, mul_one]

/-- C2: far-field limit of the `erfc` profile. -/
theorem erfcProfile_farfield (cs D t : ℝ) (ht : 0 < t) (hD : 0 < D) :
    Tendsto (fun x => erfcProfile cs D x t) atTop (𝓝 0) := by
  have hs : (0 : ℝ) < Real.sqrt (4 * D * t) := Real.sqrt_pos.mpr (by positivity)
  have hsinv : (0 : ℝ) < (Real.sqrt (4 * D * t))⁻¹ := inv_pos.mpr hs
  have harg : Tendsto (fun x : ℝ => x / Real.sqrt (4 * D * t)) atTop atTop := by
    have hmul := tendsto_id.const_mul_atTop hsinv
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have herfc := erfc_tendsto_atTop.comp harg
  have hcs := herfc.const_mul cs
  have heq : (fun x : ℝ => erfcProfile cs D x t)
      = (fun x => cs * ((erfc ∘ (fun x => x / Real.sqrt (4 * D * t))) x)) := by
    funext x
    rfl
  rw [heq]
  simpa using hcs

/-- C2: initial condition of the `erfc` profile for `x > 0`. -/
theorem erfcProfile_initial (cs D x : ℝ) (hx : 0 < x) (hD : 0 < D) :
    Tendsto (fun t => erfcProfile cs D x t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have harg : Tendsto (fun t : ℝ => x / Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ)) atTop := by
    have hsqrt0 : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ)) := by
      have hcont : ContinuousAt (fun t : ℝ => Real.sqrt (4 * D * t)) 0 :=
        (Real.continuous_sqrt.comp (continuous_id.const_mul (4 * D))).continuousAt
      have hval : (fun t : ℝ => Real.sqrt (4 * D * t)) 0 = 0 := by simp
      have htend : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝 0)
          (𝓝 ((fun t : ℝ => Real.sqrt (4 * D * t)) 0)) := hcont
      have hlim : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun t : ℝ => Real.sqrt (4 * D * t)) (𝓝[>] (0 : ℝ))
            (𝓝 ((fun t : ℝ => Real.sqrt (4 * D * t)) 0)) :=
          htend.mono_left nhdsWithin_le_nhds
        rwa [hval] at h
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hlim, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : (0 : ℝ) < t := Set.mem_Ioi.mp ht
      have hpos : (0 : ℝ) < 4 * D * t := by positivity
      exact Real.sqrt_pos.mpr hpos
    have hinv : Tendsto (fun t : ℝ => (Real.sqrt (4 * D * t))⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.comp hsqrt0
    have hmul := hinv.const_mul_atTop hx
    have heq : (fun t : ℝ => x * (Real.sqrt (4 * D * t))⁻¹)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun t => x / Real.sqrt (4 * D * t)) := by
      filter_upwards with t
      exact (div_eq_mul_inv _ _).symm
    exact hmul.congr' heq
  have herfc := erfc_tendsto_atTop.comp harg
  have hcs := herfc.const_mul cs
  have heq : (fun t : ℝ => erfcProfile cs D x t)
      = (fun t => cs * ((erfc ∘ (fun t => x / Real.sqrt (4 * D * t))) t)) := by
    funext t
    rfl
  rw [heq]
  simpa using hcs

/-- C2: tail form of `erfc` for nonnegative arguments. -/
theorem erfc_tail (u : ℝ) (hu : 0 ≤ u) :
    erfc u = (2 / Real.sqrt Real.pi) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2) := by
  have hker : ∀ t : ℝ, (-t ^ 2) = (-(1 : ℝ) * t ^ 2) := fun t => by ring
  have hint : Integrable (fun t : ℝ => Real.exp (-t ^ 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hFIoc : (∫ t in (0 : ℝ)..u, Real.exp (-t ^ 2))
      = ∫ t in Set.Ioc 0 u, Real.exp (-t ^ 2) := intervalIntegral.integral_of_le hu
  have hunion : Set.Ioc (0 : ℝ) u ∪ Set.Ioi u = Set.Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx0, -⟩ | hxu)
      · exact hx0
      · exact lt_of_le_of_lt hu hxu
    · intro hx0
      rcases lt_or_ge x u with hxu | hxu
      · exact Or.inl ⟨hx0, le_of_lt hxu⟩
      · rcases eq_or_lt_of_le hxu with rfl | hux
        · exact Or.inl ⟨hx0, le_rfl⟩
        · exact Or.inr hux
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2))
      = (∫ t in Set.Ioc 0 u, Real.exp (-t ^ 2)) + ∫ t in Set.Ioi u, Real.exp (-t ^ 2) := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) u) (Set.Ioi u) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h1 : x ≤ u := (Set.mem_Ioc.mp hx1).2
      have h2 : u < x := Set.mem_Ioi.mp hx2
      linarith
    have hm1 : MeasurableSet (Set.Ioc (0 : ℝ) u) := measurableSet_Ioc
    have hm2 : MeasurableSet (Set.Ioi u) := measurableSet_Ioi
    have hU : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioc 0 u ∪ Set.Ioi u) :=
      hint.integrableOn
    have hIoc : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioc 0 u) := hint.integrableOn
    have hIoiu : IntegrableOn (fun t : ℝ => Real.exp (-t ^ 2)) (Set.Ioi u) := hint.integrableOn
    rw [← hunion]
    apply setIntegral_union <;> assumption
  have hC : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
  have hH : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t ^ 2)) = Real.sqrt Real.pi / 2 :=
    erfc_halfline
  have htail : (∫ t in Set.Ioi u, Real.exp (-t ^ 2))
      = Real.sqrt Real.pi / 2 - ∫ t in Set.Ioc 0 u, Real.exp (-t ^ 2) := by
    linarith [hsplit, hH]
  simp only [erfc]
  rw [hFIoc, ← hC, htail]
  ring

/-- C2: `erfc` is nonnegative on `[0, ∞)`. -/
theorem erfc_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ erfc u := by
  rw [erfc_tail u hu]
  have hC : (0 : ℝ) ≤ 2 / Real.sqrt Real.pi :=
    div_nonneg (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).le
  have hnn : (0 : ℝ) ≤ ∫ v in Set.Ioi u, Real.exp (-v ^ 2) := by
    have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioi u)), (0 : ℝ) ≤ Real.exp (-v ^ 2) := by
      filter_upwards with v
      exact (Real.exp_pos _).le
    exact integral_nonneg_of_ae hae
  exact mul_nonneg hC hnn

/-- C2: Gaussian upper bound for `erfc` on `[0, ∞)`. -/
theorem erfc_le_gauss (u : ℝ) (hu : 0 ≤ u) :
    erfc u ≤ 2 * Real.sqrt 2 * Real.exp (-u ^ 2 / 2) := by
  have hker : ∀ v : ℝ, (-v ^ 2 / 2) = (-(1 / 2 : ℝ) * v ^ 2) := fun v => by ring
  have hgauss : (∫ v : ℝ, Real.exp (-v ^ 2 / 2)) = Real.sqrt (2 * Real.pi) := by
    simp_rw [hker]
    have h := integral_gaussian (1 / 2 : ℝ)
    have hQ : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by
      field_simp
    rw [hQ] at h
    exact h
  have hint : Integrable (fun v : ℝ => Real.exp (-v ^ 2 / 2)) := by
    simp_rw [hker]
    apply integrable_exp_neg_mul_sq
    norm_num
  have hpt : ∀ v ∈ Set.Ioi u, Real.exp (-v ^ 2)
      ≤ Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2) := by
    intro v hv
    have hvu : u ≤ v := le_of_lt (Set.mem_Ioi.mp hv)
    have h2 : u ^ 2 ≤ v ^ 2 := by gcongr
    have harg : -v ^ 2 ≤ (-u ^ 2 / 2) + (-v ^ 2 / 2) := by linarith [h2]
    calc Real.exp (-v ^ 2) ≤ Real.exp ((-u ^ 2 / 2) + (-v ^ 2 / 2)) :=
          Real.exp_le_exp.mpr harg
      _ = Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2) := Real.exp_add _ _
  have hae : (fun v => Real.exp (-v ^ 2))
      ≤ᵐ[volume.restrict (Set.Ioi u)]
      (fun v => Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hpt v hv
  have hInt : IntegrableOn (fun v => Real.exp (-v ^ 2)) (Set.Ioi u) := by
    have hker1 : ∀ v : ℝ, (-v ^ 2) = (-(1 : ℝ) * v ^ 2) := fun v => by ring
    have hfull : Integrable (fun v : ℝ => Real.exp (-v ^ 2)) := by
      simp_rw [hker1]
      apply integrable_exp_neg_mul_sq
      norm_num
    exact hfull.integrableOn
  have hdom : Integrable
      (fun v => Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2)) (volume.restrict (Set.Ioi u)) := by
    simpa [smul_eq_mul] using
      ((hint.integrableOn : Integrable _ (volume.restrict (Set.Ioi u))).const_mul _)
  have hmono : (∫ v in Set.Ioi u, Real.exp (-v ^ 2))
      ≤ ∫ v in Set.Ioi u, Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2) := by
    apply integral_mono_ae <;> assumption
  have hpull : (∫ v in Set.Ioi u, Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2))
      = Real.exp (-u ^ 2 / 2) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2) := by
    have heq : (fun v : ℝ => Real.exp (-u ^ 2 / 2) * Real.exp (-v ^ 2 / 2))
        = (fun v => Real.exp (-u ^ 2 / 2) • Real.exp (-v ^ 2 / 2)) := by
      funext v
      rw [smul_eq_mul]
    rw [heq, integral_smul, smul_eq_mul]
  have hsub : (∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2))
      ≤ ∫ v, Real.exp (-v ^ 2 / 2) := by
    have hsp : (∫ v in (Set.Ioi u)ᶜ, Real.exp (-v ^ 2 / 2))
        + ∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2) = ∫ v, Real.exp (-v ^ 2 / 2) := by
      have h := integral_add_compl (s := Set.Ioi u) measurableSet_Ioi hint
      linarith
    have hnn : (0 : ℝ) ≤ ∫ v in (Set.Ioi u)ᶜ, Real.exp (-v ^ 2 / 2) := by
      have hae0 : ∀ᵐ v ∂(volume.restrict ((Set.Ioi u)ᶜ)),
          (0 : ℝ) ≤ Real.exp (-v ^ 2 / 2) := by
        filter_upwards with v
        exact (Real.exp_pos _).le
      exact integral_nonneg_of_ae hae0
    linarith
  rw [erfc_tail u hu]
  calc (2 / Real.sqrt Real.pi) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2)
      ≤ (2 / Real.sqrt Real.pi)
        * (Real.exp (-u ^ 2 / 2) * ∫ v in Set.Ioi u, Real.exp (-v ^ 2 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).le)
        rw [← hpull]
        exact hmono
    _ ≤ (2 / Real.sqrt Real.pi) * (Real.exp (-u ^ 2 / 2) * ∫ v, Real.exp (-v ^ 2 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos).le)
        exact mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le
    _ = 2 * Real.sqrt 2 * Real.exp (-u ^ 2 / 2) := by
        rw [hgauss]
        have h2nn : (0 : ℝ) ≤ 2 := by norm_num
        have hpin : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
        have hsqrt2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
          apply Real.sqrt_mul <;> assumption
        rw [hsqrt2]
        have hsq : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
        field_simp

/-- C2: the `erfc` profile is integrable on `[0, ∞)`. -/
theorem erfcProfile_integrableOn (cs D t : ℝ) (hcs : 0 < cs) (hD : 0 < D) (ht : 0 < t) :
    IntegrableOn (fun x => erfcProfile cs D x t) (Set.Ioi 0) := by
  have ha : (0 : ℝ) < Real.sqrt (4 * D * t) := Real.sqrt_pos.mpr (by positivity)
  have ha' : Real.sqrt (4 * D * t) ≠ 0 := ne_of_gt ha
  have h2a2 : (2 * (Real.sqrt (4 * D * t)) ^ 2 : ℝ) ≠ 0 := by positivity
  have hb : (0 : ℝ) < 1 / (2 * (Real.sqrt (4 * D * t)) ^ 2) := by positivity
  have hker : ∀ x : ℝ, (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))
      = (-(1 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) * x ^ 2) := by
    intro x
    field_simp
  have hbase : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))) := by
    simp_rw [hker]
    exact integrable_exp_neg_mul_sq hb
  have hdom : Integrable (fun x : ℝ => cs * 2 * Real.sqrt 2
      * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))) := by
    simpa [smul_eq_mul] using hbase.const_mul (cs * 2 * Real.sqrt 2)
  have hcont : Continuous (fun x : ℝ => erfcProfile cs D x t) := by
    have herfc : Continuous erfc := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (hasDerivAt_erfc x).continuousAt
    exact (herfc.comp (continuous_id.div_const (Real.sqrt (4 * D * t)))).const_mul cs
  have hmeas : AEStronglyMeasurable (fun x => erfcProfile cs D x t)
      (volume.restrict (Set.Ioi 0)) :=
    hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖erfcProfile cs D x t‖ ≤ cs * 2 * Real.sqrt 2
        * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (Set.mem_Ioi.mp hx)
    have hu : (0 : ℝ) ≤ x / Real.sqrt (4 * D * t) := div_nonneg hx0 ha.le
    have hle := erfc_le_gauss (x / Real.sqrt (4 * D * t)) hu
    have hexp_eq : (-(x / Real.sqrt (4 * D * t)) ^ 2 / 2)
        = (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := by
      field_simp
    rw [hexp_eq] at hle
    have hnn : 0 ≤ erfcProfile cs D x t :=
      mul_nonneg hcs.le (erfc_nonneg _ hu)
    calc ‖erfcProfile cs D x t‖ = |erfcProfile cs D x t| := Real.norm_eq_abs _
      _ = erfcProfile cs D x t := abs_of_nonneg hnn
      _ = cs * erfc (x / Real.sqrt (4 * D * t)) := rfl
      _ ≤ cs * (2 * Real.sqrt 2 * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2))) :=
          mul_le_mul_of_nonneg_left hle hcs.le
      _ = cs * 2 * Real.sqrt 2 * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := by ring
  have hdomR : Integrable (fun x : ℝ => cs * 2 * Real.sqrt 2
      * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)))
      (volume.restrict (Set.Ioi 0)) := hdom.integrableOn
  have hbound' : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)), ‖erfcProfile cs D x t‖ ≤ cs * 2 * Real.sqrt 2 * Real.exp (-x ^ 2 / (2 * (Real.sqrt (4 * D * t)) ^ 2)) := hbound
  exact Integrable.mono' hdomR hmeas hbound'

/-- C2: pointwise strict increase of the profile in time for `x > 0`. -/
theorem profile_pointwise_lt (cs D x t₁ t₂ : ℝ) (hx : 0 < x) (hcs : 0 < cs) (hD : 0 < D)
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (h12 : t₁ < t₂) :
    erfcProfile cs D x t₁ < erfcProfile cs D x t₂ := by
  have ha : Real.sqrt (4 * D * t₁) < Real.sqrt (4 * D * t₂) := by
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    have h4D : (0 : ℝ) < 4 * D := by positivity
    exact mul_lt_mul_of_pos_left h12 h4D
  have ha1 : (0 : ℝ) < Real.sqrt (4 * D * t₁) := Real.sqrt_pos.mpr (by positivity)
  have ha2 : (0 : ℝ) < Real.sqrt (4 * D * t₂) := Real.sqrt_pos.mpr (by positivity)
  have harg : x / Real.sqrt (4 * D * t₂) < x / Real.sqrt (4 * D * t₁) := by
    gcongr
  have herfc := erfc_strictAnti (Set.mem_univ _) (Set.mem_univ _) harg
  simp only [erfcProfile]
  exact mul_lt_mul_of_pos_left herfc hcs

/-- C2: mass on `[0, ∞)` is strictly increasing in `t` (proved form).
Mass is conserved only under no-flux/decay boundaries; the maintained-surface
problem gains mass through its boundary. The exact value `2 cs √(Dt/π)` is not
proved here. -/
theorem erfcProfile_mass_strictMono (cs D : ℝ) (hcs : 0 < cs) (hD : 0 < D) :
    StrictMonoOn (fun t => ∫ x in Set.Ioi (0 : ℝ), erfcProfile cs D x t) (Set.Ioi (0 : ℝ)) := by
  intro t₁ ht₁ t₂ ht₂ h12
  have ht₁' : (0 : ℝ) < t₁ := Set.mem_Ioi.mp ht₁
  have ht₂' : (0 : ℝ) < t₂ := Set.mem_Ioi.mp ht₂
  have hint1 := erfcProfile_integrableOn cs D t₁ hcs hD ht₁'
  have hint2 := erfcProfile_integrableOn cs D t₂ hcs hD ht₂'
  have hsub : (∫ x in Set.Ioi (0 : ℝ), erfcProfile cs D x t₂)
      - ∫ x in Set.Ioi (0 : ℝ), erfcProfile cs D x t₁
      = ∫ x in Set.Ioi (0 : ℝ), (erfcProfile cs D x t₂ - erfcProfile cs D x t₁) := by
    have g1 : Integrable (fun x => erfcProfile cs D x t₁) (volume.restrict (Set.Ioi 0)) := hint1
    have g2 : Integrable (fun x => erfcProfile cs D x t₂) (volume.restrict (Set.Ioi 0)) := hint2
    exact (integral_sub g2 g1).symm
  suffices hpos : (0 : ℝ)
      < ∫ x in Set.Ioi (0 : ℝ), (erfcProfile cs D x t₂ - erfcProfile cs D x t₁) by
    linarith [hsub]
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (0 : ℝ) ≤ erfcProfile cs D x t₂ - erfcProfile cs D x t₁ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (0 : ℝ) < x := Set.mem_Ioi.mp hx
    have hlt := profile_pointwise_lt cs D x t₁ t₂ hx' hcs hD ht₁' ht₂' h12
    linarith
  have hint_sub : Integrable (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have g1 : Integrable (fun x => erfcProfile cs D x t₁) (volume.restrict (Set.Ioi 0)) := hint1
    have g2 : Integrable (fun x => erfcProfile cs D x t₂) (volume.restrict (Set.Ioi 0)) := hint2
    exact g2.sub g1
  have hiff : (0 : ℝ) < ∫ x in Set.Ioi (0 : ℝ), (erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
      ↔ 0 < (volume.restrict (Set.Ioi (0 : ℝ)))
        (Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)) :=
    integral_pos_iff_support_of_nonneg_ae hnn hint_sub
  have hsupp_pos : (0 : ENNReal) < (volume.restrict (Set.Ioi (0 : ℝ)))
      (Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)) := by
    have hsub2 : Set.Ioo (1 / 2 : ℝ) 1
        ⊆ Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
          ∩ Set.Ioi (0 : ℝ) := by
      intro x hx
      have hx1 : (1 / 2 : ℝ) < x := (Set.mem_Ioo.mp hx).1
      have hx' : (0 : ℝ) < x := by linarith
      have hlt := profile_pointwise_lt cs D x t₁ t₂ hx' hcs hD ht₁' ht₂' h12
      constructor
      · rw [Function.mem_support]
        exact ne_of_gt (by linarith [hlt] : (0 : ℝ) < erfcProfile cs D x t₂ - erfcProfile cs D x t₁)
      · exact Set.mem_Ioi.mpr hx'
    have hmeas : volume (Set.Ioo (1 / 2 : ℝ) 1) = ENNReal.ofReal (1 - 1 / 2) := Real.volume_Ioo
    have h1 : volume (Set.Ioo (1 / 2 : ℝ) 1)
        ≤ (volume.restrict (Set.Ioi (0 : ℝ)))
          (Function.support (fun x => erfcProfile cs D x t₂ - erfcProfile cs D x t₁)) := by
      rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi]
      exact measure_mono hsub2
    have h2 : (0 : ENNReal) < volume (Set.Ioo (1 / 2 : ℝ) 1) := by
      rw [hmeas]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    exact lt_of_lt_of_le h2 h1
  exact hiff.mpr hsupp_pos

/-- C3: energy identity in derivative form (Dirichlet BCs, energy method).
Regularity and the PDE are hypotheses on the strip `Icc a b ×ˢ univ`. -/
theorem energy_identity_deriv (a b D : ℝ) (hab : a < b) (hD : 0 < D)
    (c₁ c₂ w wx wxx wt : ℝ → ℝ → ℝ)
    (hw_def : ∀ x t, w x t = c₁ x t - c₂ x t)
    (ht : ∀ x t, HasDerivAt (fun τ => w x τ) (wt x t) t)
    (hx : ∀ x t, HasDerivAt (fun u => w u t) (wx x t) x)
    (hxx : ∀ x t, HasDerivAt (fun u => wx u t) (wxx x t) x)
    (hw_cont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hwx_cont : ContinuousOn (fun p : ℝ × ℝ => wx p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hwxx_cont : ContinuousOn (fun p : ℝ × ℝ => wxx p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hwt_cont : ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hpde : ∀ x ∈ Set.Icc a b, ∀ t, wt x t = D * wxx x t)
    (hbc : ∀ t, w a t = 0 ∧ w b t = 0) :
    ∀ t₀, HasDerivAt (fun t => ∫ x in Set.Ioc a b, (w x t) ^ 2)
      (-2 * D * ∫ x in Set.Ioc a b, (wx x t₀) ^ 2) t₀ := by
  intro t₀
  have hsq : ∀ a' x : ℝ, HasDerivAt (fun τ => (w a' τ) ^ 2) (2 * w a' x * wt a' x) x := by
    intro a' x
    have h := (ht a' x).mul (ht a' x)
    have heq : (fun τ : ℝ => w a' τ * w a' τ) = (fun τ => (w a' τ) ^ 2) := by
      funext τ
      rw [pow_two]
    have hval : wt a' x * w a' x + w a' x * wt a' x = 2 * w a' x * wt a' x := by ring
    have hclean : HasDerivAt (fun τ : ℝ => w a' τ * w a' τ)
        (wt a' x * w a' x + w a' x * wt a' x) x := h
    rwa [heq, hval] at hclean
  have hKcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc (t₀ - 1) (t₀ + 1)) :=
    IsCompact.prod isCompact_Icc isCompact_Icc
  have hKsub : Set.Icc a b ×ˢ Set.Icc (t₀ - 1) (t₀ + 1) ⊆ Set.Icc a b ×ˢ Set.univ := by
    intro p hp
    rw [mem_prod] at hp ⊢
    exact ⟨hp.1, mem_univ _⟩
  have hF'cont : ContinuousOn (fun p : ℝ × ℝ => 2 * w p.1 p.2 * wt p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc (t₀ - 1) (t₀ + 1)) := by
    have hw2 := hw_cont.mono hKsub
    have hwt2 := hwt_cont.mono hKsub
    have hmul := hw2.mul hwt2
    have h := hmul.const_mul 2
    apply h.congr
    intro p hp
    change 2 * w p.1 p.2 * wt p.1 p.2 = 2 * (w p.1 p.2 * wt p.1 p.2)
    ring
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hF'cont
  have hε : (0 : NNReal) < 1 := one_pos
  have hcont_slice : ∀ x : ℝ, ContinuousOn (fun a => (w a x) ^ 2) (Set.Ioc a b) := by
    intro x
    have hwx : ContinuousOn (fun a => w a x) (Set.Ioc a b) :=
      hw_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun y hy => by
        change (y, x) ∈ Set.Icc a b ×ˢ Set.univ
        rw [mem_prod]
        exact ⟨Set.Ioc_subset_Icc_self hy, mem_univ _⟩)
    exact hwx.pow 2
  have hcont_slice' : ∀ x : ℝ, ContinuousOn (fun a => 2 * w a x * wt a x) (Set.Ioc a b) := by
    intro x
    have hwx : ContinuousOn (fun a => w a x) (Set.Ioc a b) :=
      hw_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun y hy => by
        change (y, x) ∈ Set.Icc a b ×ˢ Set.univ
        rw [mem_prod]
        exact ⟨Set.Ioc_subset_Icc_self hy, mem_univ _⟩)
    have hwt : ContinuousOn (fun a => wt a x) (Set.Ioc a b) :=
      hwt_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun y hy => by
        change (y, x) ∈ Set.Icc a b ×ˢ Set.univ
        rw [mem_prod]
        exact ⟨Set.Ioc_subset_Icc_self hy, mem_univ _⟩)
    have h := (hwx.mul hwt).const_mul 2
    apply h.congr
    intro a ha
    change 2 * w a x * wt a x = 2 * (w a x * wt a x)
    ring
  have hFmeas : ∀ᶠ x in 𝓝 t₀, AEStronglyMeasurable (fun a => (w a x) ^ 2)
      (volume.restrict (Set.Ioc a b)) := by
    filter_upwards with x
    exact (hcont_slice x).aestronglyMeasurable measurableSet_Ioc
  have hF'meas : ∀ᶠ x in 𝓝 t₀, AEStronglyMeasurable (fun a => 2 * w a x * wt a x)
      (volume.restrict (Set.Ioc a b)) := by
    filter_upwards with x
    exact (hcont_slice' x).aestronglyMeasurable measurableSet_Ioc
  have h_deriv_pf : ∀ᵐ a ∂(volume.restrict (Set.Ioc a b)),
      ∀ x ∈ Metric.ball t₀ ((1 : NNReal) : ℝ),
        HasDerivAt (fun τ => (w a τ) ^ 2) (2 * w a x * wt a x) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    intro x _
    exact hsq a x
  have h_bound_pf : ∀ᵐ a ∂(volume.restrict (Set.Ioc a b)),
      ∀ x ∈ Metric.ball t₀ ((1 : NNReal) : ℝ), ‖2 * w a x * wt a x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    intro x hx
    have hxIcc : x ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
      have hdist : dist x t₀ < 1 := Metric.mem_ball.mp hx
      rw [Real.dist_eq] at hdist
      have habs : |x - t₀| < 1 := hdist
      rw [abs_lt] at habs
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hyIcc : y ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hy
    have hmem : (y, x) ∈ Set.Icc a b ×ˢ Set.Icc (t₀ - 1) (t₀ + 1) := ⟨hyIcc, hxIcc⟩
    exact hC (y, x) hmem
  have h_int_pf : Integrable (fun _ : ℝ => C) (volume.restrict (Set.Ioc a b)) := by
    have hCcont : ContinuousOn (fun _ : ℝ => C) (Set.Icc a b) := continuousOn_const
    have hIcc : IntegrableOn (fun _ : ℝ => C) (Set.Icc a b) volume :=
      hCcont.integrableOn_compact isCompact_Icc
    exact hIcc.mono_set Set.Ioc_subset_Icc_self
  have hcont_Icc_sq : ContinuousOn (fun y => (w y t₀) ^ 2) (Set.Icc a b) := by
    have hwc : ContinuousOn (fun y => w y t₀) (Set.Icc a b) :=
      hw_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun y hy => by
        change (y, t₀) ∈ Set.Icc a b ×ˢ Set.univ
        rw [mem_prod]
        exact ⟨hy, mem_univ _⟩)
    exact hwc.pow 2
  have hFint : Integrable (fun a => (w a t₀) ^ 2) (volume.restrict (Set.Ioc a b)) := by
    obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_Icc_sq
    have hC₂int : Integrable (fun _ : ℝ => C₂) (volume.restrict (Set.Ioc a b)) := by
      have hCcont : ContinuousOn (fun _ : ℝ => C₂) (Set.Icc a b) := continuousOn_const
      have hIcc : IntegrableOn (fun _ : ℝ => C₂) (Set.Icc a b) volume :=
        hCcont.integrableOn_compact isCompact_Icc
      exact hIcc.mono_set Set.Ioc_subset_Icc_self
    have hmeas : AEStronglyMeasurable (fun a => (w a t₀) ^ 2)
        (volume.restrict (Set.Ioc a b)) :=
      (hcont_slice t₀).aestronglyMeasurable measurableSet_Ioc
    have hbdd : ∀ᵐ y ∂(volume.restrict (Set.Ioc a b)), ‖(w y t₀) ^ 2‖ ≤ C₂ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact hC₂ y (Set.Ioc_subset_Icc_self hy)
    exact hC₂int.mono' hmeas hbdd
  have hF'0 : AEStronglyMeasurable (fun a => 2 * w a t₀ * wt a t₀)
      (volume.restrict (Set.Ioc a b)) :=
    (hcont_slice' t₀).aestronglyMeasurable measurableSet_Ioc
  have hsball : Metric.ball t₀ ((1 : NNReal) : ℝ) ∈ 𝓝 t₀ :=
    Metric.ball_mem_nhds t₀ (by exact_mod_cast hε)
  have hleib : HasDerivAt (fun t => ∫ x in Set.Ioc a b, (w x t) ^ 2)
      (∫ x in Set.Ioc a b, 2 * w x t₀ * wt x t₀) t₀ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun x a => (w a x) ^ 2)
      (F' := fun x a => 2 * w a x * wt a x) hsball hFmeas hFint hF'0
      h_bound_pf h_int_pf h_deriv_pf).2
  have hibp : (∫ x in Set.Ioc a b, 2 * w x t₀ * wt x t₀)
      = -2 * D * ∫ x in Set.Ioc a b, (wx x t₀) ^ 2 := by
    have hab' : a ≤ b := hab.le
    have hIoc_eq : ∀ f : ℝ → ℝ, (∫ x in Set.Ioc a b, f x) = ∫ x in a..b, f x :=
      fun f => (intervalIntegral.integral_of_le hab').symm
    have hpde' : ∀ x ∈ Set.Ioc a b, 2 * w x t₀ * wt x t₀ = 2 * w x t₀ * (D * wxx x t₀) := by
      intro x hx
      have hxIcc : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
      rw [hpde x hxIcc t₀]
    have hcongr : (∫ x in a..b, 2 * w x t₀ * wt x t₀)
        = ∫ x in a..b, 2 * w x t₀ * (D * wxx x t₀) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      have hxIoc : x ∈ Set.Ioc a b := by
        have h := Set.uIoc_of_le hab'
        rwa [h] at hx
      exact hpde' x hxIoc
    have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u => w u t₀) (wx x t₀) x :=
      fun x _ => hx x t₀
    have hv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun u => wx u t₀) (wxx x t₀) x :=
      fun x _ => hxx x t₀
    have hwx_slice : ContinuousOn (fun x => wx x t₀) (Set.Icc a b) :=
      hwx_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun x hx => by
        change (x, t₀) ∈ Set.Icc a b ×ˢ Set.univ
        rw [mem_prod]
        exact ⟨hx, mem_univ _⟩)
    have hwxx_slice : ContinuousOn (fun x => wxx x t₀) (Set.Icc a b) :=
      hwxx_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun x hx => by
        change (x, t₀) ∈ Set.Icc a b ×ˢ Set.univ
        rw [mem_prod]
        exact ⟨hx, mem_univ _⟩)
    have hu' : IntervalIntegrable (fun x => wx x t₀) volume a b := by
      have hc : ContinuousOn (fun x => wx x t₀) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab']
        exact hwx_slice
      exact hc.intervalIntegrable
    have hv' : IntervalIntegrable (fun x => wxx x t₀) volume a b := by
      have hc : ContinuousOn (fun x => wxx x t₀) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab']
        exact hwxx_slice
      exact hc.intervalIntegrable
    have hibp0 : (∫ x in a..b, w x t₀ * wxx x t₀)
        = (w b t₀ * wx b t₀ - w a t₀ * wx a t₀) - ∫ x in a..b, wx x t₀ * wx x t₀ := by
      have hmain : (∫ x in a..b, wx x t₀ * wx x t₀ + w x t₀ * wxx x t₀)
          = w b t₀ * wx b t₀ - w a t₀ * wx a t₀ :=
        intervalIntegral.integral_deriv_mul_eq_sub hu hv hu' hv'
      have hw_slice : ContinuousOn (fun x => w x t₀) (Set.Icc a b) :=
        hw_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun x hx => by
          change (x, t₀) ∈ Set.Icc a b ×ˢ Set.univ
          rw [mem_prod]
          exact ⟨hx, mem_univ _⟩)
      have hmul1 : ContinuousOn (fun x => wx x t₀ * wx x t₀) (Set.Icc a b) :=
        hwx_slice.mul hwx_slice
      have hmul2 : ContinuousOn (fun x => w x t₀ * wxx x t₀) (Set.Icc a b) :=
        hw_slice.mul hwxx_slice
      have hc1 : ContinuousOn (fun x => wx x t₀ * wx x t₀) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab']
        exact hmul1
      have hc2 : ContinuousOn (fun x => w x t₀ * wxx x t₀) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab']
        exact hmul2
      have hsplit : (∫ x in a..b, wx x t₀ * wx x t₀ + w x t₀ * wxx x t₀)
          = (∫ x in a..b, wx x t₀ * wx x t₀) + ∫ x in a..b, w x t₀ * wxx x t₀ :=
        intervalIntegral.integral_add hc1.intervalIntegrable hc2.intervalIntegrable
      linarith [hmain, hsplit]
    have hpull2 : (∫ x in a..b, 2 * w x t₀ * (D * wxx x t₀))
        = (2 * D) * ∫ x in a..b, w x t₀ * wxx x t₀ := by
      have heq : (fun x : ℝ => 2 * w x t₀ * (D * wxx x t₀))
          = (fun x => (2 * D) * (w x t₀ * wxx x t₀)) := by
        funext x
        ring
      rw [heq, intervalIntegral.integral_const_mul]
    have hdir : w b t₀ * wx b t₀ - w a t₀ * wx a t₀ = 0 := by
      have ha0 := (hbc t₀).1
      have hb0 := (hbc t₀).2
      rw [ha0, hb0, zero_mul, zero_mul, sub_self]
    have hsq2 : (∫ x in a..b, wx x t₀ * wx x t₀) = ∫ x in a..b, (wx x t₀) ^ 2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x _hx
      rw [pow_two]
    calc (∫ x in Set.Ioc a b, 2 * w x t₀ * wt x t₀)
        = (∫ x in a..b, 2 * w x t₀ * wt x t₀) := hIoc_eq _
      _ = ∫ x in a..b, 2 * w x t₀ * (D * wxx x t₀) := hcongr
      _ = (2 * D) * ∫ x in a..b, w x t₀ * wxx x t₀ := hpull2
      _ = (2 * D) * ((w b t₀ * wx b t₀ - w a t₀ * wx a t₀) - ∫ x in a..b, wx x t₀ * wx x t₀) := by
          rw [hibp0]
      _ = (2 * D) * (0 - ∫ x in a..b, wx x t₀ * wx x t₀) := by rw [hdir]
      _ = -2 * D * ∫ x in a..b, (wx x t₀) ^ 2 := by rw [← hsq2]; ring
      _ = -2 * D * ∫ x in Set.Ioc a b, (wx x t₀) ^ 2 := by rw [hIoc_eq]
  rwa [hibp] at hleib

/-- C3: uniqueness on a bounded interval with Dirichlet data (energy method). -/
theorem diffusion_unique_dirichlet (a b T D : ℝ) (hab : a < b) (hT : 0 < T) (hD : 0 < D)
    (c₁ c₂ w wx wxx wt : ℝ → ℝ → ℝ)
    (hw_def : ∀ x t, w x t = c₁ x t - c₂ x t)
    (ht : ∀ x t, HasDerivAt (fun τ => w x τ) (wt x t) t)
    (hx : ∀ x t, HasDerivAt (fun u => w u t) (wx x t) x)
    (hxx : ∀ x t, HasDerivAt (fun u => wx u t) (wxx x t) x)
    (hw_cont : ContinuousOn (fun p : ℝ × ℝ => w p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hwx_cont : ContinuousOn (fun p : ℝ × ℝ => wx p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hwxx_cont : ContinuousOn (fun p : ℝ × ℝ => wxx p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hwt_cont : ContinuousOn (fun p : ℝ × ℝ => wt p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hpde : ∀ x ∈ Set.Icc a b, ∀ t, wt x t = D * wxx x t)
    (hbc : ∀ t, w a t = 0 ∧ w b t = 0)
    (hinit : ∀ x ∈ Set.Icc a b, w x 0 = 0) :
    ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Icc 0 T, c₁ x t = c₂ x t := by
  have hE : ∀ t₀, HasDerivAt (fun t => ∫ x in Set.Ioc a b, (w x t) ^ 2)
      (-2 * D * ∫ x in Set.Ioc a b, (wx x t₀) ^ 2) t₀ :=
    energy_identity_deriv a b D hab hD c₁ c₂ w wx wxx wt hw_def ht hx hxx
      hw_cont hwx_cont hwxx_cont hwt_cont hpde hbc
  have hEle : ∀ t ∈ Set.Icc 0 T, (∫ x in Set.Ioc a b, (w x t) ^ 2)
      ≤ ∫ x in Set.Ioc a b, (w x 0) ^ 2 := by
    intro t ht
    rcases eq_or_lt_of_le (Set.mem_Icc.mp ht).1 with rfl | h0pos
    · exact le_rfl
    · have hEcont : ContinuousOn (fun t => ∫ x in Set.Ioc a b, (w x t) ^ 2) (Set.Icc 0 t) :=
        fun s _ => ((hE s).continuousAt).continuousWithinAt
      have hEdiff : DifferentiableOn ℝ (fun t => ∫ x in Set.Ioc a b, (w x t) ^ 2) (Set.Ioo 0 t) :=
        fun s _ => ((hE s).differentiableAt).differentiableWithinAt
      have hab0t : (0 : ℝ) < t := h0pos
      have hf' : ∀ x ∈ Set.Ioo 0 t, HasDerivAt (fun t => ∫ y in Set.Ioc a b, (w y t) ^ 2)
          (-2 * D * ∫ y in Set.Ioc a b, (wx y x) ^ 2) x := fun x _ => hE x
      obtain ⟨ξ, hξmem, hξ⟩ : ∃ c ∈ Set.Ioo 0 t,
          (-2 * D * ∫ x in Set.Ioc a b, (wx x c) ^ 2)
            = (((∫ x in Set.Ioc a b, (w x t) ^ 2) - ∫ x in Set.Ioc a b, (w x 0) ^ 2) / (t - 0)) := by
        exact exists_hasDerivAt_eq_slope _ _ hab0t hEcont hf'
      have hGt : (∫ x in Set.Ioc a b, (w x t) ^ 2) - ∫ x in Set.Ioc a b, (w x 0) ^ 2
          = (-2 * D * ∫ x in Set.Ioc a b, (wx x ξ) ^ 2) * (t - 0) := by
        have ht0 : t - 0 ≠ 0 := by
          have hpos : (0 : ℝ) < t - 0 := by linarith [h0pos]
          exact ne_of_gt hpos
        rw [eq_div_iff ht0] at hξ
        exact hξ.symm
      have hGnn : (0 : ℝ) ≤ ∫ x in Set.Ioc a b, (wx x ξ) ^ 2 := by
        have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), (0 : ℝ) ≤ (wx x ξ) ^ 2 := by
          filter_upwards with x
          exact sq_nonneg _
        exact MeasureTheory.integral_nonneg_of_ae hae
      have hGle : (-2 * D * ∫ x in Set.Ioc a b, (wx x ξ) ^ 2) * (t - 0) ≤ 0 := by
        have h1 : (-2 * D * ∫ x in Set.Ioc a b, (wx x ξ) ^ 2) ≤ 0 := by
          have h2D : (-2 * D : ℝ) ≤ 0 := by
            have hpos : (0 : ℝ) ≤ 2 * D := by positivity
            linarith
          exact mul_nonpos_of_nonpos_of_nonneg h2D hGnn
        have h2 : (0 : ℝ) ≤ t - 0 := by linarith [h0pos]
        exact mul_nonpos_of_nonpos_of_nonneg h1 h2
      linarith [hGt, hGle]
  have hE0 : (∫ x in Set.Ioc a b, (w x 0) ^ 2) = 0 := by
    have heq : EqOn (fun x => (w x 0) ^ 2) 0 (Set.Ioc a b) := by
      intro x hx
      have hxIcc : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
      show (w x 0) ^ 2 = (0 : ℝ → ℝ) x
      rw [hinit x hxIcc]
      simp
    have h : (∫ x in Set.Ioc a b, (w x 0) ^ 2) = ∫ x in Set.Ioc a b, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact heq hx
    rw [h]
    simp
  have hEnn : ∀ t, (0 : ℝ) ≤ ∫ x in Set.Ioc a b, (w x t) ^ 2 := by
    intro t
    have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), (0 : ℝ) ≤ (w x t) ^ 2 := by
      filter_upwards with x
      exact sq_nonneg _
    exact MeasureTheory.integral_nonneg_of_ae hae
  have hEeq0 : ∀ t ∈ Set.Icc 0 T, (∫ x in Set.Ioc a b, (w x t) ^ 2) = 0 := by
    intro t ht
    have h1 := hEle t ht
    rw [hE0] at h1
    have h2 := hEnn t
    linarith
  intro x hx t ht
  have hEt0 := hEeq0 t ht
  have hw0 : w x t = 0 := by
    by_contra hne
    have hpos : (0 : ℝ) < (w x t) ^ 2 := sq_pos_of_ne_zero hne
    have hsqc : ContinuousOn (fun y => (w y t) ^ 2) (Set.Icc a b) := by
      have hwxc : ContinuousOn (fun y => w y t) (Set.Icc a b) :=
        hw_cont.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun y hy => by
          show (y, t) ∈ Set.Icc a b ×ˢ Set.univ
          rw [mem_prod]
          exact ⟨hy, mem_univ _⟩)
      exact hwxc.pow 2
    have hc : (0 : ℝ) < (w x t) ^ 2 / 2 := by linarith [hpos]
    have hev : ∀ᶠ y in 𝓝[Set.Icc a b] x, dist ((w y t) ^ 2) ((w x t) ^ 2) < (w x t) ^ 2 / 2 := by
      have htw : Tendsto (fun y => (w y t) ^ 2) (𝓝[Set.Icc a b] x) (𝓝 ((w x t) ^ 2)) :=
        hsqc x hx
      have hmem := Metric.ball_mem_nhds ((w x t) ^ 2) hc
      have hpre := htw hmem
      filter_upwards [hpre] with y hy
      exact Metric.mem_ball.mp hy
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
    have hJbound : ∀ y ∈ Set.Icc a b, dist y x < δ → (w x t) ^ 2 / 2 ≤ (w y t) ^ 2 := by
      intro y hy hdyx
      have h := hδ y hdyx hy
      rw [Real.dist_eq] at h
      have habs := abs_lt.mp h
      linarith [habs.1, habs.2, hpos]
    have habx : a < x ∨ x < b := by
      by_contra hcon
      push Not at hcon
      have hx1 := (Set.mem_Icc.mp hx).1
      have hx2 := (Set.mem_Icc.mp hx).2
      linarith [hab, hcon.1, hcon.2, hx1, hx2]
    set u : ℝ := max a (x - δ / 2) with hu_def
    set v : ℝ := min b (x + δ / 2) with hv_def
    have hux : u ≤ x := by
      rw [hu_def]
      exact max_le_iff.mpr ⟨(Set.mem_Icc.mp hx).1, by linarith [hδpos]⟩
    have hxv : x ≤ v := by
      rw [hv_def]
      exact le_min_iff.mpr ⟨(Set.mem_Icc.mp hx).2, by linarith [hδpos]⟩
    have huv : u < v := by
      rcases habx with hax | hxb
      · have hu_lt : u < x := by
          rw [hu_def]
          exact max_lt_iff.mpr ⟨hax, by linarith [hδpos]⟩
        exact lt_of_lt_of_le hu_lt hxv
      · have hv_gt : x < v := by
          rw [hv_def]
          exact lt_min_iff.mpr ⟨hxb, by linarith [hδpos]⟩
        exact lt_of_le_of_lt hux hv_gt
    have hJball : ∀ y ∈ Set.Ioo u v, dist y x < δ := by
      intro y hy
      have hy1 : u < y := (Set.mem_Ioo.mp hy).1
      have hy2 : y < v := (Set.mem_Ioo.mp hy).2
      have hlo : x - δ / 2 ≤ y := by
        have h1 : x - δ / 2 ≤ u := by
          rw [hu_def]
          exact le_max_right _ _
        exact le_trans h1 (le_of_lt hy1)
      have hhi : y ≤ x + δ / 2 := by
        have h1 : v ≤ x + δ / 2 := by
          rw [hv_def]
          exact min_le_right _ _
        exact le_trans (le_of_lt hy2) h1
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hJIcc : Set.Ioo u v ⊆ Set.Icc a b := by
      intro y hy
      have hy1 : u < y := (Set.mem_Ioo.mp hy).1
      have hy2 : y < v := (Set.mem_Ioo.mp hy).2
      have hau : a ≤ u := by
        rw [hu_def]
        exact le_max_left _ _
      have hvb : v ≤ b := by
        rw [hv_def]
        exact min_le_left _ _
      exact Set.mem_Icc.mpr ⟨le_of_lt (lt_of_le_of_lt hau hy1), le_of_lt (lt_of_lt_of_le hy2 hvb)⟩
    have hJIoc : Set.Ioo u v ⊆ Set.Ioc a b := by
      intro y hy
      have hyIcc := hJIcc hy
      have hy1 : u < y := (Set.mem_Ioo.mp hy).1
      have hau : a ≤ u := by
        rw [hu_def]
        exact le_max_left _ _
      exact Set.mem_Ioc.mpr ⟨lt_of_le_of_lt hau hy1, (Set.mem_Icc.mp hyIcc).2⟩
    have hJpos : (0 : ℝ) < ∫ y in Set.Ioo u v, (w y t) ^ 2 := by
      have hge : ∀ y ∈ Set.Ioo u v, (w x t) ^ 2 / 2 ≤ (w y t) ^ 2 :=
        fun y hy => hJbound y (hJIcc hy) (hJball y hy)
      have hIc : IntegrableOn (fun _ : ℝ => (w x t) ^ 2 / 2) (Set.Ioo u v) := by
        have hIccC : IntegrableOn (fun _ : ℝ => (w x t) ^ 2 / 2) (Set.Icc a b) :=
          continuous_const.continuousOn.integrableOn_compact isCompact_Icc
        exact hIccC.mono_set hJIcc
      have hIf : IntegrableOn (fun y => (w y t) ^ 2) (Set.Ioo u v) := by
        have hIcc : IntegrableOn (fun y => (w y t) ^ 2) (Set.Icc a b) :=
          hsqc.integrableOn_compact isCompact_Icc
        exact hIcc.mono_set hJIcc
      have haeJ : (fun _ : ℝ => (w x t) ^ 2 / 2)
          ≤ᵐ[volume.restrict (Set.Ioo u v)] (fun y => (w y t) ^ 2) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        exact hge y hy
      have hmonoJ : (∫ y in Set.Ioo u v, (w x t) ^ 2 / 2)
          ≤ ∫ y in Set.Ioo u v, (w y t) ^ 2 := by
        exact integral_mono_ae hIc hIf haeJ
      have hconstJ : (∫ y in Set.Ioo u v, (w x t) ^ 2 / 2)
          = ((w x t) ^ 2 / 2) * (v - u) := by
        have huv' : (0 : ℝ) ≤ v - u := le_of_lt (sub_pos.mpr huv)
        have hvol : (volume (Set.Ioo u v)).toReal = v - u := by
          rw [Real.volume_Ioo, ENNReal.toReal_ofReal huv']
        rw [setIntegral_const, MeasureTheory.Measure.real_def, hvol, smul_eq_mul]
        ring
      have hJmeasure : (0 : ℝ) < ((w x t) ^ 2 / 2) * (v - u) :=
        mul_pos hc (sub_pos.mpr huv)
      linarith [hconstJ, hmonoJ, hJmeasure]
    have hIfull : IntegrableOn (fun y => (w y t) ^ 2) (Set.Ioc a b) := by
      have hIcc : IntegrableOn (fun y => (w y t) ^ 2) (Set.Icc a b) :=
        hsqc.integrableOn_compact isCompact_Icc
      exact hIcc.mono_set Set.Ioc_subset_Icc_self
    have haenn : ∀ᵐ y ∂(volume.restrict (Set.Ioc a b)), (0 : ℝ) ≤ (w y t) ^ 2 := by
      filter_upwards with y
      exact sq_nonneg _
    have hmonoFull : (∫ y in Set.Ioo u v, (w y t) ^ 2)
        ≤ ∫ y in Set.Ioc a b, (w y t) ^ 2 := by
      have hsub : Set.Ioo u v ≤ᵐ[volume] Set.Ioc a b :=
        Filter.Eventually.of_forall (fun y hy => hJIoc hy)
      exact setIntegral_mono_set hIfull haenn hsub
    linarith [hJpos, hmonoFull, hEt0]
  have hcc : c₁ x t - c₂ x t = 0 := by
    have h := hw_def x t
    rw [hw0] at h
    exact h.symm
  exact sub_eq_zero.mp hcc

/-- Parabolic scaling of a solution. -/
noncomputable def scaledSol (c : ℝ → ℝ → ℝ) (lam x t : ℝ) : ℝ :=
  c (lam * x) (lam ^ 2 * t)

/-- C3: parabolic scaling preserves the diffusion equation (global solution). -/
theorem similarity_pde (D lam : ℝ) (hlam : 0 < lam) (c cx cxx ct : ℝ → ℝ → ℝ)
    (ht : ∀ X T, HasDerivAt (fun σ => c X σ) (ct X T) T)
    (hx : ∀ X T, HasDerivAt (fun u => c u T) (cx X T) X)
    (hxx : ∀ X T, HasDerivAt (fun u => cx u T) (cxx X T) X)
    (hpde : ∀ X T, ct X T = D * cxx X T) :
    ∀ x t, deriv (fun τ => scaledSol c lam x τ) t
      = D * deriv (fun x' => deriv (fun u => scaledSol c lam u t) x') x := by
  intro x t
  have hTlin : ∀ τ : ℝ, HasDerivAt (fun τ => lam ^ 2 * τ) (lam ^ 2) τ := by
    intro τ
    simpa using (hasDerivAt_id' τ).const_mul (lam ^ 2)
  have hts : HasDerivAt (fun τ => scaledSol c lam x τ)
      (lam ^ 2 * ct (lam * x) (lam ^ 2 * t)) t := by
    have hraw := (ht (lam * x) (lam ^ 2 * t)).comp t (hTlin t)
    show HasDerivAt (fun τ => c (lam * x) (lam ^ 2 * τ))
      (lam ^ 2 * ct (lam * x) (lam ^ 2 * t)) t
    have hderiv : lam ^ 2 * ct (lam * x) (lam ^ 2 * t)
        = ct (lam * x) (lam ^ 2 * t) * lam ^ 2 := by ring
    rw [hderiv]
    exact hraw
  have hx1 : ∀ x' : ℝ, HasDerivAt (fun u => scaledSol c lam u t)
      (lam * cx (lam * x') (lam ^ 2 * t)) x' := by
    intro x'
    have hXlin : HasDerivAt (fun ξ => lam * ξ) lam x' := by
      simpa using (hasDerivAt_id' x').const_mul lam
    have hraw := (hx (lam * x') (lam ^ 2 * t)).comp x' hXlin
    change HasDerivAt (fun u => c (lam * u) (lam ^ 2 * t))
      (lam * cx (lam * x') (lam ^ 2 * t)) x'
    have hderiv : lam * cx (lam * x') (lam ^ 2 * t)
        = cx (lam * x') (lam ^ 2 * t) * lam := by ring
    rw [hderiv]
    exact hraw
  have hxx2 : HasDerivAt (fun x' => deriv (fun u => scaledSol c lam u t) x')
      (lam * (lam * cxx (lam * x) (lam ^ 2 * t))) x := by
    have hfun : (fun x' => deriv (fun u => scaledSol c lam u t) x')
        = (fun x' => lam * cx (lam * x') (lam ^ 2 * t)) := by
      funext x'
      exact (hx1 x').deriv
    rw [hfun]
    have hXlin : HasDerivAt (fun ξ => lam * ξ) lam x := by
      simpa using (hasDerivAt_id' x).const_mul lam
    have hraw := (hxx (lam * x) (lam ^ 2 * t)).comp x hXlin
    have hchain := hraw.const_mul lam
    have hderiv : lam * (lam * cxx (lam * x) (lam ^ 2 * t))
        = lam * (cxx (lam * x) (lam ^ 2 * t) * lam) := by ring
    rw [hderiv]
    exact hchain
  rw [hts.deriv, hxx2.deriv, hpde (lam * x) (lam ^ 2 * t)]
  ring

/-- Similarity variable `ξ = x / √(D * t)`. -/
noncomputable def simVar (D x t : ℝ) : ℝ :=
  x / Real.sqrt (D * t)

/-- C3: the similarity variable is invariant under parabolic scaling. -/
theorem simVar_invariant (D x t lam : ℝ) (hD : 0 < D) (ht : 0 < t) (hlam : 0 < lam) :
    simVar D (lam * x) (lam ^ 2 * t) = simVar D x t := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hDt : (0 : ℝ) < D * t := by positivity
  have hsq : Real.sqrt (D * t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hDt)
  have hsqrt : Real.sqrt (D * (lam ^ 2 * t)) = lam * Real.sqrt (D * t) := by
    have hfactor : (D * (lam ^ 2 * t) : ℝ) = lam ^ 2 * (D * t) := by ring
    rw [hfactor, Real.sqrt_mul (sq_nonneg lam), Real.sqrt_sq hlam.le]
  simp only [simVar]
  rw [hsqrt]
  field_simp

/-- Linear steady profile on `[0, L]`. -/
noncomputable def steadyProfile (c₁ c₂ L x : ℝ) : ℝ :=
  c₁ + ((c₂ - c₁) / L) * x

/-- C4: left boundary value. -/
theorem steady_boundary_zero (c₁ c₂ L : ℝ) : steadyProfile c₁ c₂ L 0 = c₁ := by
  simp only [steadyProfile, mul_zero, add_zero]

/-- C4: right boundary value. -/
theorem steady_boundary_L (c₁ c₂ L : ℝ) (hL : 0 < L) : steadyProfile c₁ c₂ L L = c₂ := by
  have hL' : L ≠ 0 := ne_of_gt hL
  simp only [steadyProfile]
  field_simp
  ring

/-- C4: first spatial derivative of the steady profile (constant). -/
theorem steady_xderiv_value (c₁ c₂ L x : ℝ) :
    HasDerivAt (fun x => steadyProfile c₁ c₂ L x) (((c₂ - c₁) / L) * 1) x := by
  have hmul : HasDerivAt (fun x : ℝ => ((c₂ - c₁) / L) * x) (((c₂ - c₁) / L) * 1) x := by
    simpa using (hasDerivAt_id' x).const_mul ((c₂ - c₁) / L)
  simpa [steadyProfile] using hmul.const_add c₁

/-- C4: the steady profile satisfies the steady PDE (`∂c/∂t = 0`, `D ∂²c/∂x² = 0`). -/
theorem steady_pde (c₁ c₂ L D x t : ℝ) (hL : 0 < L) :
    deriv (fun t => steadyProfile c₁ c₂ L x) t = 0
      ∧ D * deriv (fun x' => deriv (fun u => steadyProfile c₁ c₂ L u) x') x = 0 := by
  constructor
  · have hfun : (fun t : ℝ => steadyProfile c₁ c₂ L x)
        = (fun _ : ℝ => steadyProfile c₁ c₂ L x) := rfl
    rw [hfun]
    exact deriv_const _ _
  · have hfun : (fun x' => deriv (fun u => steadyProfile c₁ c₂ L u) x')
        = (fun _ => ((c₂ - c₁) / L) * 1) := by
      funext x'
      exact (steady_xderiv_value c₁ c₂ L x').deriv
    rw [hfun]
    have h0 : deriv (fun _ : ℝ => ((c₂ - c₁) / L) * 1) x = 0 := deriv_const _ _
    rw [h0, mul_zero]

/-- C4: steady membrane flux `J = D (c₁ - c₂) / L` from Fick's law. -/
theorem steady_flux (c₁ c₂ L D : ℝ) (hL : 0 < L) (x : ℝ) :
    -D * deriv (fun x' => steadyProfile c₁ c₂ L x') x = D * (c₁ - c₂) / L := by
  have hL' : L ≠ 0 := ne_of_gt hL
  rw [(steady_xderiv_value c₁ c₂ L x).deriv]
  field_simp
  ring

/-- Closed-form sine-series coefficients for a uniform initial profile. -/
noncomputable def fourierCoeff (c₀ L : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (2 * c₀ / (n * Real.pi)) * (1 - (-1) ^ n)

/-- Fourier sine-series terms for the slab (Dirichlet zero boundaries). -/
noncomputable def fourierTerm (c₀ L D : ℝ) (n : ℕ) (x t : ℝ) : ℝ :=
  fourierCoeff c₀ L n * Real.sin (n * Real.pi * x / L)
    * Real.exp (-D * (n * Real.pi / L) ^ 2 * t)

/-- C4: coefficient formula `(2/L) ∫₀ᴸ c₀ sin(nπx/L) dx = bₙ`. -/
theorem fourierCoeff_formula (c₀ L : ℝ) (hL : 0 < L) (n : ℕ) (hn : 1 ≤ n) :
    (2 / L) * ∫ x in (0 : ℝ)..L, c₀ * Real.sin (n * Real.pi * x / L)
      = fourierCoeff c₀ L n := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by
    have h0n : 0 < n := by omega
    exact_mod_cast h0n
  have hnpi : (0 : ℝ) < n * Real.pi := mul_pos hnpos Real.pi_pos
  have hnpi' : (n * Real.pi : ℝ) ≠ 0 := ne_of_gt hnpi
  have hform : (fun x : ℝ => n * Real.pi * x / L) = (fun x => (n * Real.pi / L) * x) := by
    funext x
    ring
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) L, HasDerivAt
      (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x))
      (c₀ * Real.sin ((n * Real.pi / L) * x)) x := by
    intro x _
    have hu : HasDerivAt (fun x : ℝ => (n * Real.pi / L) * x) ((n * Real.pi) / L) x := by
      simpa using (hasDerivAt_id' x).const_mul ((n * Real.pi) / L)
    have hcos := hu.cos
    have hchain := hcos.const_mul (c₀ * (-L / (n * Real.pi)))
    show HasDerivAt (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x))
      (c₀ * Real.sin ((n * Real.pi / L) * x)) x
    have hder : c₀ * Real.sin ((n * Real.pi / L) * x)
        = c₀ * (-L / (n * Real.pi))
          * (-Real.sin ((n * Real.pi / L) * x) * ((n * Real.pi) / L)) := by
      field_simp
    rw [hder]
    exact hchain
  have hFcont : ContinuousOn (fun x => c₀ * Real.sin ((n * Real.pi / L) * x)) (Set.uIcc 0 L) := by
    have hsin : Continuous (fun x : ℝ => Real.sin ((n * Real.pi / L) * x)) :=
      Real.continuous_sin.comp (continuous_id.const_mul _)
    have hmul := hsin.const_mul c₀
    exact hmul.continuousOn
  have hFint : IntervalIntegrable (fun x => c₀ * Real.sin ((n * Real.pi / L) * x)) volume 0 L :=
    hFcont.intervalIntegrable
  have hFTC : (∫ x in (0 : ℝ)..L, c₀ * Real.sin ((n * Real.pi / L) * x))
      = (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x)) L
        - (fun x => c₀ * (-L / (n * Real.pi)) * Real.cos ((n * Real.pi / L) * x)) 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hF hFint
  have hcosL : Real.cos ((n * Real.pi / L) * L) = (-1) ^ n := by
    have harg : (n * Real.pi / L) * L = n * Real.pi := by
      field_simp
    rw [harg]
    exact Real.cos_nat_mul_pi n
  have hcos0 : Real.cos ((n * Real.pi / L) * 0) = 1 := by
    have harg : (n * Real.pi / L) * 0 = 0 := by ring
    rw [harg]
    exact Real.cos_zero
  simp only [fourierCoeff, ite_eq_right hn0]
  have harg : ∀ x : ℝ, (n * Real.pi * x / L) = ((n * Real.pi / L) * x) :=
    fun x => congrFun hform x
  simp_rw [harg]
  rw [hFTC]
  simp only []
  rw [hcosL, hcos0]
  field_simp
  ring

/-- C4: termwise bounds uniform for `t ≥ δ > 0`. -/
theorem fourierTerm_bound (c₀ L D δ : ℝ) (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hD : 0 < D) (hδ : 0 < δ)
    (n : ℕ) (x t : ℝ) (ht : δ ≤ t) :
    ‖fourierTerm c₀ L D n x t‖
      ≤ (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
  have hL' : L ≠ 0 := ne_of_gt hL
  have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hn0 : n = 0
  · subst hn0
    have hb0 : fourierCoeff c₀ L 0 = 0 := ite_eq_left rfl
    have hC : (0 : ℝ) ≤ 4 * c₀ / Real.pi + 1 := by positivity
    simp only [fourierTerm, hb0, zero_mul, norm_zero, pow_zero, mul_one]
    exact hC
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnR : (0 : ℝ) < n := by
      have h0n : 0 < n := by omega
      exact_mod_cast h0n
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpi' : (n * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos hnR Real.pi_pos)
    have h3 : (0 : ℝ) ≤ 4 * c₀ / (n * Real.pi) := by positivity
    have h2n : (0 : ℝ) ≤ 2 * c₀ / (n * Real.pi) := by positivity
    have hb : |fourierCoeff c₀ L n| ≤ 4 * c₀ / (n * Real.pi) := by
      simp only [fourierCoeff, ite_eq_right hn0]
      have h1 : |(-1 : ℝ) ^ n| = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      have h2 : |(1 : ℝ) - (-1) ^ n| ≤ 2 := by
        calc |(1 : ℝ) - (-1) ^ n| = |1 + (-(-1) ^ n)| := by rw [sub_eq_add_neg]
          _ ≤ |1| + |-(-1) ^ n| := abs_add_le _ _
          _ = 2 := by rw [abs_one, abs_neg, h1]; norm_num
      calc |(2 * c₀ / (n * Real.pi)) * (1 - (-1) ^ n)|
          = |2 * c₀ / (n * Real.pi)| * |1 - (-1) ^ n| := abs_mul _ _
        _ = (2 * c₀ / (n * Real.pi)) * |1 - (-1) ^ n| := by rw [abs_of_nonneg h2n]
        _ ≤ (2 * c₀ / (n * Real.pi)) * 2 := mul_le_mul_of_nonneg_left h2 h2n
        _ = 4 * c₀ / (n * Real.pi) := by
            field_simp
            ring
    have hsin : |Real.sin (n * Real.pi * x / L)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have hexp_t : Real.exp (-D * (n * Real.pi / L) ^ 2 * t)
        ≤ Real.exp (-D * (n * Real.pi / L) ^ 2 * δ) := by
      apply Real.exp_le_exp.mpr
      have hnn : (-D * (n * Real.pi / L) ^ 2) ≤ 0 := by
        have h1 : (0 : ℝ) ≤ D * (n * Real.pi / L) ^ 2 := mul_nonneg hD.le (sq_nonneg _)
        have h2 : -D * (n * Real.pi / L) ^ 2 = -(D * (n * Real.pi / L) ^ 2) := by ring
        rw [h2]
        linarith [h1]
      exact mul_le_mul_of_nonpos_left ht hnn
    have hexp_n : Real.exp (-D * (n * Real.pi / L) ^ 2 * δ)
        ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
      have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        nlinarith [sq_nonneg ((n : ℝ) - 1), hn1']
      have hk : (0 : ℝ) ≤ D * (Real.pi / L) ^ 2 * δ :=
        mul_nonneg (mul_nonneg hD.le (sq_nonneg _)) hδ.le
      have hX : (-D * (n * Real.pi / L) ^ 2 * δ) ≤ n * (-D * (Real.pi / L) ^ 2 * δ) := by
        have hsq : (n * Real.pi / L) ^ 2 = (n : ℝ) ^ 2 * (Real.pi / L) ^ 2 := by
          ring
        rw [hsq]
        nlinarith [mul_nonneg (sub_nonneg.mpr hn2) hk]
      calc Real.exp (-D * (n * Real.pi / L) ^ 2 * δ)
          ≤ Real.exp (n * (-D * (Real.pi / L) ^ 2 * δ)) := Real.exp_le_exp.mpr hX
        _ = Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := Real.exp_nat_mul _ _
    have hexp_le : Real.exp (-D * (n * Real.pi / L) ^ 2 * t)
        ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := hexp_t.trans hexp_n
    have hρ0 : (0 : ℝ) ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by positivity
    have g1 := hb
    have g2 := hsin
    have g3 : (0 : ℝ) ≤ |Real.sin (n * Real.pi * x / L)| := abs_nonneg _
    have g4 := h3
    have h12 : |fourierCoeff c₀ L n| * |Real.sin (n * Real.pi * x / L)|
        ≤ (4 * c₀ / (n * Real.pi)) * 1 := by
      apply mul_le_mul <;> assumption
    have g5 : (0 : ℝ) ≤ Real.exp (-D * (n * Real.pi / L) ^ 2 * t) := (Real.exp_pos _).le
    have g6 : (0 : ℝ) ≤ (4 * c₀ / (n * Real.pi)) * 1 := mul_nonneg h3 zero_le_one
    have h123 : (|fourierCoeff c₀ L n| * |Real.sin (n * Real.pi * x / L)|)
        * Real.exp (-D * (n * Real.pi / L) ^ 2 * t)
        ≤ ((4 * c₀ / (n * Real.pi)) * 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
      apply mul_le_mul <;> assumption
    have hCbound : (4 * c₀ / (n * Real.pi)) * 1 ≤ 4 * c₀ / Real.pi + 1 := by
      rw [mul_one]
      have hle : 4 * c₀ / (n * Real.pi) ≤ 4 * c₀ / Real.pi := by
        have heq : (4 * c₀ / (n * Real.pi)) = (4 * c₀ / Real.pi) * (1 / n) := by
          field_simp
        rw [heq]
        have h1n : (1 : ℝ) / n ≤ 1 := (div_le_one hnR).mpr hn1R
        have hnn : (0 : ℝ) ≤ 4 * c₀ / Real.pi := by positivity
        calc (4 * c₀ / Real.pi) * (1 / n) ≤ (4 * c₀ / Real.pi) * 1 :=
              mul_le_mul_of_nonneg_left h1n hnn
          _ = 4 * c₀ / Real.pi := mul_one _
      linarith [hle]
    have hfinal : ((4 * c₀ / (n * Real.pi)) * 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n
        ≤ (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n :=
      mul_le_mul_of_nonneg_right hCbound hρ0
    simp only [fourierTerm]
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    exact le_trans h123 hfinal

/-- C4: the Weierstrass dominator is summable. -/
theorem fourier_dominator_summable (c₀ L D δ : ℝ) (hL : 0 < L) (hD : 0 < D) (hδ : 0 < δ) :
    Summable (fun n : ℕ => (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n) := by
  have hρ0 : (0 : ℝ) ≤ Real.exp (-D * (Real.pi / L) ^ 2 * δ) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-D * (Real.pi / L) ^ 2 * δ) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have hL' : L ≠ 0 := ne_of_gt hL
    have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
    have hpl : (Real.pi / L : ℝ) ≠ 0 := div_ne_zero hpi' hL'
    have hsq2 : (Real.pi / L) ^ 2 ≠ 0 := by
      rw [pow_two]
      exact mul_ne_zero hpl hpl
    have hsq : (0 : ℝ) < (Real.pi / L) ^ 2 := lt_of_le_of_ne (sq_nonneg _) hsq2.symm
    have hDL : (0 : ℝ) < D * (Real.pi / L) ^ 2 * δ :=
      mul_pos (mul_pos hD hsq) hδ
    linarith
  have hgeom := summable_geometric_of_lt_one hρ0 hρ1
  exact hgeom.mul_left _

/-- C4: uniform convergence of the slab series for `t ≥ δ > 0` (Weierstrass M-test).
Proved: coefficient formula, termwise bounds, uniform convergence on `[δ, ∞)`.
Not proved: termwise differentiation (PDE satisfaction), `C^2` regularity,
initial-data attainment at `t = 0`, or convergence at `t = 0`. -/
theorem fourier_uniform_convergent (c₀ L D δ : ℝ) (hc₀ : 0 ≤ c₀) (hL : 0 < L) (hD : 0 < D)
    (hδ : 0 < δ) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => (Finset.range N).sum fun n => fourierTerm c₀ L D n p.1 p.2)
      (fun p => ∑' n, fourierTerm c₀ L D n p.1 p.2) atTop
      (Set.Icc 0 L ×ˢ Set.Ici δ) := by
  have hM := fourier_dominator_summable c₀ L D δ hL hD hδ
  have hbdd : ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ Set.Icc 0 L ×ˢ Set.Ici δ →
      ‖fourierTerm c₀ L D n p.1 p.2‖
        ≤ (4 * c₀ / Real.pi + 1) * Real.exp (-D * (Real.pi / L) ^ 2 * δ) ^ n := by
    intro n p hp
    have ht : δ ≤ p.2 := Set.mem_Ici.mp (mem_prod.mp hp).2
    exact fourierTerm_bound c₀ L D δ hc₀ hL hD hδ n p.1 p.2 ht
  exact tendstoUniformlyOn_tsum_nat hM hbdd

#print axioms fickFlux
#print axioms fick_continuity_imply_diffusion
#print axioms gauss
#print axioms gauss_xderiv_value
#print axioms gauss_xxderiv_value
#print axioms gauss_tderiv_value
#print axioms gauss_pde
#print axioms gauss_nonneg
#print axioms gauss_mass
#print axioms gauss_weak_limit
#print axioms erfc
#print axioms erfcDeriv
#print axioms erfcDeriv2
#print axioms erfc_zero
#print axioms hasDerivAt_erfc
#print axioms hasDerivAt_erfcDeriv
#print axioms erfc_ode
#print axioms erfc_strictAnti
#print axioms erfc_halfline
#print axioms erfc_tendsto_atTop
#print axioms erfcProfile
#print axioms erfcProfile_xderiv_value
#print axioms erfcProfile_xxderiv_value
#print axioms erfcProfile_tderiv_value
#print axioms erfcProfile_pde
#print axioms erfcProfile_surface
#print axioms erfcProfile_farfield
#print axioms erfcProfile_initial
#print axioms erfc_tail
#print axioms erfc_nonneg
#print axioms erfc_le_gauss
#print axioms erfcProfile_integrableOn
#print axioms profile_pointwise_lt
#print axioms erfcProfile_mass_strictMono
#print axioms energy_identity_deriv
#print axioms diffusion_unique_dirichlet
#print axioms scaledSol
#print axioms similarity_pde
#print axioms simVar
#print axioms simVar_invariant
#print axioms steadyProfile
#print axioms steady_boundary_zero
#print axioms steady_boundary_L
#print axioms steady_xderiv_value
#print axioms steady_pde
#print axioms steady_flux
#print axioms fourierCoeff
#print axioms fourierTerm
#print axioms fourierCoeff_formula
#print axioms fourierTerm_bound
#print axioms fourier_dominator_summable
#print axioms fourier_uniform_convergent

end CondensedMatter.Diffusion

end
