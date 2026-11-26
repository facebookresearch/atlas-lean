/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.PDE.HeatKernel
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Whole-space heat smoothing

For `g` on `EuclideanSpace ℝ (Fin n)` that is a.e. strongly measurable with `|g y| ≤ M` for
almost every `y`, the heat convolution
`u(t, x) = ∫ y, g y * heatKernel (EuclideanSpace ℝ (Fin n)) t (x - y)`, where
`heatKernel E t z = (4πt)^(-n/2) * exp(-‖z‖² / (4t))` is the heat kernel of
`MathlibExt.Analysis.PDE.HeatKernel`, is smooth (`ContDiffOn ℝ ∞`, i.e. `C^∞`) at
positive time, satisfies the heat equation `u_t = Δu` at positive time, and preserves the
constant function `1` at positive time. For finite `p ≥ 1` and compactly supported `C²` data `φ`,
the right-hand difference quotient `(u(t) - φ) / t` converges to `Δφ` in `L^p` as `t → 0⁺`.

`heatConvolution` is meant for `t > 0`. It is not the identity at `t = 0`: for `n > 0` the kernel
vanishes there (`0 ^ (-n / 2) = 0`), so `heatConvolution n g 0 = 0` for every `g`, the constant
`1` included.

## Main definitions

- `heatConvolution n g t x`: the heat convolution `∫ y, g y * heatKernel _ t (x - y)`, for
  `t > 0`. It accepts any `g`; the results take bounded data.

## Main results

- `heat_convolution_smooth`: for a.e. strongly measurable `g` with `|g| ≤ M` a.e., the heat
  convolution is `ContDiffOn ℝ ∞` at positive time. The target is `∞` (`C^∞`), not `⊤`: under
  current Mathlib `ContDiffOn ⊤` means analytic (`ω`), while `∞` means `C^∞` (all finite
  orders). Analyticity is a separate follow-up, not proved here.
- `heat_convolution_satisfies_heat_equation`: for the same `g`, `u_t = Δu` at positive time.
- `heat_convolution_const_one`: the convolution of `1` is `1` at positive time.
- `heat_semigroup_generator_eq_laplacian`: for finite `p ≥ 1` and compactly supported `C²` `φ`,
  `‖heatConvolution n φ t - φ - t * Δφ‖_p / t → 0` as `t → 0⁺`, i.e. the right-hand difference
  quotient converges to `Δφ` in `L^p`; `heat_semigroup_generator_eq_laplacian_ennreal` states it
  with `eLpNorm` in `ENNReal`.

## Implementation notes

The kernel `K_t(z) = heatKernel (EuclideanSpace ℝ (Fin n)) t z` is a Gaussian-times-polynomial
kernel (the class `gaussPolyKernel` with `Q = 1`, `k = 0`), and every such class member is
`ContDiffOn ∞` at positive time: the class is closed under time and space differentiation
(kernel closure identities), the convolution is jointly differentiable (joint `HasFDerivAt` from
its time and space partials), and the `fderiv` of a class member is again a `coprod` of class
members, so induction on the order gives `ContDiffOn ∞`. Specializing to `(Q, k) = (1, 0)` gives
smoothing. The heat equation follows from the time partial, the second space partials, and the
kernel PDE `∂t K = ΔK`, which is `heatKernel_hasDerivAt_time_eq_laplacian` with the Laplacian
expanded in coordinates. The generator follows from the Taylor remainder identity and the `L^p`
estimate.

The file is organized in sections:

- A. Shared definitions and Gaussian integrability
- B. Gaussian moments
- C. Taylor expansion
- D. Kernel closure and domination
- E. Continuity, time and space partials
- F. Joint differentiability and `fderiv` decomposition
- G. Induction to `ContDiffOn ∞` and specialization
- H. Laplacian identification and the kernel PDE
- I. Heat equation assembly
- J. Constant-one
- K. Remainder, modulus, and the `L^p` estimate

## References

- L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies
  in Mathematics 19, American Mathematical Society, 2010, Chapter 2:
  the heat equation, the fundamental solution, and smoothing by
  convolution with the heat kernel (§2.3).
- E. M. Stein and R. Shakarchi, *Fourier Analysis: An Introduction*,
  Princeton Lectures in Analysis I, Princeton University Press, 2003,
  Chapter 5: the heat equation on the line and the Gaussian.
-/

@[expose] public section

namespace MathlibExt.Analysis.PDE.HeatKernel

open MeasureTheory
open scoped Topology
open Filter

/-! ## A. Shared definitions and Gaussian integrability -/

/-- `Φ n` is the heat kernel `heatKernel` on `EuclideanSpace ℝ (Fin n)`:
`Φ n t x = (4πt)^(-n/2) exp(-‖x‖² / (4t))`. -/
local notation:max "Φ" n:max => heatKernel (EuclideanSpace ℝ (Fin n))

/-- **Heat convolution.** For `g : EuclideanSpace ℝ (Fin n) → ℝ` and a time `t`,
`heatConvolution n g t x = ∫ y, g y * heatKernel (EuclideanSpace ℝ (Fin n)) t (x - y)`, the
convolution of `g` with the heat kernel at time `t`. The definition accepts any `g`: where
`y ↦ g y * heatKernel _ t (x - y)` is not integrable, the Bochner integral is `0`. The results of
this file take bounded data: `heat_convolution_smooth` and
`heat_convolution_satisfies_heat_equation` assume `g` a.e. strongly measurable with `|g y| ≤ M`
for almost every `y`, and the generator results take compactly supported `C²` data. It is meant
for `t > 0`: for `n > 0` the kernel vanishes at `t = 0` (`0 ^ (-n / 2) = 0`), so
`heatConvolution n g 0 = 0` for every `g`, the constant `1` included. -/
noncomputable def heatConvolution (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ (y : EuclideanSpace ℝ (Fin n)), g y * heatKernel (EuclideanSpace ℝ (Fin n)) t (x - y)

/-- The heat kernel on `EuclideanSpace ℝ (Fin n)`, with the dimension `n` in the exponent. -/
private theorem heatKernel_euclideanSpace (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Φ n t x = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t)) := by
  unfold heatKernel
  rw [finrank_euclideanSpace_fin]

/-- Gaussians `exp (-b ‖v‖²)` with `0 < b` are integrable on `EuclideanSpace ℝ ι`. Every other
Gaussian integrability result of this file specializes this one. -/
private theorem integrable_real_exp_neg_mul_sq_norm (ι : Type*) [Fintype ι] {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℝ ι => Real.exp (-b * ‖v‖ ^ 2)) volume := by
  have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := (b : ℂ)) (by simpa using hb) (0 : ℂ) (0 : EuclideanSpace ℝ ι)
  refine h0.norm.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero,
    ← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Translated Gaussians `exp (-‖x - y‖² / c)` with `0 < c` are integrable, by translation
invariance of `volume`. -/
private theorem aux_gaussReal_int (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (c0 : ℝ) (hc0 : 0 < c0) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x - y‖ ^ 2 / c0)) := by
  refine ((integrable_real_exp_neg_mul_sq_norm (Fin n) (one_div_pos.mpr hc0)).comp_sub_left
    x).congr (Filter.Eventually.of_forall fun y => ?_)
  change Real.exp (-(1 / c0) * ‖x - y‖ ^ 2) = Real.exp (-‖x - y‖ ^ 2 / c0)
  congr 1
  ring

/-- Polynomial growth is dominated by a Gaussian factor: `(1+r)^D ≤ C * exp (a*r^2)`. -/
private lemma poly_exp_bound_aux (D : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ D ≤ C * Real.exp (a * r ^ 2) := by
  refine ⟨Real.exp ((D : ℝ) ^ 2 / (4 * a)), Real.exp_pos _, fun r hr => ?_⟩
  have h1r : (1 : ℝ) + r ≤ Real.exp r := by
    have h := Real.add_one_le_exp r
    linarith
  have hpow : (1 + r) ^ D ≤ (Real.exp r) ^ D := by
    exact pow_le_pow_left₀ (by positivity) h1r D
  have hexpD : (Real.exp r) ^ D = Real.exp ((D : ℝ) * r) := by
    rw [← Real.exp_nat_mul]
  have hane : a ≠ 0 := ne_of_gt ha
  have h4ane : (4 : ℝ) * a ≠ 0 := mul_ne_zero (by norm_num) hane
  have hAM : (D : ℝ) * r ≤ a * r ^ 2 + (D : ℝ) ^ 2 / (4 * a) := by
    have hsq := sq_nonneg (a * r - (D : ℝ) / 2)
    have h2 : a * ((D : ℝ) * r) ≤ a * (a * r ^ 2) + (D : ℝ) ^ 2 / 4 := by nlinarith [hsq]
    have h3 : (D : ℝ) * r ≤ (a * (a * r ^ 2) + (D : ℝ) ^ 2 / 4) / a := by
      rw [le_div_iff₀ ha]
      linarith [h2]
    have h4 : (a * (a * r ^ 2) + (D : ℝ) ^ 2 / 4) / a = a * r ^ 2 + (D : ℝ) ^ 2 / (4 * a) := by
      field_simp [hane, h4ane]
    rw [h4] at h3
    exact h3
  calc (1 + r) ^ D ≤ (Real.exp r) ^ D := hpow
    _ = Real.exp ((D : ℝ) * r) := hexpD
    _ ≤ Real.exp (a * r ^ 2 + (D : ℝ) ^ 2 / (4 * a)) := Real.exp_le_exp.mpr hAM
    _ = Real.exp ((D : ℝ) ^ 2 / (4 * a)) * Real.exp (a * r ^ 2) := by
        rw [add_comm (a * r ^ 2) _, Real.exp_add]

/-- Polynomial-times-Gaussian is integrable on EuclideanSpace. -/
private lemma integrable_poly_gauss_aux (n : ℕ) (D : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun v : EuclideanSpace ℝ (Fin n) => (1 + ‖v‖) ^ D * Real.exp (-c * ‖v‖ ^ 2))
      volume := by
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  obtain ⟨C, hCpos, hCb⟩ := poly_exp_bound_aux D (c / 2) hc2
  have hG : Integrable (fun v : EuclideanSpace ℝ (Fin n) => Real.exp (-(c / 2) * ‖v‖ ^ 2)) volume :=
    integrable_real_exp_neg_mul_sq_norm (Fin n) hc2
  have hGC : Integrable (fun v : EuclideanSpace ℝ (Fin n) => C * Real.exp (-(c / 2) * ‖v‖ ^ 2))
    volume :=
    hG.const_mul C
  refine hGC.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · apply Continuous.pow
      apply Continuous.add continuous_const continuous_norm
    · apply Real.continuous_exp.comp
      apply Continuous.mul continuous_const
      exact continuous_norm.pow 2
  · filter_upwards with v
    have hr : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
    have hle := hCb ‖v‖ hr
    rw [Real.norm_eq_abs]
    have hnonneg1 : (0 : ℝ) ≤ (1 + ‖v‖) ^ D * Real.exp (-c * ‖v‖ ^ 2) := by positivity
    rw [abs_of_nonneg hnonneg1]
    have hexp : Real.exp (-c * ‖v‖ ^ 2) = Real.exp (-(c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖
      ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    have hCexp : C * Real.exp ((c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖ ^ 2) = C := by
      have h : Real.exp ((c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖ ^ 2) = 1 := by
        rw [← Real.exp_add]
        simp [add_neg_cancel]
      calc C * Real.exp ((c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖ ^ 2)
          = C * (Real.exp ((c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖ ^ 2)) := by ring
        _ = C * 1 := by rw [h]
        _ = C := by ring
    calc (1 + ‖v‖) ^ D * (Real.exp (-(c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖ ^ 2))
        ≤ (C * Real.exp ((c / 2) * ‖v‖ ^ 2)) * (Real.exp (-(c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2)
          * ‖v‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (C * Real.exp ((c / 2) * ‖v‖ ^ 2) * Real.exp (-(c / 2) * ‖v‖ ^ 2)) * Real.exp (-(c / 2) *
        ‖v‖ ^ 2) := by ring
      _ = C * Real.exp (-(c / 2) * ‖v‖ ^ 2) := by rw [hCexp]

/-- Gaussian-times-polynomial kernels. -/
private noncomputable def gaussPolyKernel (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))
    * MvPolynomial.eval (fun i => x i) Q * t ^ (-(k : ℤ))

/-- Iterated coordinate second partial `D_{ij} φ`, as a function. -/
private noncomputable def secondPartialFn (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
    (WithLp.toLp 2 (Function.update x i v)) j r)))
    ((WithLp.toLp 2 (Function.update x i v)) j))
    (x i)

/-- Uniform modulus of `D_{ij} φ`. -/
private noncomputable def secondPartialModulus (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n) (r : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ x z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r
    ∧ v = |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|}

/-- Taylor remainder integrand (the `s`-integral of the second-order term). -/
private noncomputable def Dfn (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
    (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)

/-! ## B. Gaussian moments -/

section Moments

open MeasureTheory ProbabilityTheory

private theorem heatKernel_1d_pdf (t : ℝ) (ht : 0 < t) (v : NNReal) (hv : (v : ℝ) = 2 * t)
    (s : ℝ) :
    gaussianPDFReal 0 v s
      = (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t)) := by
  have hbase : (2:ℝ) * Real.pi * v = 4 * Real.pi * t := by rw [hv]; ring
  have hexp : -(s - 0) ^ 2 / (2 * (v : ℝ)) = -s ^ 2 / (4 * t) := by
    rw [hv, sub_zero]
    have hden : (2:ℝ) * (2 * t) = 4 * t := by ring
    rw [hden]
  have hsqrt : (√(4 * Real.pi * t))⁻¹ = (4 * Real.pi * t) ^ (-(1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ 4 * Real.pi * t)]
    congr 1
    ring
  simp only [gaussianPDFReal, hbase, hexp, hsqrt]

private theorem heatKernel_1d_ne_zero (t : ℝ) (ht : 0 < t) (v : NNReal) (hv : (v : ℝ) = 2 * t) :
    v ≠ 0 := by
  rintro rfl
  simp at hv
  linarith

private theorem heatKernel_1d_mass (t : ℝ) (ht : 0 < t) (v : NNReal) (hv : (v : ℝ) = 2 * t) :
    ∫ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t)) = 1 := by
  have hv0 : v ≠ 0 := heatKernel_1d_ne_zero t ht v hv
  have hpoint : ∀ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))
      = gaussianPDFReal 0 v s :=
    fun s => (heatKernel_1d_pdf t ht v hv s).symm
  simp_rw [hpoint]
  exact integral_gaussianPDFReal_eq_one 0 hv0

private theorem heatKernel_1d_first (t : ℝ) (ht : 0 < t) (v : NNReal) (hv : (v : ℝ) = 2 * t) :
    ∫ s : ℝ, ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))) * s = 0 := by
  have hv0 : v ≠ 0 := heatKernel_1d_ne_zero t ht v hv
  have h := integral_id_gaussianReal (μ := (0:ℝ)) (v := v)
  rw [integral_gaussianReal_eq_integral_smul hv0] at h
  have hpoint : ∀ s : ℝ, ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))) * s
      = gaussianPDFReal 0 v s • s := by
    intro s
    rw [smul_eq_mul, heatKernel_1d_pdf t ht v hv s]
  simp_rw [hpoint]
  exact h

private theorem heatKernel_1d_second (t : ℝ) (ht : 0 < t) (v : NNReal) (hv : (v : ℝ) = 2 * t) :
    ∫ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t)) * s * s
      = 2 * t := by
  have hv0 : v ≠ 0 := heatKernel_1d_ne_zero t ht v hv
  have hvar := variance_fun_id_gaussianReal (μ := (0:ℝ)) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
  simp only [integral_id_gaussianReal] at hvar
  have h2 : (∫ ω : ℝ, ω ^ 2 ∂(gaussianReal 0 v)) = 2 * t := by
    have h3 := hvar
    simp only [sub_zero] at h3
    rwa [hv] at h3
  rw [integral_gaussianReal_eq_integral_smul hv0] at h2
  have hpoint : ∀ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t)) * s * s
      = gaussianPDFReal 0 v s • s ^ 2 := by
    intro s
    rw [smul_eq_mul, heatKernel_1d_pdf t ht v hv s, pow_two]
    ring
  simp_rw [hpoint]
  exact h2

private theorem heatKernel_transfer (n : ℕ) (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin n), F x)
      = ∫ y : Fin n → ℝ, F ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have h := hmp.integral_comp' (fun y : Fin n → ℝ => F ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y))
  simpa using h

private theorem heatKernel_norm_sq (n : ℕ) (y : Fin n → ℝ) :
    ‖(MeasurableEquiv.toLp 2 (Fin n → ℝ)) y‖ ^ 2 = ∑ j, (y j) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

private theorem heatKernel_rpow_prod (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
      = ∏ _j : Fin n, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0:ℝ) ≤ 4 * Real.pi * t := by positivity
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.rpow_natCast _ n, ← Real.rpow_mul hpos]
  congr 1
  ring

private theorem heatKernel_mass_point (n : ℕ) (t : ℝ) (ht : 0 < t) (y : Fin n → ℝ) :
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖(MeasurableEquiv.toLp 2 (Fin n → ℝ)) y‖ ^ 2 / (4 * t))
      = ∏ j, ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(y j) ^ 2 / (4 * t))) := by
  rw [heatKernel_rpow_prod n t ht, heatKernel_norm_sq]
  have hsum : -(∑ j, (y j) ^ 2) / (4 * t) = ∑ j, (-(y j) ^ 2 / (4 * t)) := by
    simp only [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  rw [hsum, Real.exp_sum, Finset.prod_mul_distrib]

private theorem heatKernel_first_point (n : ℕ) (t : ℝ) (ht : 0 < t) (i : Fin n) (y : Fin n → ℝ) :
    ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖(MeasurableEquiv.toLp 2 (Fin n → ℝ)) y‖ ^ 2 / (4 * t)))
        * ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) i
      = ∏ j, ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(y j) ^ 2 / (4 * t))
          * (if j = i then y j else 1)) := by
  have hmass := heatKernel_mass_point n t ht y
  have hite : ∏ j : Fin n, (if j = i then y j else 1) = y i := by simp
  have e1 : ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) i = y i := rfl
  rw [Finset.prod_mul_distrib, hmass, hite, e1]

private theorem heatKernel_second_point (n : ℕ) (t : ℝ) (ht : 0 < t) (i j : Fin n)
    (y : Fin n → ℝ) :
    ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖(MeasurableEquiv.toLp 2 (Fin n → ℝ)) y‖ ^ 2 / (4 * t)))
        * (((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) i * ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) j)
      = ∏ k, ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(y k) ^ 2 / (4 * t))
          * (if k = i then y k else 1) * (if k = j then y k else 1)) := by
  have hmass := heatKernel_mass_point n t ht y
  have hite_i : ∏ k : Fin n, (if k = i then y k else 1) = y i := by simp
  have hite_j : ∏ k : Fin n, (if k = j then y k else 1) = y j := by simp
  have e1 : ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) i = y i := rfl
  have e2 : ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) y) j = y j := rfl
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hmass, hite_i, hite_j, e1, e2]
  ring

/-- Gaussian moments of the heat kernel. -/
private theorem heatKernel_mass (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ y : EuclideanSpace ℝ (Fin n), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1 := by
  have h := integral_heatKernel (E := EuclideanSpace ℝ (Fin n)) ht
  simp only [heatKernel, finrank_euclideanSpace_fin] at h
  exact h

/-- First moment of the heat kernel vanishes. -/
private theorem heatKernel_firstMoment (n : ℕ) {t : ℝ} (ht : 0 < t) (i : Fin n) :
    ∫ y : EuclideanSpace ℝ (Fin n), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0 := by
  have ht' : (0:ℝ) < 2 * t := by linarith
  have hv_eq : ((⟨2 * t, ht'.le⟩ : NNReal) : ℝ) = 2 * t := rfl
  rw [heatKernel_transfer n]
  simp_rw [heatKernel_first_point n t ht i]
  rw [integral_fintype_prod_volume_eq_prod (fun (j : Fin n) (s : ℝ) =>
    (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t)) * (if j = i then s else 1))]
  have hfactor : ∀ j : Fin n, (∫ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2)
      * Real.exp (-s ^ 2 / (4 * t)) * (if j = i then s else 1)) = (if j = i then (0:ℝ) else 1) := by
    intro j
    split_ifs with h
    · exact heatKernel_1d_first t ht _ hv_eq
    · simp only [mul_one]
      exact heatKernel_1d_mass t ht _ hv_eq
  simp_rw [hfactor]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Second moments of the heat kernel: `2t * δ_ij`. -/
private theorem heatKernel_secondMoment (n : ℕ) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    ∫ y : EuclideanSpace ℝ (Fin n), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
      = if i = j then 2 * t else 0 := by
  have ht' : (0:ℝ) < 2 * t := by linarith
  have hv_eq : ((⟨2 * t, ht'.le⟩ : NNReal) : ℝ) = 2 * t := rfl
  rw [heatKernel_transfer n]
  simp_rw [heatKernel_second_point n t ht i j]
  rw [integral_fintype_prod_volume_eq_prod (fun (k : Fin n) (s : ℝ) =>
    (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))
      * (if k = i then s else 1) * (if k = j then s else 1))]
  by_cases h : i = j
  · subst h
    simp only [ite_true]
    have hfactor : ∀ k : Fin n, (∫ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2)
        * Real.exp (-s ^ 2 / (4 * t)) * (if k = i then s else 1) * (if k = i then s else 1))
        = (if k = i then 2 * t else 1) := by
      intro k
      split_ifs with hk
      · exact heatKernel_1d_second t ht _ hv_eq
      · simp only [mul_one]
        exact heatKernel_1d_mass t ht _ hv_eq
    simp_rw [hfactor]
    rw [Finset.prod_eq_single i]
    · simp
    · intro k _ hki
      simp [hki]
    · intro hi
      simp at hi
  · simp only [h, ite_false]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change (∫ s : ℝ, (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))
      * (if i = i then s else 1) * (if i = j then s else 1)) = 0
    simp only [ite_true, h, ite_false, mul_one]
    exact heatKernel_1d_first t ht _ hv_eq

end Moments

/-! ## C. Taylor expansion -/

section Taylor

open MeasureTheory

private lemma lpasms_expand (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    w = ∑ i, (w i) • EuclideanSpace.single i 1 := by
  apply PiLp.ext
  intro j
  have hsum : (∑ i, (w i) • EuclideanSpace.single i (1:ℝ)).ofLp j
      = ∑ i, (((w i) • EuclideanSpace.single i (1:ℝ))).ofLp j := by
    have h := map_sum (PiLp.proj 2 (fun _ : Fin n => ℝ) j :
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun i => (w i) • EuclideanSpace.single i (1:ℝ)) Finset.univ
    simp only [PiLp.proj_apply] at h
    exact h
  rw [hsum]
  simp only [PiLp.smul_apply]
  simp only [EuclideanSpace.single, PiLp.single_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

private lemma lpasms_coord_line (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) (i : Fin n) (r₀ : ℝ) :
    HasDerivAt (fun r => WithLp.toLp 2 (Function.update p i r))
      (EuclideanSpace.single i 1) r₀ := by
  have heq : (fun r => WithLp.toLp 2 (Function.update p i r))
      = fun r => (WithLp.toLp 2 (Function.update p i 0))
          + r • EuclideanSpace.single i (1:ℝ) := by
    funext r
    apply PiLp.ext
    intro j
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    change Function.update p i r j
        = Function.update p i 0 j + r * (EuclideanSpace.single i (1:ℝ)).ofLp j
    rw [Function.update_apply, Function.update_apply]
    show (if j = i then r else p j)
        = (if j = i then (0:ℝ) else p j) + r * (EuclideanSpace.single i (1:ℝ)).ofLp j
    have hsingle : (EuclideanSpace.single i (1:ℝ)).ofLp j = (if j = i then (1:ℝ) else 0) := by
      simp [EuclideanSpace.single, PiLp.single_apply]
    rw [hsingle]
    by_cases hj : j = i <;> simp [hj]
  rw [heq]
  have h1 : HasDerivAt (fun r : ℝ => r • EuclideanSpace.single i (1:ℝ))
      ((1:ℝ) • EuclideanSpace.single i (1:ℝ)) r₀ :=
    (hasDerivAt_id r₀).smul_const _
  rw [one_smul] at h1
  exact HasDerivAt.const_add _ h1

private lemma lpasms_partial_eq (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (q : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (hφ : HasFDerivAt φ L q) :
    L (EuclideanSpace.single i (1:ℝ))
      = deriv (fun r => φ (WithLp.toLp 2 (Function.update q i r))) (q i) := by
  have hpt : (fun r => WithLp.toLp 2 (Function.update q i r)) (q i) = q := by
    change WithLp.toLp 2 (Function.update q i (q i)) = q
    rw [Function.update_eq_self]
  have hφ' : HasFDerivAt φ L
      ((fun r => WithLp.toLp 2 (Function.update q i r)) (q i)) := by
    rw [hpt]
    exact hφ
  have hci := hφ'.comp_hasDerivAt (q i) (lpasms_coord_line n q i (q i))
  exact hci.deriv.symm

private lemma lpasms_chain1 (n : ℕ) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (s : ℝ) (w : EuclideanSpace ℝ (Fin n)) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hφ : HasFDerivAt φ L (c s)) (hc : HasDerivAt c w s) :
    HasDerivAt (fun s => φ (c s))
      (∑ i, (w i) * deriv (fun r => φ (WithLp.toLp 2 (Function.update (c s) i r))) ((c s) i)) s :=
        by
  have hcomp : HasDerivAt (fun s => φ (c s)) (L w) s := hφ.comp_hasDerivAt s hc
  have hLw : L w
      = ∑ i, (w i) * deriv (fun r => φ (WithLp.toLp 2 (Function.update (c s) i r))) ((c s) i) := by
    conv_lhs => rw [lpasms_expand n w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, smul_eq_mul, lpasms_partial_eq n φ (c s) i L hφ]
  rw [hLw] at hcomp
  exact hcomp

private lemma lpasms_taylor1 (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    g 1 - g 0 - deriv g 0 = ∫ s in (0:ℝ)..1, (1 - s) * deriv (deriv g) s := by
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hdd : Differentiable ℝ (deriv g) := ContDiff.differentiable_deriv_two hg
  have hcg : Continuous (deriv g) := hg1.continuous
  have hcdd : Continuous (deriv (deriv g)) := ContDiff.continuous_deriv hg1 le_rfl
  have hu : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x => 1 - x) (-1) x := by
    intro x _
    exact (hasDerivAt_id x).const_sub (1:ℝ)
  have hv : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (deriv g) (deriv (deriv g) x) x :=
    fun x _ => (hdd x).hasDerivAt
  have hibp : ∫ x in (0:ℝ)..1, (-1:ℝ) * deriv g x + (1 - x) * deriv (deriv g) x
      = (1 - (1:ℝ)) * deriv g 1 - (1 - 0) * deriv g 0 :=
    intervalIntegral.integral_deriv_mul_eq_sub (a := (0:ℝ)) (b := 1)
      (u := fun x => 1 - x) (v := deriv g) (u' := fun _ => (-1:ℝ)) (v' := deriv (deriv g))
      hu hv (continuous_const.intervalIntegrable _ _) (hcdd.intervalIntegrable _ _)
  have hftc : ∫ x in (0:ℝ)..1, deriv g x = g 1 - g 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hgd x) (hcg.intervalIntegrable _ _)
  have hint1 : IntervalIntegrable (fun x : ℝ => (-1:ℝ) * deriv g x) volume 0 1 :=
    (continuous_const.mul hcg).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun x : ℝ => (1 - x) * deriv (deriv g) x) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul hcdd).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hint1 hint2] at hibp
  rw [intervalIntegral.integral_const_mul] at hibp
  rw [hftc] at hibp
  linear_combination -hibp

private lemma lpasms_curve_deriv (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    HasDerivAt (fun s => x - s • y) (-y) s := by
  have h := HasDerivAt.const_sub x ((hasDerivAt_id s).smul_const y)
  rw [one_smul] at h
  exact h

private lemma lpasms_curve_smooth (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 2 (fun s : ℝ => x - s • y) :=
  contDiff_const.sub (contDiff_id.smul contDiff_const)

private lemma lpasms_partial_smooth (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (i : Fin n) :
    ContDiff ℝ 1 (fun q => (fderiv ℝ φ q) (EuclideanSpace.single i (1:ℝ))) := by
  have hff : ContDiff ℝ 1
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ φ p.1) p.2) :=
    hφ.contDiff_fderiv_apply (m := 1) (by decide)
  have hpair : ContDiff ℝ 1
      (fun q : EuclideanSpace ℝ (Fin n) => (q, EuclideanSpace.single i (1:ℝ))) :=
    contDiff_id.prodMk contDiff_const
  exact hff.comp hpair

/-- Second-order Taylor expansion with integral remainder, in
coordinates, for a `C²` function, with the iterated partials in the
form used by the heat-semigroup generator assembly. -/
private theorem taylor_two_integral_remainder_lpasm (n : ℕ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x y : EuclideanSpace ℝ (Fin n)) :
    φ (x - y) - φ x + ∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)
      = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i) := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hcs : ∀ (s : ℝ), HasDerivAt (fun s : ℝ => x - s • y) (-y) s :=
    fun s => lpasms_curve_deriv n x y s
  have hcsd : ∀ (s : ℝ), DifferentiableAt ℝ (fun s : ℝ => x - s • y) s :=
    fun s => (hcs s).differentiableAt
  have hneg : ∀ i : Fin n, ((-y) i) = -(y i) := fun i => PiLp.neg_apply _ _ _
  have hψd : ∀ (i : Fin n) (q : EuclideanSpace ℝ (Fin n)),
      DifferentiableAt ℝ
        (fun q : EuclideanSpace ℝ (Fin n) =>
          deriv (fun r => φ (WithLp.toLp 2 (Function.update q i r))) (q i)) q := by
    intro i q
    have heq : (fun q : EuclideanSpace ℝ (Fin n) =>
          deriv (fun r => φ (WithLp.toLp 2 (Function.update q i r))) (q i))
        = fun q : EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ φ q) (EuclideanSpace.single i (1:ℝ)) := by
      funext q
      exact (lpasms_partial_eq n φ q i _ ((hφd q).hasFDerivAt)).symm
    rw [heq]
    exact ((lpasms_partial_smooth n φ hφ i).differentiable (by decide)) q
  have hψcd : ∀ (i : Fin n) (s : ℝ),
      DifferentiableAt ℝ
        (fun s : ℝ => deriv (fun r => φ (WithLp.toLp 2 (Function.update (x - s • y) i r)))
          ((x - s • y) i)) s := by
    intro i s
    exact (hψd i (x - s • y)).comp s (hcsd s)
  have hder1 : ∀ (s : ℝ), deriv (fun s : ℝ => φ (x - s • y)) s
      = ∑ i, ((-y) i) * deriv (fun r => φ (WithLp.toLp 2 (Function.update (x - s • y) i r)))
          ((x - s • y) i) := by
    intro s
    exact (lpasms_chain1 n (fun s : ℝ => x - s • y) φ s (-y) (fderiv ℝ φ (x - s • y))
      ((hφd _).hasFDerivAt) (hcs s)).deriv
  have hdi : ∀ (i : Fin n) (s : ℝ),
      deriv (fun s : ℝ => ((-y) i) * deriv (fun r => φ (WithLp.toLp 2
        (Function.update (x - s • y) i r))) ((x - s • y) i)) s
      = ((-y) i) * (∑ j, ((-y) j) *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) j v)) i r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) j v)) i))
            ((x - s • y) j)) := by
    intro i s
    rw [deriv_const_mul _ (hψcd i s)]
    congr 1
    exact (lpasms_chain1 n (fun s : ℝ => x - s • y)
      (fun q : EuclideanSpace ℝ (Fin n) =>
        deriv (fun r => φ (WithLp.toLp 2 (Function.update q i r))) (q i))
      s (-y) _ ((hψd i _).hasFDerivAt) (hcs s)).deriv
  have hder2 : ∀ (s : ℝ), deriv (deriv (fun s : ℝ => φ (x - s • y))) s
      = ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i) := by
    intro s
    have hfun : deriv (fun s : ℝ => φ (x - s • y))
        = ∑ i, fun s : ℝ => ((-y) i) * deriv (fun r => φ (WithLp.toLp 2
          (Function.update (x - s • y) i r))) ((x - s • y) i) := by
      funext s
      rw [hder1 s, Finset.sum_apply]
    have hsumdiff : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        DifferentiableAt ℝ (fun s : ℝ => ((-y) i) * deriv (fun r => φ (WithLp.toLp 2
          (Function.update (x - s • y) i r))) ((x - s • y) i)) s := by
      intro i _
      exact (hψcd i s).const_mul _
    rw [hfun, deriv_sum hsumdiff]
    simp only [hdi]
    simp only [hneg]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hg2 : ContDiff ℝ 2 (fun s : ℝ => φ (x - s • y)) :=
    hφ.comp (lpasms_curve_smooth n x y)
  have htaylor := lpasms_taylor1 (fun s : ℝ => φ (x - s • y)) hg2
  have hg1 : φ (x - (1:ℝ) • y) = φ (x - y) := by
    rw [one_smul]
  have hg0 : φ (x - (0:ℝ) • y) = φ x := by
    rw [zero_smul, sub_zero]
  have hdg0 : deriv (fun s : ℝ => φ (x - s • y)) 0
      = -(∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) := by
    rw [hder1 0]
    simp only [zero_smul, sub_zero, hneg, neg_mul]
    exact Finset.sum_neg_distrib _
  rw [hg1, hg0, hdg0] at htaylor
  have hint : ∀ s : ℝ, (1 - s) * deriv (deriv (fun s : ℝ => φ (x - s • y))) s
      = (1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i) := fun s => by rw [hder2 s]
  simp only [hint] at htaylor
  linear_combination htaylor

end Taylor

/-! ## D. Kernel closure and domination -/

section Closures

open MeasureTheory


/-- Derivative of a polynomial evaluation along a coordinate update. -/
private theorem hasDerivAt_eval_update (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (f : Fin n → ℝ)
    (i : Fin n) (r : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (Function.update f i s) Q)
      (MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i Q)) r := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.pderiv_C, MvPolynomial.eval_C, map_zero]
      exact hasDerivAt_const _ _
  | add p q hp hq =>
      have h : HasDerivAt
          ((fun s => MvPolynomial.eval (Function.update f i s) p)
            + (fun s => MvPolynomial.eval (Function.update f i s) q))
          ((MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i p))
            + (MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i q))) r :=
        hp.add hq
      have hfun : ((fun s => MvPolynomial.eval (Function.update f i s) p)
          + (fun s => MvPolynomial.eval (Function.update f i s) q))
          = (fun s => MvPolynomial.eval (Function.update f i s) (p + q)) := by
        funext s
        simp only [Pi.add_apply, map_add]
      have hval : (MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i p))
          + (MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i q))
          = MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i (p + q)) := by
        simp only [map_add]
      rw [hfun, hval] at h
      exact h
  | mul_X p j hp =>
      by_cases hji : j = i
      · rw [hji]
        have hX : HasDerivAt (fun s : ℝ => Function.update f i s i) 1 r := by
          simpa using hasDerivAt_id' r
        have h : HasDerivAt
            ((fun s => MvPolynomial.eval (Function.update f i s) p)
              * (fun s : ℝ => Function.update f i s i))
            ((MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i p))
              * Function.update f i r i
              + (MvPolynomial.eval (Function.update f i r) p) * 1) r :=
          hp.mul hX
        have hfun : ((fun s => MvPolynomial.eval (Function.update f i s) p)
            * (fun s : ℝ => Function.update f i s i))
            = (fun s => MvPolynomial.eval (Function.update f i s)
              (p * MvPolynomial.X i)) := by
          funext s
          simp only [Pi.mul_apply, map_mul, MvPolynomial.eval_X]
        have hval : (MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i p))
            * Function.update f i r i
            + (MvPolynomial.eval (Function.update f i r) p) * 1
            = MvPolynomial.eval (Function.update f i r)
              (MvPolynomial.pderiv i (p * MvPolynomial.X i)) := by
          rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.eval_X,
            MvPolynomial.pderiv_X_self, map_one]
        rw [hfun, hval] at h
        exact h
      · have hX : HasDerivAt (fun s : ℝ => Function.update f i s j) 0 r := by
          have h2 : (fun s : ℝ => Function.update f i s j) = (fun _ => f j) := by
            funext s
            exact Function.update_of_ne hji _ _
          rw [h2]
          exact hasDerivAt_const _ _
        have h : HasDerivAt
            ((fun s => MvPolynomial.eval (Function.update f i s) p)
              * (fun s : ℝ => Function.update f i s j))
            ((MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i p))
              * Function.update f i r j
              + (MvPolynomial.eval (Function.update f i r) p) * 0) r :=
          hp.mul hX
        have hfun : ((fun s => MvPolynomial.eval (Function.update f i s) p)
            * (fun s : ℝ => Function.update f i s j))
            = (fun s => MvPolynomial.eval (Function.update f i s)
              (p * MvPolynomial.X j)) := by
          funext s
          simp only [Pi.mul_apply, map_mul, MvPolynomial.eval_X]
        have hval : (MvPolynomial.eval (Function.update f i r) (MvPolynomial.pderiv i p))
            * Function.update f i r j
            + (MvPolynomial.eval (Function.update f i r) p) * 0
            = MvPolynomial.eval (Function.update f i r)
              (MvPolynomial.pderiv i (p * MvPolynomial.X j)) := by
          rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.eval_X,
            MvPolynomial.pderiv_X_of_ne hji, map_zero]
        rw [hfun, hval] at h
        exact h

/-- Time derivative of the kernel is a sum of two class members. -/
private theorem gaussPolyKernel_deriv_time (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => gaussPolyKernel n Q k s x) t
      = gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t x
        + gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2) t x := by
  have ht' : t ≠ 0 := ht.ne'
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4t : (4 : ℝ) * Real.pi * t ≠ 0 := by
    have h1 : (4 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt hpi)
    exact mul_ne_zero h1 ht'
  have h4tpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have h4t2 : (4 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht'
  have hlin : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
    have h := HasDerivAt.const_mul (4 * Real.pi) (hasDerivAt_id' t)
    simpa using h
  have hlin2 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
    have h := HasDerivAt.const_mul (4 : ℝ) (hasDerivAt_id' t)
    simpa using h
  have hA : HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-(n : ℝ) / 2))
      ((4 * Real.pi) * (-(n : ℝ) / 2) * (4 * Real.pi * t) ^ (-(n : ℝ) / 2 - 1)) t := by
    exact hlin.rpow_const (Or.inl h4t)
  have hc0 : HasDerivAt (fun _ : ℝ => -‖x‖ ^ 2) 0 t := hasDerivAt_const _ _
  have hφ : HasDerivAt (fun s : ℝ => -‖x‖ ^ 2 / (4 * s))
      ((0 * (4 * t) - (-‖x‖ ^ 2) * 4) / (4 * t) ^ 2) t := by
    exact hc0.div hlin2 h4t2
  have hB : HasDerivAt (fun s : ℝ => Real.exp (-‖x‖ ^ 2 / (4 * s)))
      (Real.exp (-‖x‖ ^ 2 / (4 * t))
        * ((0 * (4 * t) - (-‖x‖ ^ 2) * 4) / (4 * t) ^ 2)) t :=
    hφ.exp
  have hC : HasDerivAt (fun s : ℝ => s ^ (-(k : ℤ)))
      (((-(k : ℤ) : ℤ) : ℝ) * t ^ (-(k : ℤ) - 1)) t := by
    exact hasDerivAt_zpow _ _ (Or.inl ht')
  have hAB : HasDerivAt
      (fun s : ℝ => (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s)))
      (((4 * Real.pi) * (-(n : ℝ) / 2) * (4 * Real.pi * t) ^ (-(n : ℝ) / 2 - 1))
        * Real.exp (-‖x‖ ^ 2 / (4 * t))
        + (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * (Real.exp (-‖x‖ ^ 2 / (4 * t))
            * ((0 * (4 * t) - (-‖x‖ ^ 2) * 4) / (4 * t) ^ 2))) t :=
    hA.mul hB
  have hABP : HasDerivAt
      (fun s : ℝ => (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * s))
        * MvPolynomial.eval (fun i => x i) Q)
      ((((4 * Real.pi) * (-(n : ℝ) / 2) * (4 * Real.pi * t) ^ (-(n : ℝ) / 2 - 1))
        * Real.exp (-‖x‖ ^ 2 / (4 * t))
        + (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * (Real.exp (-‖x‖ ^ 2 / (4 * t))
            * ((0 * (4 * t) - (-‖x‖ ^ 2) * 4) / (4 * t) ^ 2)))
        * MvPolynomial.eval (fun i => x i) Q) t :=
    hAB.mul_const _
  have hfull : HasDerivAt (fun s : ℝ => gaussPolyKernel n Q k s x)
      (((((4 * Real.pi) * (-(n : ℝ) / 2) * (4 * Real.pi * t) ^ (-(n : ℝ) / 2 - 1))
        * Real.exp (-‖x‖ ^ 2 / (4 * t))
        + (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * (Real.exp (-‖x‖ ^ 2 / (4 * t))
            * ((0 * (4 * t) - (-‖x‖ ^ 2) * 4) / (4 * t) ^ 2)))
        * MvPolynomial.eval (fun i => x i) Q)
        * t ^ (-(k : ℤ))
        + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))
          * MvPolynomial.eval (fun i => x i) Q)
          * (((-(k : ℤ) : ℤ) : ℝ) * t ^ (-(k : ℤ) - 1))) t :=
    hABP.mul hC
  have hmain := hfull.deriv
  rw [hmain]
  simp only [gaussPolyKernel]
  have eval1 : MvPolynomial.eval (fun i => x i) (-(((n : ℝ) / 2 + (k : ℝ)) • Q))
      = -(((n : ℝ) / 2 + (k : ℝ))) * MvPolynomial.eval (fun i => x i) Q := by
    rw [map_neg, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, neg_mul]
  have hsum : MvPolynomial.eval (fun i => x i) (∑ i, MvPolynomial.X i ^ 2) = ‖x‖ ^ 2 := by
    rw [map_sum]
    simp_rw [map_pow, MvPolynomial.eval_X]
    exact (EuclideanSpace.real_norm_sq_eq x).symm
  have eval2 : MvPolynomial.eval (fun i => x i) ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
      = (1 / 4 : ℝ) * (MvPolynomial.eval (fun i => x i) Q * ‖x‖ ^ 2) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hsum]
  have hexp1 : (-((k + 1 : ℕ) : ℤ) : ℤ) = -(k : ℤ) - 1 := by push_cast; ring
  have hexp2 : (-((k + 2 : ℕ) : ℤ) : ℤ) = -(k : ℤ) - 2 := by push_cast; ring
  have hz1 : t ^ (-(k : ℤ) - 1) = t ^ (-(k : ℤ)) / t := by
    rw [zpow_sub_one₀ ht', div_eq_mul_inv]
  have hz2 : t ^ (-(k : ℤ) - 2) = t ^ (-(k : ℤ)) / t ^ 2 := by
    have e : (-(k : ℤ) - 2 : ℤ) = (-(k : ℤ) - 1) - 1 := by ring
    rw [e, zpow_sub_one₀ ht', zpow_sub_one₀ ht']
    rw [div_eq_mul_inv, sq, mul_inv]
    ring
  have hrpow : (4 * Real.pi * t) ^ (-(n : ℝ) / 2 - 1)
      = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) / (4 * Real.pi * t) := by
    rw [Real.rpow_sub h4tpos, Real.rpow_one]
  rw [eval1, eval2, hexp1, hexp2, hz1, hz2, hrpow]
  have h4t2sq : ((4 : ℝ) * t) ^ 2 ≠ 0 := pow_ne_zero 2 h4t2
  have ht2 : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 ht'
  push_cast
  field_simp [ht', h4t, h4t2, h4t2sq, ht2]
  ring

/-- Space derivative of the kernel is a sum of two class members. -/
private theorem gaussPolyKernel_deriv_space (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    deriv (fun s => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update x i s))) (x i)
      = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t x
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t x := by
  have ht' : t ≠ 0 := ht.ne'
  have h4t2 : (4 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht'
  have hupd0 : Function.update (WithLp.ofLp x) i ((x : EuclideanSpace ℝ (Fin n)).ofLp i)
      = WithLp.ofLp x :=
    Function.update_eq_self_iff.mpr rfl
  have hy0 : (WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) = x := by
    simp only [hupd0, WithLp.toLp_ofLp]
  have hnormeq : ∀ s : ℝ,
      ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖ ^ 2
      = (‖x‖ ^ 2 - (x i) ^ 2) + s ^ 2 := by
    intro s
    rw [EuclideanSpace.real_norm_sq_eq]
    have hterm : ∀ j : Fin n,
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) j) ^ 2
        = Function.update (fun j => (x j) ^ 2) i (s ^ 2) j := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    simp_rw [hterm]
    have e1 : ∑ j, Function.update (fun j => (x j) ^ 2) i (s ^ 2) j
        = s ^ 2 + ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 := by
      have h := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (x j) ^ 2) (s ^ 2)
      rw [Finset.sdiff_singleton_eq_erase] at h
      exact h
    have hsplit : (x i) ^ 2 + ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 = ∑ j, (x j) ^ 2 :=
      Finset.add_sum_erase _ (fun j => (x j) ^ 2) (Finset.mem_univ i)
    have hnormx : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := EuclideanSpace.real_norm_sq_eq x
    linear_combination e1 + hsplit - hnormx
  have hnorm : HasDerivAt
      (fun s : ℝ => ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      (2 * x i) (x i) := by
    have hsq : HasDerivAt (fun s : ℝ => (‖x‖ ^ 2 - (x i) ^ 2) + s ^ 2) (2 * x i) (x i) := by
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x i) (x i) := by
        have h := hasDerivAt_pow 2 (x i)
        rwa [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat] at h
      have h : HasDerivAt
          ((fun _ : ℝ => (‖x‖ ^ 2 - (x i) ^ 2)) + (fun s : ℝ => s ^ 2))
          (0 + 2 * x i) (x i) :=
        (hasDerivAt_const _ _).add h2
      have hfun : ((fun _ : ℝ => (‖x‖ ^ 2 - (x i) ^ 2)) + (fun s : ℝ => s ^ 2))
          = (fun s : ℝ => (‖x‖ ^ 2 - (x i) ^ 2) + s ^ 2) := by
        funext s
        simp only [Pi.add_apply]
      rw [hfun] at h
      simpa using h
    have hfun : (fun s : ℝ => ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖
      ^ 2)
        = (fun s : ℝ => (‖x‖ ^ 2 - (x i) ^ 2) + s ^ 2) := funext hnormeq
    rw [hfun]
    exact hsq
  have hψ : HasDerivAt
      (fun s : ℝ => -‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (4
        * t))
      ((-(2 * x i)) / (4 * t)) (x i) :=
    hnorm.neg.div_const _
  have hB : HasDerivAt
      (fun s : ℝ => Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖
        ^ 2 / (4 * t)))
      (Real.exp (-‖x‖ ^ 2 / (4 * t)) * ((-(2 * x i)) / (4 * t))) (x i) := by
    have h : HasDerivAt
        (fun s : ℝ => Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin
          n))‖ ^ 2 / (4 * t)))
        (Real.exp (-‖(WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 /
          (4 * t))
          * ((-(2 * x i)) / (4 * t))) (x i) :=
      hψ.exp
    rw [hy0] at h
    exact h
  have hPfun : (fun s : ℝ => MvPolynomial.eval
        (fun j => (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) j) Q)
      = (fun s : ℝ => MvPolynomial.eval (Function.update (WithLp.ofLp x) i s) Q) := by
    funext s
    have hpt : (fun j => (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) j)
        = Function.update (WithLp.ofLp x) i s :=
      funext fun j => PiLp.toLp_apply _ _ _ _
    rw [hpt]
  have hPval : MvPolynomial.eval (Function.update (WithLp.ofLp x) i (x i))
      (MvPolynomial.pderiv i Q)
      = MvPolynomial.eval (fun a => (x : EuclideanSpace ℝ (Fin n)) a)
        (MvPolynomial.pderiv i Q) := by
    rw [hupd0]
  have hP : HasDerivAt
      (fun s : ℝ => MvPolynomial.eval
        (fun j => (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) j) Q)
      (MvPolynomial.eval (fun a => (x : EuclideanSpace ℝ (Fin n)) a)
        (MvPolynomial.pderiv i Q)) (x i) := by
    have h := hasDerivAt_eval_update n Q (WithLp.ofLp x) i (x i)
    rw [← hPfun, hPval] at h
    exact h
  have hAB : HasDerivAt
      (fun s : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (4
          * t)))
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * (Real.exp (-‖x‖ ^ 2 / (4 * t)) * ((-(2 * x i)) / (4 * t)))) (x i) :=
    HasDerivAt.const_mul _ hB
  have hABP : HasDerivAt
      (fun s : ℝ => ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / (4
          * t)))
        * MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ
          (Fin n)) j) Q)
      (((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * (Real.exp (-‖x‖ ^ 2 / (4 * t)) * ((-(2 * x i)) / (4 * t))))
        * MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ
          (Fin n)) j) Q
        + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖(WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n))‖ ^ 2
            / (4 * t)))
          * MvPolynomial.eval (fun a => (x : EuclideanSpace ℝ (Fin n)) a)
            (MvPolynomial.pderiv i Q)) (x i) :=
    hAB.mul hP
  have hfull : HasDerivAt
      (fun s : ℝ => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update x i s)))
      (((((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * (Real.exp (-‖x‖ ^ 2 / (4 * t)) * ((-(2 * x i)) / (4 * t))))
        * MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ
          (Fin n)) j) Q
        + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖(WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n))‖ ^ 2
            / (4 * t)))
          * MvPolynomial.eval (fun a => (x : EuclideanSpace ℝ (Fin n)) a)
            (MvPolynomial.pderiv i Q)))
        * t ^ (-(k : ℤ))) (x i) :=
    hABP.mul_const _
  have hmain := hfull.deriv
  rw [hmain]
  simp only [gaussPolyKernel]
  simp only [hupd0]
  have evalX : MvPolynomial.eval (fun a => (x : EuclideanSpace ℝ (Fin n)) a)
      (((-1 / 2 : ℝ)) • (MvPolynomial.X i * Q))
      = (-1 / 2 : ℝ) * ((x i) * MvPolynomial.eval (fun a => (x : EuclideanSpace ℝ (Fin n)) a) Q) :=
        by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hexp1 : (-((k + 1 : ℕ) : ℤ) : ℤ) = -(k : ℤ) - 1 := by push_cast; ring
  have hz1 : t ^ (-(k : ℤ) - 1) = t ^ (-(k : ℤ)) / t := by
    rw [zpow_sub_one₀ ht', div_eq_mul_inv]
  rw [evalX, hexp1, hz1]
  field_simp [ht', h4t2]
  ring

end Closures

section Domination

open MeasureTheory


/-- Coordinates are bounded by one plus the norm. -/
private lemma coord_le_one_add_norm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ 1 + ‖x‖ := by
  have h : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at h
  have hn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  linarith

/-- Polynomial bound: `|eval|` is at most a constant times `(1 + ‖x‖) ^ D`. -/
private lemma mvpoly_eval_le (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, ∃ D : ℕ, 0 < C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      |MvPolynomial.eval (fun i => x i) Q| ≤ C * (1 + ‖x‖) ^ D := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨|a| + 1, 0, by positivity, fun x => ?_⟩
    simp only [MvPolynomial.eval_C, pow_zero, mul_one]
    exact le_add_of_nonneg_right zero_le_one
  | add p q hp hq =>
    obtain ⟨Cp, Dp, hCp, hp⟩ := hp
    obtain ⟨Cq, Dq, hCq, hq⟩ := hq
    refine ⟨Cp + Cq, max Dp Dq, add_pos hCp hCq, fun x => ?_⟩
    simp only [MvPolynomial.eval_add]
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
    have hp' : Cp * (1 + ‖x‖) ^ Dp ≤ Cp * (1 + ‖x‖) ^ max Dp Dq :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_left Dp Dq)) (le_of_lt hCp)
    have hq' : Cq * (1 + ‖x‖) ^ Dq ≤ Cq * (1 + ‖x‖) ^ max Dp Dq :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (le_max_right Dp Dq)) (le_of_lt hCq)
    calc |MvPolynomial.eval (fun i => x i) p + MvPolynomial.eval (fun i => x i) q|
        ≤ |MvPolynomial.eval (fun i => x i) p| + |MvPolynomial.eval (fun i => x i) q| :=
          abs_add_le _ _
      _ ≤ Cp * (1 + ‖x‖) ^ max Dp Dq + Cq * (1 + ‖x‖) ^ max Dp Dq :=
          add_le_add (le_trans (hp x) hp') (le_trans (hq x) hq')
      _ = (Cp + Cq) * (1 + ‖x‖) ^ max Dp Dq := (add_mul _ _ _).symm
  | mul_X p j hp =>
    obtain ⟨C, D, hC, hp⟩ := hp
    refine ⟨C, D + 1, hC, fun x => ?_⟩
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, abs_mul]
    have hC0 : (0 : ℝ) ≤ C * (1 + ‖x‖) ^ D :=
      mul_nonneg (le_of_lt hC) (pow_nonneg (by positivity) D)
    have hle : |MvPolynomial.eval (fun i => x i) p| * |x j|
        ≤ (C * (1 + ‖x‖) ^ D) * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg' (hp x) (coord_le_one_add_norm n x j) (abs_nonneg _) hC0
    calc |MvPolynomial.eval (fun i => x i) p| * |x j|
        ≤ (C * (1 + ‖x‖) ^ D) * (1 + ‖x‖) := hle
      _ = C * (1 + ‖x‖) ^ (D + 1) := by rw [pow_succ']; ring

/-- Elementary exponential lower bound: `(y / m) ^ m ≤ exp y` for `y ≥ 0`. -/
private lemma pow_div_le_exp (y : ℝ) (m : ℕ) (hy : 0 ≤ y) (hm : 1 ≤ m) :
    (y / m) ^ m ≤ Real.exp y := by
  have hmpos' : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hmpos'
  have hz : (0 : ℝ) ≤ y / m := div_nonneg hy (Nat.cast_nonneg m)
  have h1 : y / m ≤ Real.exp (y / m) := by
    have h := Real.add_one_le_exp (y / m)
    linarith
  have hmy : (m : ℝ) * (y / m) = y := by field_simp
  calc (y / m) ^ m ≤ (Real.exp (y / m)) ^ m := pow_le_pow_left₀ hz h1 m
    _ = Real.exp y := by rw [← Real.exp_nat_mul, hmy]

/-- Polynomial growth is beaten by Gaussian growth. -/
private lemma poly_le_exp_mul (D : ℕ) (t0 : ℝ) (ht0 : 0 < t0) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ D ≤ C * Real.exp (r ^ 2 / (16 * t0)) := by
  set m : ℕ := D + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have h16 : (0 : ℝ) < 16 * t0 * m := by positivity
  have h16t0 : (0 : ℝ) < 16 * t0 := by positivity
  refine ⟨(2 ^ D) * ((16 * t0 * m) ^ m + 1), ?_, fun r hr => ?_⟩
  · exact mul_pos (pow_pos zero_lt_two D)
      (add_pos_of_nonneg_of_pos (pow_nonneg (le_of_lt h16) m) zero_lt_one)
  · have hK1 : (1 : ℝ) ≤ (16 * t0 * m) ^ m + 1 :=
      le_add_of_nonneg_left (pow_nonneg (le_of_lt h16) m)
    by_cases hr1 : r ≤ 1
    · have h1r : (1 : ℝ) + r ≤ 2 := by linarith
      have hbase : (0 : ℝ) ≤ 1 + r := by linarith
      have hexp1 : (1 : ℝ) ≤ Real.exp (r ^ 2 / (16 * t0)) :=
        Real.one_le_exp (div_nonneg (sq_nonneg r) (le_of_lt h16t0))
      have hKE : (1 : ℝ) ≤ ((16 * t0 * m) ^ m + 1) * Real.exp (r ^ 2 / (16 * t0)) :=
        one_le_mul_of_one_le_of_one_le hK1 hexp1
      calc (1 + r) ^ D ≤ 2 ^ D := pow_le_pow_left₀ hbase h1r D
        _ = 2 ^ D * 1 := (mul_one _).symm
        _ ≤ 2 ^ D * (((16 * t0 * m) ^ m + 1) * Real.exp (r ^ 2 / (16 * t0))) :=
            mul_le_mul_of_nonneg_left hKE (pow_nonneg zero_le_two D)
        _ = (2 ^ D * ((16 * t0 * m) ^ m + 1)) * Real.exp (r ^ 2 / (16 * t0)) := by ring
    · push Not at hr1
      have hr1' : (1 : ℝ) ≤ r := le_of_lt hr1
      have h2r : (1 : ℝ) + r ≤ 2 * r := by linarith
      have hbase : (0 : ℝ) ≤ 1 + r := by linarith
      have hD2m : D ≤ 2 * m := by omega
      have hrD : r ^ D ≤ r ^ (2 * m) := pow_le_pow_right₀ hr1' hD2m
      have hy : (0 : ℝ) ≤ r ^ 2 / (16 * t0) :=
        div_nonneg (sq_nonneg r) (le_of_lt h16t0)
      have hpm : ((r ^ 2 / (16 * t0)) / m) ^ m ≤ Real.exp (r ^ 2 / (16 * t0)) :=
        pow_div_le_exp _ m hy hm1
      have h16ne : (16 : ℝ) * t0 ≠ 0 := ne_of_gt h16t0
      have hfactor : r ^ (2 * m)
          = (16 * t0 * m) ^ m * (((r ^ 2 / (16 * t0)) / m)) ^ m := by
        rw [← mul_pow, pow_mul]
        congr 1
        field_simp
      have key : (1 + r) ^ D
          ≤ 2 ^ D * (16 * t0 * m) ^ m * Real.exp (r ^ 2 / (16 * t0)) := by
        calc (1 + r) ^ D ≤ (2 * r) ^ D := pow_le_pow_left₀ hbase h2r D
          _ = 2 ^ D * r ^ D := by rw [mul_pow]
          _ ≤ 2 ^ D * r ^ (2 * m) :=
              mul_le_mul_of_nonneg_left hrD (pow_nonneg zero_le_two D)
          _ = 2 ^ D * ((16 * t0 * m) ^ m * (((r ^ 2 / (16 * t0)) / m)) ^ m) := by
              rw [hfactor]
          _ ≤ 2 ^ D * ((16 * t0 * m) ^ m * Real.exp (r ^ 2 / (16 * t0))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpm (pow_nonneg (le_of_lt h16) m))
                (pow_nonneg zero_le_two D)
          _ = 2 ^ D * (16 * t0 * m) ^ m * Real.exp (r ^ 2 / (16 * t0)) := by ring
      have hKm : (16 * t0 * m) ^ m ≤ (16 * t0 * m) ^ m + 1 :=
        le_add_of_nonneg_right zero_le_one
      calc (1 + r) ^ D ≤ 2 ^ D * (16 * t0 * m) ^ m * Real.exp (r ^ 2 / (16 * t0)) := key
        _ ≤ (2 ^ D * ((16 * t0 * m) ^ m + 1)) * Real.exp (r ^ 2 / (16 * t0)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKm (pow_nonneg zero_le_two D))
              (le_of_lt (Real.exp_pos _))

/-- The rpow prefactor is bounded on the compact time interval. -/
private lemma prefactor_bound (n : ℕ) (t0 t : ℝ) (ht0 : 0 < t0)
    (hlo : t0 / 2 ≤ t) (_hhi : t ≤ 2 * t0) :
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2) ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) := by
  have ht : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) hlo
  have hbase : (0 : ℝ) ≤ 4 * Real.pi * t := le_of_lt (by positivity)
  have hbase_lo : (0 : ℝ) < 2 * Real.pi * t0 := by positivity
  have hle : 2 * Real.pi * t0 ≤ 4 * Real.pi * t := by
    have h := mul_le_mul_of_nonneg_left hlo (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
    rwa [show (4 : ℝ) * Real.pi * (t0 / 2) = 2 * Real.pi * t0 by ring] at h
  have he : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have hpow : ((2 * Real.pi * t0) ^ ((n : ℝ) / 2)) ≤ ((4 * Real.pi * t) ^ ((n : ℝ) / 2)) :=
    Real.rpow_le_rpow (le_of_lt hbase_lo) hle he
  have e1 : (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
      = (((4 * Real.pi * t) ^ ((n : ℝ) / 2)))⁻¹ := by
    rw [show (-(n : ℝ) / 2) = -((n : ℝ) / 2) by ring, Real.rpow_neg hbase]
  have e2 : (2 * Real.pi * t0) ^ (-(n : ℝ) / 2)
      = (((2 * Real.pi * t0) ^ ((n : ℝ) / 2)))⁻¹ := by
    rw [show (-(n : ℝ) / 2) = -((n : ℝ) / 2) by ring, Real.rpow_neg (le_of_lt hbase_lo)]
  rw [e1, e2]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos hbase_lo _)).mpr hpow

/-- The zpow time factor is bounded on the compact time interval. -/
private lemma zpow_bound (k : ℕ) (t0 t : ℝ) (ht0 : 0 < t0) (hlo : t0 / 2 ≤ t) :
    t ^ (-(k : ℤ)) ≤ (t0 / 2) ^ (-(k : ℤ)) := by
  have ht : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) hlo
  have ht0' : (0 : ℝ) < t0 / 2 := by positivity
  have hpow : (t0 / 2) ^ k ≤ t ^ k := pow_le_pow_left₀ (le_of_lt ht0') hlo k
  have e1 : t ^ (-(k : ℤ)) = ((t ^ k : ℝ))⁻¹ := by rw [zpow_neg, zpow_natCast]
  have e2 : (t0 / 2) ^ (-(k : ℤ)) = (((t0 / 2) ^ k : ℝ))⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [e1, e2]
  exact (inv_le_inv₀ (pow_pos ht k) (pow_pos ht0' k)).mpr hpow

/-- Gaussian comparison on the time interval. -/
private lemma gauss_le (n : ℕ) (t0 t : ℝ) (ht0 : 0 < t0)
    (hlo : t0 / 2 ≤ t) (hhi : t ≤ 2 * t0) (z : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-‖z‖ ^ 2 / (4 * t)) ≤ Real.exp (-‖z‖ ^ 2 / (8 * t0)) := by
  apply Real.exp_le_exp_of_le
  have ht : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) hlo
  have h4t : (0 : ℝ) < 4 * t := by positivity
  have h8t0 : (0 : ℝ) < 8 * t0 := by positivity
  have h4t8 : 4 * t ≤ 8 * t0 := by linarith
  rw [div_le_div_iff₀ h4t h8t0]
  exact mul_le_mul_of_nonpos_left h4t8 (neg_nonpos.mpr (sq_nonneg _))

/-- Domination of a Gaussian-polynomial kernel by a slower Gaussian
on a compact time interval away from `0`. -/
private theorem gaussPolyKernel_domination (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {t0 : ℝ} (ht0 : 0 < t0) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, t0 / 2 ≤ t → t ≤ 2 * t0 →
      ∀ z : EuclideanSpace ℝ (Fin n),
        |gaussPolyKernel n Q k t z| ≤ C * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := by
  obtain ⟨Cp, D, hCp, hpoly⟩ := mvpoly_eval_le n Q
  obtain ⟨Cg, hCg, hgauss⟩ := poly_le_exp_mul D t0 ht0
  have hC1pos : (0 : ℝ) < (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hC2pos : (0 : ℝ) < (t0 / 2) ^ (-(k : ℤ)) := zpow_pos (by positivity) _
  refine ⟨(2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Cp * ((t0 / 2) ^ (-(k : ℤ))) * Cg,
    mul_pos (mul_pos (mul_pos hC1pos hCp) hC2pos) hCg, fun {t} htlo hthi z => ?_⟩
  have ht : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) htlo
  have hA : |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)|
      ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact prefactor_bound n t0 t ht0 htlo hthi
  have hB : |Real.exp (-‖z‖ ^ 2 / (4 * t))| = Real.exp (-‖z‖ ^ 2 / (4 * t)) :=
    abs_of_pos (Real.exp_pos _)
  have hC : |MvPolynomial.eval (fun i => z i) Q| ≤ Cp * (1 + ‖z‖) ^ D := hpoly z
  have hD : |t ^ (-(k : ℤ))| ≤ (t0 / 2) ^ (-(k : ℤ)) := by
    rw [abs_of_pos (zpow_pos ht _)]
    exact zpow_bound k t0 t ht0 htlo
  have hker : |gaussPolyKernel n Q k t z|
      = |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * |Real.exp (-‖z‖ ^ 2 / (4 * t))|
        * |MvPolynomial.eval (fun i => z i) Q| * |t ^ (-(k : ℤ))| := by
    simp only [gaussPolyKernel, abs_mul]
  have hsplit : Real.exp (-‖z‖ ^ 2 / (8 * t0))
      = Real.exp (-‖z‖ ^ 2 / (16 * t0)) * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := by
    rw [← Real.exp_add]
    congr 1
    have h8ne : (8 : ℝ) * t0 ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt ht0)
    have h16ne : (16 : ℝ) * t0 ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt ht0)
    field_simp
    ring
  have hcancel : Real.exp (‖z‖ ^ 2 / (16 * t0)) * Real.exp (-‖z‖ ^ 2 / (16 * t0)) = 1 := by
    have harg : (‖z‖ ^ 2 / (16 * t0) : ℝ) + (-‖z‖ ^ 2 / (16 * t0)) = 0 := by
      rw [neg_div]
      exact add_neg_cancel _
    rw [← Real.exp_add, harg, Real.exp_zero]
  have h3 : (1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (16 * t0)) ≤ Cg := by
    have hscalar := hgauss ‖z‖ (norm_nonneg z)
    have h4 : (1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (16 * t0))
        ≤ (Cg * Real.exp (‖z‖ ^ 2 / (16 * t0))) * Real.exp (-‖z‖ ^ 2 / (16 * t0)) :=
      mul_le_mul_of_nonneg_right hscalar (le_of_lt (Real.exp_pos _))
    have heq : (Cg * Real.exp (‖z‖ ^ 2 / (16 * t0))) * Real.exp (-‖z‖ ^ 2 / (16 * t0))
        = Cg := by rw [mul_assoc, hcancel, mul_one]
    rw [heq] at h4
    exact h4
  have h2 : (1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (8 * t0))
      ≤ Cg * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := by
    rw [hsplit]
    calc (1 + ‖z‖) ^ D * (Real.exp (-‖z‖ ^ 2 / (16 * t0)) * Real.exp (-‖z‖ ^ 2 / (16 * t0)))
        = ((1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (16 * t0)))
          * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := by ring
      _ ≤ Cg * Real.exp (-‖z‖ ^ 2 / (16 * t0)) :=
          mul_le_mul_of_nonneg_right h3 (le_of_lt (Real.exp_pos _))
  have hgauss2 : (1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (4 * t))
      ≤ Cg * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := by
    have h1 : Real.exp (-‖z‖ ^ 2 / (4 * t)) ≤ Real.exp (-‖z‖ ^ 2 / (8 * t0)) :=
      gauss_le n t0 t ht0 htlo hthi z
    calc (1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (4 * t))
        ≤ (1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (8 * t0)) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (by positivity) D)
      _ ≤ Cg * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := h2
  have eA : (0 : ℝ) ≤ |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| := abs_nonneg _
  have eE : (0 : ℝ) ≤ Real.exp (-‖z‖ ^ 2 / (4 * t)) := le_of_lt (Real.exp_pos _)
  have eP : (0 : ℝ) ≤ |MvPolynomial.eval (fun i => z i) Q| := abs_nonneg _
  have eT : (0 : ℝ) ≤ |t ^ (-(k : ℤ))| := abs_nonneg _
  have bA : (0 : ℝ) ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) := le_of_lt hC1pos
  have bE : (0 : ℝ) ≤ Real.exp (-‖z‖ ^ 2 / (4 * t)) := le_of_lt (Real.exp_pos _)
  have bP : (0 : ℝ) ≤ Cp * (1 + ‖z‖) ^ D :=
    mul_nonneg (le_of_lt hCp) (pow_nonneg (by positivity) D)
  have s1 : |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * Real.exp (-‖z‖ ^ 2 / (4 * t))
      ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t)) :=
    mul_le_mul_of_nonneg' hA le_rfl eE bA
  have s2 : |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * |MvPolynomial.eval (fun i => z i) Q|
      ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * (Cp * (1 + ‖z‖) ^ D) :=
    mul_le_mul_of_nonneg' s1 hC eP (mul_nonneg bA bE)
  have s3 : |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * |MvPolynomial.eval (fun i => z i) Q| * |t ^ (-(k : ℤ))|
      ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * (Cp * (1 + ‖z‖) ^ D) * ((t0 / 2) ^ (-(k : ℤ))) :=
    mul_le_mul_of_nonneg' s2 hD eT (mul_nonneg (mul_nonneg bA bE) bP)
  rw [hker, hB]
  calc |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * |MvPolynomial.eval (fun i => z i) Q| * |t ^ (-(k : ℤ))|
      ≤ (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * (Cp * (1 + ‖z‖) ^ D) * ((t0 / 2) ^ (-(k : ℤ))) := s3
    _ = ((2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Cp * ((t0 / 2) ^ (-(k : ℤ))))
        * ((1 + ‖z‖) ^ D * Real.exp (-‖z‖ ^ 2 / (4 * t))) := by ring
    _ ≤ ((2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Cp * ((t0 / 2) ^ (-(k : ℤ))))
        * (Cg * Real.exp (-‖z‖ ^ 2 / (16 * t0))) :=
        mul_le_mul_of_nonneg_left hgauss2
          (mul_nonneg (mul_nonneg (le_of_lt hC1pos) (le_of_lt hCp)) (le_of_lt hC2pos))
    _ = (2 * Real.pi * t0) ^ (-(n : ℝ) / 2) * Cp * ((t0 / 2) ^ (-(k : ℤ))) * Cg
        * Real.exp (-‖z‖ ^ 2 / (16 * t0)) := by ring

end Domination

/-! ## E. Continuity, time and space partials -/

section ClassConvCont

open MeasureTheory


private lemma poly_eval_bound (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, ∃ D : ℕ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      |MvPolynomial.eval (fun i => x i) Q| ≤ C * (1 + ‖x‖) ^ D := by
  classical
  let D : ℕ := ∑ d ∈ Q.support, ∑ i ∈ d.support, d i
  let C : ℝ := ∑ d ∈ Q.support, |Q.coeff d|
  refine ⟨C, D, Finset.sum_nonneg (fun d _ => abs_nonneg _), fun x => ?_⟩
  rw [MvPolynomial.eval_eq]
  calc |∑ d ∈ Q.support, Q.coeff d * ∏ i ∈ d.support, (x i) ^ (d i)|
      ≤ ∑ d ∈ Q.support, |Q.coeff d * ∏ i ∈ d.support, (x i) ^ (d i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Q.support, |Q.coeff d| * ∏ i ∈ d.support, |x i| ^ (d i) := by
        congr 1
        ext d
        rw [abs_mul, Finset.abs_prod]
        congr 1
        exact Finset.prod_congr rfl (fun i _ => by rw [abs_pow])
    _ ≤ ∑ d ∈ Q.support, |Q.coeff d| * (1 + ‖x‖) ^ D := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc ∏ i ∈ d.support, |x i| ^ (d i)
            ≤ ∏ i ∈ d.support, (1 + ‖x‖) ^ (d i) := by
              apply Finset.prod_le_prod₀ _ _
              · intro i _
                exact pow_nonneg (abs_nonneg _) _
              · intro i _
                apply pow_le_pow_left₀ (abs_nonneg _) _ _
                have hxi : |x i| ≤ ‖x‖ := by
                  have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin n => ℝ) x i
                  simpa using h
                linarith [norm_nonneg x]
          _ = (1 + ‖x‖) ^ (∑ i ∈ d.support, d i) :=
              Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ (1 + ‖x‖) ^ D := by
              apply pow_le_pow_right₀ _ _
              · linarith [norm_nonneg x]
              · exact Finset.single_le_sum
                  (f := fun d' => ∑ i ∈ d'.support, d' i)
                  (fun d' _ => Nat.zero_le _) hd
    _ = C * (1 + ‖x‖) ^ D := by
        rw [Finset.sum_mul]

private lemma poly_gaussian_bounded (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (a : ℝ) (ha : 0 < a) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z : EuclideanSpace ℝ (Fin n),
      |MvPolynomial.eval (fun i => z i) Q * Real.exp (-a * ‖z‖ ^ 2)| ≤ Cg := by
  obtain ⟨C, D, hC, hbound⟩ := poly_eval_bound n Q
  refine ⟨C * Real.exp ((D : ℝ) ^ 2 / (4 * a)), mul_nonneg hC (Real.exp_nonneg _),
    fun z => ?_⟩
  have hexp_pos : 0 < Real.exp (-a * ‖z‖ ^ 2) := Real.exp_pos _
  rw [abs_mul, abs_of_pos hexp_pos]
  calc |MvPolynomial.eval (fun i => z i) Q| * Real.exp (-a * ‖z‖ ^ 2)
      ≤ (C * (1 + ‖z‖) ^ D) * Real.exp (-a * ‖z‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right (hbound z) (le_of_lt hexp_pos)
    _ = C * ((1 + ‖z‖) ^ D * Real.exp (-a * ‖z‖ ^ 2)) := by ring
    _ ≤ C * Real.exp ((D : ℝ) ^ 2 / (4 * a)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have h1 : (1 + ‖z‖) ^ D ≤ Real.exp ((D : ℝ) * ‖z‖) := by
          have hbase : (1 : ℝ) + ‖z‖ ≤ Real.exp ‖z‖ := by
            have h := Real.add_one_le_exp (‖z‖)
            linarith
          calc (1 + ‖z‖) ^ D ≤ (Real.exp ‖z‖) ^ D :=
                pow_le_pow_left₀ (by positivity) hbase D
            _ = Real.exp ((D : ℝ) * ‖z‖) := by
                rw [Real.exp_nat_mul]
        have h2 : Real.exp ((D : ℝ) * ‖z‖) * Real.exp (-a * ‖z‖ ^ 2)
            ≤ Real.exp ((D : ℝ) ^ 2 / (4 * a)) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          rw [le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg ((D : ℝ) - 2 * a * ‖z‖)]
        calc (1 + ‖z‖) ^ D * Real.exp (-a * ‖z‖ ^ 2)
            ≤ Real.exp ((D : ℝ) * ‖z‖) * Real.exp (-a * ‖z‖ ^ 2) := by
              apply mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
          _ ≤ Real.exp ((D : ℝ) ^ 2 / (4 * a)) := h2

private lemma kernel_continuousAt_q (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (q₀ : ℝ × EuclideanSpace ℝ (Fin n)) (hq₀ : 0 < q₀.1)
    (y : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      gaussPolyKernel n Q k q.1 (q.2 - y)) q₀ := by
  unfold gaussPolyKernel
  have ht_ne : q₀.1 ≠ 0 := ne_of_gt hq₀
  have h4pt_ne : 4 * Real.pi * q₀.1 ≠ 0 := by positivity
  have h1 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (4 * Real.pi * q.1) ^ (-(n : ℝ) / 2)) q₀ := by
    have hf : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => 4 * Real.pi * q.1) q₀ :=
      (continuousAt_const.mul continuousAt_const).mul continuousAt_fst
    exact hf.rpow_const (p := (-(n : ℝ) / 2)) (Or.inl h4pt_ne)
  have hsub : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => q.2 - y) q₀ :=
    continuousAt_snd.sub continuousAt_const
  have h2 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖q.2 - y‖ ^ 2 / (4 * q.1))) q₀ := by
    have hnorm : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => ‖q.2 - y‖) q₀ :=
      hsub.norm
    have hnum : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => -‖q.2 - y‖ ^ 2) q₀ :=
      (hnorm.pow 2).neg
    have hden : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => (4 * q.1 : ℝ)) q₀ :=
      continuousAt_const.mul continuousAt_fst
    have hden_ne : (4 : ℝ) * q₀.1 ≠ 0 := by positivity
    exact (hnum.div hden hden_ne).rexp
  have h3 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => (q.2 - y) i) Q) q₀ := by
    have hcoord : Continuous (fun x : EuclideanSpace ℝ (Fin n) => fun i => x i) :=
      continuous_pi_iff.mpr (fun i => PiLp.continuous_apply 2 _ i)
    have hpoly : Continuous (fun v : Fin n → ℝ => MvPolynomial.eval v Q) :=
      MvPolynomial.continuous_eval Q
    exact (hpoly.comp hcoord).continuousAt.comp hsub
  have h4 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      q.1 ^ (-(k : ℤ))) q₀ := by
    exact continuousAt_fst.zpow₀ _ (Or.inl ht_ne)
  exact ((h1.mul h2).mul h3).mul h4

private lemma kernel_continuous_y (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (ht : t ≠ 0) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      gaussPolyKernel n Q k t (x - y)) := by
  unfold gaussPolyKernel
  have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) :=
    continuous_const.sub continuous_id
  have h2 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x - y‖ ^ 2 / (4 * t))) := by
    have hnorm : Continuous (fun y : EuclideanSpace ℝ (Fin n) => ‖x - y‖) :=
      hsub.norm
    have hnum : Continuous (fun y : EuclideanSpace ℝ (Fin n) => -‖x - y‖ ^ 2) :=
      (hnorm.pow 2).neg
    have hden : Continuous (fun _ : EuclideanSpace ℝ (Fin n) => (4 * t : ℝ)) :=
      continuous_const
    have hden_ne : ∀ y : EuclideanSpace ℝ (Fin n), (4 : ℝ) * t ≠ 0 := fun _ => by positivity
    exact (hnum.div hden hden_ne).rexp
  have h3 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => (x - y) i) Q) := by
    have hcoord : Continuous (fun x : EuclideanSpace ℝ (Fin n) => fun i => x i) :=
      continuous_pi_iff.mpr (fun i => PiLp.continuous_apply 2 _ i)
    have hpoly : Continuous (fun v : Fin n → ℝ => MvPolynomial.eval v Q) :=
      MvPolynomial.continuous_eval Q
    exact (hpoly.comp hcoord).comp hsub
  exact ((continuous_const.mul h2).mul h3).mul continuous_const

private lemma exp_shift_bound (n : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (x₀ x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball x₀ 1) :
    Real.exp (-‖x - y‖ ^ 2 / (16 * t₀))
      ≤ Real.exp ((‖x₀‖ + 1) ^ 2 / (16 * t₀))
        * Real.exp (-‖y‖ ^ 2 / (32 * t₀)) := by
  have h16 : 0 < 16 * t₀ := by positivity
  have h32 : 0 < 32 * t₀ := by positivity
  have hdist : dist x x₀ < 1 := Metric.mem_ball.mp hx
  have hx_norm : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have htri : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      have h : x = x₀ + (x - x₀) := by abel
      conv_lhs => rw [h]
      exact norm_add_le _ _
    have hdist_eq : dist x x₀ = ‖x - x₀‖ := dist_eq_norm _ _
    linarith [hdist, hdist_eq, htri]
  have hnorm : ‖y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    have htri : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
      have h : y = x - (x - y) := by abel
      conv_lhs => rw [h]
      have h2 := norm_sub_le (x : EuclideanSpace ℝ (Fin n)) (x - y)
      linarith [h2]
    nlinarith [htri, norm_nonneg (x - y), norm_nonneg (x : EuclideanSpace ℝ (Fin n)),
      norm_nonneg (y : EuclideanSpace ℝ (Fin n)), sq_nonneg (‖x - y‖ - ‖x‖)]
  have hexp_ineq : -‖x - y‖ ^ 2 / (16 * t₀)
      ≤ -‖y‖ ^ 2 / (32 * t₀) + ‖x‖ ^ 2 / (16 * t₀) := by
    have e1 : -‖x - y‖ ^ 2 / (16 * t₀) = (-2 * ‖x - y‖ ^ 2) / (32 * t₀) := by ring
    have e2 : -‖y‖ ^ 2 / (32 * t₀) + ‖x‖ ^ 2 / (16 * t₀)
        = (-‖y‖ ^ 2 + 2 * ‖x‖ ^ 2) / (32 * t₀) := by ring
    rw [e1, e2, div_le_div_iff_of_pos_right h32]
    linarith [hnorm]
  have hCx : ‖x‖ ^ 2 / (16 * t₀) ≤ (‖x₀‖ + 1) ^ 2 / (16 * t₀) := by
    rw [div_le_div_iff_of_pos_right h16]
    apply pow_le_pow_left₀ (norm_nonneg _) hx_norm 2
  calc Real.exp (-‖x - y‖ ^ 2 / (16 * t₀))
      ≤ Real.exp (-‖y‖ ^ 2 / (32 * t₀) + ‖x‖ ^ 2 / (16 * t₀)) :=
        Real.exp_le_exp.mpr hexp_ineq
    _ = Real.exp (‖x‖ ^ 2 / (16 * t₀)) * Real.exp (-‖y‖ ^ 2 / (32 * t₀)) := by
        rw [add_comm, Real.exp_add]
    _ ≤ Real.exp ((‖x₀‖ + 1) ^ 2 / (16 * t₀)) * Real.exp (-‖y‖ ^ 2 / (32 * t₀)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact Real.exp_le_exp.mpr hCx

private lemma poly_exp_split_bound (n : ℕ) (Q : MvPolynomial (Fin n) ℝ)
    (t₀ t : ℝ) (ht₀ : 0 < t₀) (ht_lo : t₀ / 2 < t) (ht_hi : t < 2 * t₀)
    (Cg : ℝ) (hCg_nonneg : 0 ≤ Cg) (hCg : ∀ z : EuclideanSpace ℝ (Fin n),
      |MvPolynomial.eval (fun i => z i) Q * Real.exp (-(1 / (16 * t₀)) * ‖z‖ ^ 2)| ≤ Cg)
    (z : EuclideanSpace ℝ (Fin n)) :
    |MvPolynomial.eval (fun i => z i) Q| * Real.exp (-‖z‖ ^ 2 / (4 * t))
      ≤ Cg * Real.exp (-‖z‖ ^ 2 / (16 * t₀)) := by
  have hr : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have hexp2_nonneg : 0 ≤ Real.exp (-‖z‖ ^ 2 / (4 * t) + ‖z‖ ^ 2 / (16 * t₀)) :=
    Real.exp_nonneg _
  have hexp_split : Real.exp (-‖z‖ ^ 2 / (4 * t))
      = Real.exp (-‖z‖ ^ 2 / (16 * t₀))
        * Real.exp (-‖z‖ ^ 2 / (4 * t) + ‖z‖ ^ 2 / (16 * t₀)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hP1 : |MvPolynomial.eval (fun i => z i) Q| * Real.exp (-‖z‖ ^ 2 / (16 * t₀))
      ≤ Cg := by
    have h := hCg z
    rw [abs_mul, abs_of_pos (Real.exp_pos _)] at h
    have heq : (-(1 / (16 * t₀)) : ℝ) * ‖z‖ ^ 2 = -‖z‖ ^ 2 / (16 * t₀) := by ring
    rw [heq] at h
    exact h
  have hP2 : Real.exp (-‖z‖ ^ 2 / (4 * t) + ‖z‖ ^ 2 / (16 * t₀))
      ≤ Real.exp (-‖z‖ ^ 2 / (16 * t₀)) := by
    apply Real.exp_le_exp.mpr
    have ht_pos : 0 < t := by linarith
    have h4t_pos : 0 < 4 * t := by positivity
    have hle : 4 * t ≤ 8 * t₀ := by linarith
    have hdiv : (1 : ℝ) / (8 * t₀) ≤ 1 / (4 * t) :=
      one_div_le_one_div_of_le h4t_pos hle
    have hr_div : ‖z‖ ^ 2 / (8 * t₀) ≤ ‖z‖ ^ 2 / (4 * t) := by
      rw [div_eq_mul_one_div _ (8 * t₀), div_eq_mul_one_div _ (4 * t)]
      exact mul_le_mul_of_nonneg_left hdiv hr
    have heq1 : ‖z‖ ^ 2 / (8 * t₀) = 2 * (‖z‖ ^ 2 / (16 * t₀)) := by ring
    rw [neg_div, neg_div]
    linarith [hr_div, heq1]
  calc |MvPolynomial.eval (fun i => z i) Q| * Real.exp (-‖z‖ ^ 2 / (4 * t))
      = (|MvPolynomial.eval (fun i => z i) Q| * Real.exp (-‖z‖ ^ 2 / (16 * t₀)))
        * Real.exp (-‖z‖ ^ 2 / (4 * t) + ‖z‖ ^ 2 / (16 * t₀)) := by
        rw [hexp_split]; ring
    _ ≤ Cg * Real.exp (-‖z‖ ^ 2 / (16 * t₀)) :=
        mul_le_mul hP1 hP2 hexp2_nonneg hCg_nonneg

private lemma rpow_bound_on_Icc (n : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ t ∈ Set.Icc (t₀ / 2) (2 * t₀),
      |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| ≤ C1 := by
  have hcont : ContinuousOn (fun t : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2))
      (Set.Icc (t₀ / 2) (2 * t₀)) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have ht_pos : 0 < t := by linarith [ht₀, ht.1]
    have hne : 4 * Real.pi * t ≠ 0 := by positivity
    have hf : ContinuousAt (fun t : ℝ => 4 * Real.pi * t) t :=
      (continuousAt_const.mul continuousAt_const).mul continuousAt_id
    exact (hf.rpow_const (p := (-(n : ℝ) / 2)) (Or.inl hne)).continuousWithinAt
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have ht₀_mem : t₀ ∈ Set.Icc (t₀ / 2) (2 * t₀) := by
    constructor <;> linarith [ht₀]
  have hC1_nonneg : 0 ≤ C1 := by
    have h := hC1 t₀ ht₀_mem
    have hnn : 0 ≤ ‖(4 * Real.pi * t₀) ^ (-(n : ℝ) / 2)‖ := norm_nonneg _
    linarith
  refine ⟨C1, hC1_nonneg, fun t ht => ?_⟩
  have h := hC1 t ht
  simpa using h

private lemma zpow_bound_on_Icc (k : ℕ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ t ∈ Set.Icc (t₀ / 2) (2 * t₀),
      |t ^ (-(k : ℤ))| ≤ C2 := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(k : ℤ)))
      (Set.Icc (t₀ / 2) (2 * t₀)) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have ht_ne : t ≠ 0 := by
      have ht_pos : 0 < t := by linarith [ht₀, ht.1]
      linarith
    exact (continuousAt_id.zpow₀ _ (Or.inl ht_ne)).continuousWithinAt
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have ht₀_mem : t₀ ∈ Set.Icc (t₀ / 2) (2 * t₀) := by
    constructor <;> linarith [ht₀]
  have hC2_nonneg : 0 ≤ C2 := by
    have h := hC2 t₀ ht₀_mem
    have hnn : (0 : ℝ) ≤ ‖t₀ ^ (-(k : ℤ))‖ := norm_nonneg _
    linarith
  refine ⟨C2, hC2_nonneg, fun t ht => ?_⟩
  have h := hC2 t ht
  simpa using h

/-- A class-member convolution is continuous on `t > 0`. -/
private theorem classConv_continuousOn (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) :
    ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro q₀ hq₀
  obtain ⟨t₀, x₀⟩ := q₀
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true] at hq₀
  have ht₀ : 0 < t₀ := hq₀
  obtain ⟨M, hM⟩ := hg_bdd
  obtain ⟨C1, hC1_nonneg, hC1⟩ := rpow_bound_on_Icc n t₀ ht₀
  obtain ⟨C2, hC2_nonneg, hC2⟩ := zpow_bound_on_Icc k t₀ ht₀
  have ha_pos : 0 < 1 / (16 * t₀) := by positivity
  obtain ⟨Cg, hCg_nonneg, hCg⟩ := poly_gaussian_bounded n Q (1 / (16 * t₀)) ha_pos
  have hb_pos : 0 < 1 / (32 * t₀) := by positivity
  set Cx : ℝ := Real.exp ((‖x₀‖ + 1) ^ 2 / (16 * t₀)) with hCx_def
  have hCx_nonneg : 0 ≤ Cx := Real.exp_nonneg _
  set Kconst : ℝ := |M| * (C1 * C2 * Cg * Cx) with hK_def
  have hK_nonneg : 0 ≤ Kconst := by
    apply mul_nonneg (abs_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1_nonneg hC2_nonneg) hCg_nonneg) hCx_nonneg
  have hU_mem : Set.Ioo (t₀ / 2) (2 * t₀) ×ˢ Metric.ball x₀ 1 ∈ nhds (t₀, x₀) := by
    rw [nhds_prod_eq]
    apply Filter.prod_mem_prod
    · exact Ioo_mem_nhds (by linarith) (by linarith)
    · exact Metric.ball_mem_nhds _ (by norm_num)
  have hmain : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y)) (t₀, x₀) := by
    refine continuousAt_of_dominated
      (bound := fun y => Kconst * Real.exp (-(1 / (32 * t₀)) * ‖y‖ ^ 2)) ?_ ?_ ?_ ?_
    · filter_upwards [hU_mem] with q hq
      obtain ⟨t, x⟩ := q
      simp only [Set.mem_prod, Set.mem_Ioo, Metric.mem_ball] at hq
      obtain ⟨⟨ht_lo, ht_hi⟩, _⟩ := hq
      have ht_ne : t ≠ 0 := by
        have hpos : 0 < t := by linarith [ht₀]
        linarith
      have hker : AEStronglyMeasurable
          (fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (x - y)) volume :=
        (kernel_continuous_y n Q k t x ht_ne).aestronglyMeasurable
      exact hg_meas.mul hker
    · filter_upwards [hU_mem] with q hq
      obtain ⟨t, x⟩ := q
      simp only [Set.mem_prod, Set.mem_Ioo, Metric.mem_ball] at hq
      obtain ⟨⟨ht_lo, ht_hi⟩, hx⟩ := hq
      have hx_mem : x ∈ Metric.ball x₀ 1 := hx
      have ht_mem_Icc : t ∈ Set.Icc (t₀ / 2) (2 * t₀) :=
        ⟨le_of_lt ht_lo, le_of_lt ht_hi⟩
      have hrpow_le := hC1 t ht_mem_Icc
      have hzpow_le := hC2 t ht_mem_Icc
      filter_upwards [hM] with y hy
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hg_le : |g y| ≤ |M| := le_trans hy (le_abs_self _)
      have hEy_eq : Real.exp (-‖y‖ ^ 2 / (32 * t₀))
          = Real.exp (-(1 / (32 * t₀)) * ‖y‖ ^ 2) := by
        congr 1
        ring
      have hshift := exp_shift_bound n t₀ ht₀ x₀ x y hx_mem
      rw [← hCx_def] at hshift
      have hsplit_y := poly_exp_split_bound n Q t₀ t ht₀ ht_lo ht_hi
        Cg hCg_nonneg hCg (x - y)
      have hPE_nonneg : 0 ≤ |MvPolynomial.eval (fun i => (x - y) i) Q|
          * Real.exp (-‖x - y‖ ^ 2 / (4 * t)) :=
        mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
      have hEy_nonneg : 0 ≤ Real.exp (-‖y‖ ^ 2 / (32 * t₀)) := Real.exp_nonneg _
      have hCxEy_nonneg : 0 ≤ Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀)) :=
        mul_nonneg hCx_nonneg hEy_nonneg
      have hCgCxEy_nonneg : 0 ≤ Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀))) :=
        mul_nonneg hCg_nonneg hCxEy_nonneg
      have hC1mid_nonneg : 0 ≤ C1 * (Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀)))) :=
        mul_nonneg hC1_nonneg hCgCxEy_nonneg
      have hmid : |MvPolynomial.eval (fun i => (x - y) i) Q|
            * Real.exp (-‖x - y‖ ^ 2 / (4 * t))
          ≤ Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀))) := by
        calc |MvPolynomial.eval (fun i => (x - y) i) Q|
                * Real.exp (-‖x - y‖ ^ 2 / (4 * t))
            ≤ Cg * Real.exp (-‖x - y‖ ^ 2 / (16 * t₀)) := hsplit_y
          _ ≤ Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀))) :=
              mul_le_mul_of_nonneg_left hshift hCg_nonneg
      have hK_eq : |gaussPolyKernel n Q k t (x - y)|
          = |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)|
            * (|MvPolynomial.eval (fun i => (x - y) i) Q|
              * Real.exp (-‖x - y‖ ^ 2 / (4 * t)))
            * |t ^ (-(k : ℤ))| := by
        unfold gaussPolyKernel
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        ring
      have hK_le : |gaussPolyKernel n Q k t (x - y)|
          ≤ (C1 * C2 * Cg * Cx) * Real.exp (-‖y‖ ^ 2 / (32 * t₀)) := by
        have hab : |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)|
              * (|MvPolynomial.eval (fun i => (x - y) i) Q|
                * Real.exp (-‖x - y‖ ^ 2 / (4 * t)))
            ≤ C1 * (Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀)))) :=
          mul_le_mul hrpow_le hmid hPE_nonneg hC1_nonneg
        have habc : |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)|
              * (|MvPolynomial.eval (fun i => (x - y) i) Q|
                * Real.exp (-‖x - y‖ ^ 2 / (4 * t)))
              * |t ^ (-(k : ℤ))|
            ≤ C1 * (Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀)))) * C2 :=
          mul_le_mul hab hzpow_le (abs_nonneg _) hC1mid_nonneg
        rw [hK_eq]
        calc |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)|
                * (|MvPolynomial.eval (fun i => (x - y) i) Q|
                  * Real.exp (-‖x - y‖ ^ 2 / (4 * t)))
                * |t ^ (-(k : ℤ))|
            ≤ C1 * (Cg * (Cx * Real.exp (-‖y‖ ^ 2 / (32 * t₀)))) * C2 := habc
          _ = (C1 * C2 * Cg * Cx) * Real.exp (-‖y‖ ^ 2 / (32 * t₀)) := by ring
      calc |g y| * |gaussPolyKernel n Q k t (x - y)|
          ≤ |M| * ((C1 * C2 * Cg * Cx) * Real.exp (-‖y‖ ^ 2 / (32 * t₀))) :=
            mul_le_mul hg_le hK_le (abs_nonneg _) (abs_nonneg _)
        _ = Kconst * Real.exp (-(1 / (32 * t₀)) * ‖y‖ ^ 2) := by
            rw [hK_def, hEy_eq]
            ring
    · have hgauss := integrable_real_exp_neg_mul_sq_norm (Fin n) hb_pos
      exact hgauss.const_mul Kconst
    · refine Filter.Eventually.of_forall fun y => ?_
      have hker := kernel_continuousAt_q n Q k (t₀, x₀) ht₀ y
      exact continuousAt_const.mul hker
  exact hmain.continuousWithinAt

end ClassConvCont

section G4cTime

open MeasureTheory


private lemma continuous_euclidean_coord (n : ℕ) (i : Fin n) :
    Continuous fun v : EuclideanSpace ℝ (Fin n) => v i := by
  have h : ∀ v : EuclideanSpace ℝ (Fin n),
      v i = inner ℝ (EuclideanSpace.single i (1 : ℝ)) v := by
    intro v
    rw [EuclideanSpace.inner_single_left]
    simp
  simp_rw [h]
  exact Continuous.inner continuous_const continuous_id

private lemma continuous_kernel_poly (n : ℕ) (Q : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => (x - y) i) Q := by
  have h1 : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      ((fun i => (x - y) i) : Fin n → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    exact (continuous_euclidean_coord n i).comp (continuous_const.sub continuous_id)
  exact (MvPolynomial.continuous_eval Q).comp h1

private lemma continuous_kernel_space (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (s : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      gaussPolyKernel n Q k s (x - y) := by
  have hsub : Continuous fun y : EuclideanSpace ℝ (Fin n) => x - y :=
    continuous_const.sub continuous_id
  have hinner : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      -‖x - y‖ ^ 2 / (4 * s) := by
    rw [show (fun y : EuclideanSpace ℝ (Fin n) => -‖x - y‖ ^ 2 / (4 * s))
      = fun y => -‖x - y‖ ^ 2 * (4 * s)⁻¹ from
      funext fun y => div_eq_mul_inv _ _]
    exact ((hsub.norm.pow 2).neg.mul continuous_const)
  have hexp : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x - y‖ ^ 2 / (4 * s)) :=
    Real.continuous_exp.comp hinner
  have hpoly := continuous_kernel_poly n Q x
  change Continuous fun y : EuclideanSpace ℝ (Fin n) =>
    (4 * Real.pi * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / (4 * s))
      * MvPolynomial.eval (fun i => (x - y) i) Q * s ^ (-(k : ℤ))
  exact ((continuous_const.mul hexp).mul hpoly).mul continuous_const

private lemma differentiableAt_kernel_time (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {s : ℝ} (hs : 0 < s) (z : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun s' => gaussPolyKernel n Q k s' z) s := by
  have h4ps : (0 : ℝ) < 4 * Real.pi * s := by positivity
  have hA : DifferentiableAt ℝ (fun s' : ℝ => (4 * Real.pi * s') ^ (-(n : ℝ) / 2)) s := by
    have h1 : HasDerivAt (fun s' : ℝ => 4 * Real.pi * s') (4 * Real.pi) s := by
      have h := HasDerivAt.const_mul (4 * Real.pi) (hasDerivAt_id s)
      simpa using h
    exact (h1.rpow_const (Or.inl (ne_of_gt h4ps))).differentiableAt
  have hB : DifferentiableAt ℝ (fun s' : ℝ => Real.exp (-‖z‖ ^ 2 / (4 * s'))) s := by
    have hden : (4 : ℝ) * s ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 4 * s)
    have hinner : HasDerivAt (fun s' : ℝ => -‖z‖ ^ 2 / (4 * s')) _ s :=
      HasDerivAt.div (hasDerivAt_const s _) (HasDerivAt.const_mul 4 (hasDerivAt_id s)) hden
    exact (HasDerivAt.comp s (Real.hasDerivAt_exp _) hinner).differentiableAt
  have hC : DifferentiableAt ℝ (fun _ : ℝ => MvPolynomial.eval (fun i => z i) Q) s :=
    differentiableAt_const _
  have hD : DifferentiableAt ℝ (fun s' : ℝ => s' ^ (-(k : ℤ))) s :=
    (hasDerivAt_zpow _ _ (Or.inl (ne_of_gt hs))).differentiableAt
  change DifferentiableAt ℝ (fun s' : ℝ => (4 * Real.pi * s') ^ (-(n : ℝ) / 2)
    * Real.exp (-‖z‖ ^ 2 / (4 * s')) * MvPolynomial.eval (fun i => z i) Q
    * s' ^ (-(k : ℤ))) s
  exact ((hA.mul hB).mul hC).mul hD

/-- Time partial of a Gaussian-polynomial-kernel convolution, by
differentiation under the integral. -/
private theorem classConv_hasDerivAt_time (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (hTimeClosThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      deriv (fun s => gaussPolyKernel n Q k s x) t
        = gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t x
          + gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2) t x)
    (hDomThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t0 : ℝ}, 0 < t0 →
      ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, t0 / 2 ≤ t → t ≤ 2 * t0 →
        ∀ z : EuclideanSpace ℝ (Fin n),
          |gaussPolyKernel n Q k t z| ≤ C * Real.exp (-‖z‖ ^ 2 / (16 * t0))) :
    HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k s (x - y))
      (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k s (x - y)) t) t := by
  obtain ⟨M, hM⟩ := hg_bdd
  set Q1 : MvPolynomial (Fin n) ℝ := -(((n : ℝ) / 2 + (k : ℝ)) • Q)
  set Q2 : MvPolynomial (Fin n) ℝ := ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
  obtain ⟨C1, hC1pos, hC1⟩ := hDomThm n Q1 (k + 1) ht
  obtain ⟨C2, hC2pos, hC2⟩ := hDomThm n Q2 (k + 2) ht
  obtain ⟨C0, hC0pos, hC0⟩ := hDomThm n Q k ht
  have hKderiv : ∀ {s' : ℝ}, 0 < s' → ∀ z : EuclideanSpace ℝ (Fin n),
      HasDerivAt (fun s'' => gaussPolyKernel n Q k s'' z)
        (gaussPolyKernel n Q1 (k + 1) s' z
          + gaussPolyKernel n Q2 (k + 2) s' z) s' := by
    intro s' hs' z
    have hd := (differentiableAt_kernel_time n Q k hs' z).hasDerivAt
    rw [hTimeClosThm n Q k hs' z] at hd
    exact hd
  have hF_meas_all : ∀ s' : ℝ, AEStronglyMeasurable
      (fun y => g y * gaussPolyKernel n Q k s' (x - y)) volume :=
    fun s' => hg_meas.mul (continuous_kernel_space n Q k s' x).aestronglyMeasurable
  have hG : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x - y‖ ^ 2 / (16 * t))) volume :=
    aux_gaussReal_int n x (16 * t) (by positivity)
  have hF_int : Integrable (fun y => g y * gaussPolyKernel n Q k t (x - y)) volume := by
    have hmaj : Integrable (fun y => |M| * C0 * Real.exp (-‖x - y‖ ^ 2 / (16 * t))) volume :=
      hG.const_mul _
    refine hmaj.mono' (hF_meas_all t) ?_
    filter_upwards [hM] with y hy
    have hK := hC0 (show t / 2 ≤ t by linarith) (show t ≤ 2 * t by linarith) (x - y)
    change ‖g y * gaussPolyKernel n Q k t (x - y)‖ ≤ |M| * C0 * Real.exp (-‖x - y‖ ^ 2 / (16 * t))
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |gaussPolyKernel n Q k t (x - y)|
          ≤ |M| * |gaussPolyKernel n Q k t (x - y)| :=
            mul_le_mul_of_nonneg_right (hy.trans (le_abs_self M)) (abs_nonneg _)
      _ ≤ |M| * (C0 * Real.exp (-‖x - y‖ ^ 2 / (16 * t))) :=
            mul_le_mul_of_nonneg_left hK (abs_nonneg _)
      _ = |M| * C0 * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := by ring
  have hF'_meas : AEStronglyMeasurable
      (fun y => g y * (gaussPolyKernel n Q1 (k + 1) t (x - y)
        + gaussPolyKernel n Q2 (k + 2) t (x - y))) volume :=
    hg_meas.mul ((continuous_kernel_space n Q1 (k + 1) t x).aestronglyMeasurable.add
      (continuous_kernel_space n Q2 (k + 2) t x).aestronglyMeasurable)
  have bound_integrable : Integrable
      (fun y => |M| * (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t))) volume :=
    hG.const_mul _
  have h_bound : ∀ᵐ y : EuclideanSpace ℝ (Fin n), ∀ s' ∈ Set.Ioo (t / 2) (2 * t),
      ‖g y * (gaussPolyKernel n Q1 (k + 1) s' (x - y)
        + gaussPolyKernel n Q2 (k + 2) s' (x - y))‖
        ≤ |M| * (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := by
    filter_upwards [hM] with y hy s' hs'
    obtain ⟨hs'lo, hs'hi⟩ := Set.mem_Ioo.mp hs'
    have h1 := hC1 (le_of_lt hs'lo) (le_of_lt hs'hi) (x - y)
    have h2 := hC2 (le_of_lt hs'lo) (le_of_lt hs'hi) (x - y)
    have hsum : |gaussPolyKernel n Q1 (k + 1) s' (x - y)
          + gaussPolyKernel n Q2 (k + 2) s' (x - y)|
        ≤ (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := by
      calc |gaussPolyKernel n Q1 (k + 1) s' (x - y)
              + gaussPolyKernel n Q2 (k + 2) s' (x - y)|
            ≤ |gaussPolyKernel n Q1 (k + 1) s' (x - y)|
              + |gaussPolyKernel n Q2 (k + 2) s' (x - y)| := abs_add_le _ _
        _ ≤ C1 * Real.exp (-‖x - y‖ ^ 2 / (16 * t))
              + C2 * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := add_le_add h1 h2
        _ = (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := by ring
    change ‖g y * (gaussPolyKernel n Q1 (k + 1) s' (x - y)
        + gaussPolyKernel n Q2 (k + 2) s' (x - y))‖
        ≤ |M| * (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t))
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |gaussPolyKernel n Q1 (k + 1) s' (x - y)
            + gaussPolyKernel n Q2 (k + 2) s' (x - y)|
        ≤ |M| * |gaussPolyKernel n Q1 (k + 1) s' (x - y)
            + gaussPolyKernel n Q2 (k + 2) s' (x - y)| :=
          mul_le_mul_of_nonneg_right (hy.trans (le_abs_self M)) (abs_nonneg _)
      _ ≤ |M| * ((C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t))) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |M| * (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := by ring
  have h_diff : ∀ᵐ y : EuclideanSpace ℝ (Fin n), ∀ s' ∈ Set.Ioo (t / 2) (2 * t),
      HasDerivAt (fun s'' => g y * gaussPolyKernel n Q k s'' (x - y))
        (g y * (gaussPolyKernel n Q1 (k + 1) s' (x - y)
          + gaussPolyKernel n Q2 (k + 2) s' (x - y))) s' := by
    filter_upwards with y s' hs'
    obtain ⟨hs'lo, hs'hi⟩ := Set.mem_Ioo.mp hs'
    have hs'pos : 0 < s' := by linarith
    exact (hKderiv hs'pos (x - y)).const_mul (g y)
  have hs : Set.Ioo (t / 2) (2 * t) ∈ nhds t := Ioo_mem_nhds (by linarith) (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s' y => g y * gaussPolyKernel n Q k s' (x - y))
    (F' := fun s' y => g y * (gaussPolyKernel n Q1 (k + 1) s' (x - y)
      + gaussPolyKernel n Q2 (k + 2) s' (x - y)))
    (bound := fun y => |M| * (C1 + C2) * Real.exp (-‖x - y‖ ^ 2 / (16 * t)))
    (s := Set.Ioo (t / 2) (2 * t)) (μ := volume) (x₀ := t)
    hs (Filter.Eventually.of_forall hF_meas_all) hF_int hF'_meas h_bound
    bound_integrable h_diff
  have hval : ∀ y : EuclideanSpace ℝ (Fin n),
      deriv (fun s => gaussPolyKernel n Q k s (x - y)) t
        = gaussPolyKernel n Q1 (k + 1) t (x - y)
          + gaussPolyKernel n Q2 (k + 2) t (x - y) :=
    fun y => hTimeClosThm n Q k ht (x - y)
  simp only [hval]
  exact key.2

end G4cTime

section FirstPartialAsm

open MeasureTheory
open scoped Topology


private theorem aux_polyEval_diff (n : ℕ) (Q : MvPolynomial (Fin n) ℝ)
    (z0 : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q) z0
      := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have h : (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) (MvPolynomial.C
      a))
        = fun _ => a := by
      apply funext
      intro z
      simp
    rw [h]
    exact differentiableAt_const a
  | add p q hp hq =>
    have h : (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) (p + q))
        = fun z => MvPolynomial.eval (fun i => z i) p + MvPolynomial.eval (fun i => z i) q := by
      apply funext
      intro z
      simp [MvPolynomial.eval_add]
    rw [h]
    exact hp.add hq
  | mul_X p k hp =>
    have h : (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) (p *
      MvPolynomial.X k))
        = fun z => MvPolynomial.eval (fun i => z i) p * z k := by
      apply funext
      intro z
      simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [h]
    have hproj : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => z k) z0 := by
      have hh : (fun z : EuclideanSpace ℝ (Fin n) => z k)
          = ⇑(PiLp.proj 2 (fun _ : Fin n => ℝ) k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := rfl
      rw [hh]
      exact ContinuousLinearMap.differentiableAt _
    exact hp.mul hproj

private theorem aux_kernel_diff (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ) (t : ℝ)
    (z0 : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z) z0 := by
  have hnorm : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) z0 :=
    (differentiableAt_id).norm_sq ℝ
  have hneg : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => -‖z‖ ^ 2) z0 := hnorm.neg
  have hdiv : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => -‖z‖ ^ 2 / (4 * t)) z0 := by
    have heq : (fun z : EuclideanSpace ℝ (Fin n) => -‖z‖ ^ 2 / (4 * t))
        = fun z => (-‖z‖ ^ 2) * ((4 * t)⁻¹) := by
      apply funext
      intro z
      rw [div_eq_mul_inv]
    rw [heq]
    exact hneg.mul_const _
  have hexp : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2 / (4 *
    t))) z0 := by
    have hexp0 : DifferentiableAt ℝ Real.exp (-‖z0‖ ^ 2 / (4 * t)) := Real.differentiableAt_exp
    have hcomp := hexp0.comp z0 hdiv
    simpa [Function.comp_def] using hcomp
  have hpoly : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i =>
    z i) Q) z0 :=
    aux_polyEval_diff n Q z0
  have hconst1 : DifferentiableAt ℝ (fun _ : EuclideanSpace ℝ (Fin n) => (4 * Real.pi * t) ^ (-(n :
    ℝ) / 2)) z0 :=
    differentiableAt_const _
  have hconst2 : DifferentiableAt ℝ (fun _ : EuclideanSpace ℝ (Fin n) => t ^ (-(k : ℤ))) z0 :=
    differentiableAt_const _
  have h_eq : (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z)
      = fun z => ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * MvPolynomial.eval (fun i => z i) Q * t ^ (-(k : ℤ))) := by
    apply funext
    intro z
    rfl
  rw [h_eq]
  exact ((hconst1.mul hexp).mul hpoly).mul hconst2

private theorem aux_kernel_cont (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ) (t : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z) := by
  have h_eq : (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z)
      = fun z => ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * MvPolynomial.eval (fun i => z i) Q * t ^ (-(k : ℤ))) := by
    apply funext
    intro z
    rfl
  rw [h_eq]
  have hnorm : Continuous (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) :=
    continuous_norm.pow 2
  have hexp_arg : Continuous (fun z : EuclideanSpace ℝ (Fin n) => -‖z‖ ^ 2 / (4 * t)) := by
    apply Continuous.div_const
    exact hnorm.neg
  have hexp : Continuous (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2 / (4 * t))) :=
    Real.continuous_exp.comp hexp_arg
  have hpoly : Continuous (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q)
    := by
    have h1 : Continuous (fun f : Fin n → ℝ => MvPolynomial.eval f Q) :=
      MvPolynomial.continuous_eval Q
    have h2 : Continuous (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) :=
      PiLp.continuous_ofLp 2 _
    exact h1.comp h2
  have hconst1 : Continuous (fun _ : EuclideanSpace ℝ (Fin n) => (4 * Real.pi * t) ^ (-(n : ℝ) /
    2)) :=
    continuous_const
  have hconst2 : Continuous (fun _ : EuclideanSpace ℝ (Fin n) => t ^ (-(k : ℤ))) :=
    continuous_const
  exact ((hconst1.mul hexp).mul hpoly).mul hconst2

private theorem aux_update_hasDeriv (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s0 : ℝ) :
    HasDerivAt (fun s : ℝ => (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)))
      (EuclideanSpace.single i (1 : ℝ)) s0 := by
  have h_eq : (fun s : ℝ => (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)))
      = fun s : ℝ => x + (s - x i) • EuclideanSpace.single i (1 : ℝ) := by
    apply funext
    intro s
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Function.update_self]
    · simp [hj]
  rw [h_eq]
  have h1 : HasDerivAt (fun s : ℝ => s - x i) (1 : ℝ) s0 :=
    (hasDerivAt_id s0).sub_const (x i)
  have h2 : HasDerivAt (fun s : ℝ => (s - x i) • EuclideanSpace.single i (1 : ℝ))
      ((1 : ℝ) • EuclideanSpace.single i (1 : ℝ)) s0 :=
    h1.smul_const _
  simpa using h2.const_add x

private theorem aux_kernelUpdate_diff (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ) (t : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s0 : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => gaussPolyKernel n Q k t
      (WithLp.toLp 2 (Function.update w i s))) s0 := by
  have hw : DifferentiableAt ℝ
      (fun s : ℝ => (WithLp.toLp 2 (Function.update w i s) : EuclideanSpace ℝ (Fin n))) s0 :=
    (aux_update_hasDeriv n w i s0).differentiableAt
  have hk : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z)
      ((WithLp.toLp 2 (Function.update w i s0) : EuclideanSpace ℝ (Fin n))) :=
    aux_kernel_diff n Q k t _
  have hcomp := hk.comp s0 hw
  simpa [Function.comp_def] using hcomp

private theorem aux_updateDiff_norm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s : ℝ) :
    ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - x‖ = |s - x i| := by
  have h_eq : (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - x
      = (s - x i) • EuclideanSpace.single i (1 : ℝ) := by
    have h1 : (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))
        = x + (s - x i) • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [Function.update_self]
      · simp [hj]
    rw [h1]
    abel
  rw [h_eq, norm_smul, Real.norm_eq_abs, PiLp.norm_single]
  simp

private theorem aux_sq_bound (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s : ℝ)
    (hs : s ∈ Set.Ioo ((x i) - 1) ((x i) + 1)) :
    ‖x - y‖ ^ 2 ≤ 2 * ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖ ^ 2
      + 2 := by
  have hwd : ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y) - (x - y)
      = (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - x := by
    abel
  have hle : ‖((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y) - (x - y)‖ ≤
    1 := by
    rw [hwd, aux_updateDiff_norm]
    have h1 : |s - x i| < 1 := by
      have hlo : (x i) - 1 < s := hs.1
      have hhi : s < (x i) + 1 := hs.2
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    exact h1.le
  have htri : ‖x - y‖ ≤ ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖ +
    1 := by
    have h : (x - y) = ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
        - (((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y) - (x - y)) := by
      abel
    calc ‖x - y‖
        = ‖((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
          - (((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y) - (x - y))‖
            := by
          rw [← h]
      _ ≤ ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖
          + ‖((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y) - (x - y)‖ :=
          norm_sub_le _ _
      _ ≤ ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖ + 1 := by
          gcongr
  have hsq : ‖x - y‖ ^ 2
      ≤ (‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖ + 1) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have h2 : (‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖ + 1) ^ 2
      ≤ 2 * ‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖ ^ 2 + 2 := by
    nlinarith [sq_nonneg (‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖
      - 1)]
  exact hsq.trans h2

private theorem aux_exp_bound (w2 d2 t : ℝ) (ht : 0 < t) (h : d2 ≤ 2 * w2 + 2) :
    Real.exp (-w2 / (16 * t)) ≤ Real.exp (1 / (16 * t)) * Real.exp (-d2 / (32 * t)) := by
  have ht16 : 0 < (16 * t : ℝ) := by positivity
  have h1 : -w2 / (16 * t) ≤ -d2 / (32 * t) + 1 / (16 * t) := by
    have hw2 : d2 / 2 - 1 ≤ w2 := by linarith
    have hneg : -w2 / (16 * t) ≤ -(d2 / 2 - 1) / (16 * t) := by
      have hle : -w2 ≤ -(d2 / 2 - 1) := by linarith
      have hdiv := div_le_div_of_nonneg_right hle ht16.le
      simpa [neg_div] using hdiv
    calc -w2 / (16 * t) ≤ -(d2 / 2 - 1) / (16 * t) := hneg
      _ = -d2 / (32 * t) + 1 / (16 * t) := by
        field_simp
        ring
  calc Real.exp (-w2 / (16 * t))
      ≤ Real.exp (-d2 / (32 * t) + 1 / (16 * t)) := Real.exp_le_exp.mpr h1
    _ = Real.exp (-d2 / (32 * t)) * Real.exp (1 / (16 * t)) := Real.exp_add _ _
    _ = Real.exp (1 / (16 * t)) * Real.exp (-d2 / (32 * t)) := mul_comm _ _

set_option linter.unusedVariables false in
/-- First space partial of a class-member convolution, assembled from
kernel space closure and kernel domination. -/
private theorem classConv_hasDerivAt_space_asm (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hSpaceClosThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s))) (x i)
        = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t x
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t x)
    (hDomThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t0 : ℝ}, 0 < t0 →
      ∃ C : ℝ, 0 < C ∧ ∀ {t : ℝ}, t0 / 2 ≤ t → t ≤ 2 * t0 →
        ∀ z : EuclideanSpace ℝ (Fin n),
          |gaussPolyKernel n Q k t z| ≤ C * Real.exp (-‖z‖ ^ 2 / (16 * t0))) :
    HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update x i s) - y))
      (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)) (x i) := by
  obtain ⟨M, hM⟩ := hg_bdd
  set M0 : ℝ := max M 0
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hg_bdd0 : ∀ᵐ y ∂volume, |g y| ≤ M0 := hM.mono fun y hy => hy.trans (le_max_left _ _)
  obtain ⟨C, _, hC⟩ := hDomThm n Q k ht
  obtain ⟨C1, hC1pos, hC1⟩ := hDomThm n (MvPolynomial.pderiv i Q) k ht
  obtain ⟨C2, hC2pos, hC2⟩ := hDomThm n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) ht
  have ht_lo : t / 2 ≤ t := by linarith
  have ht_hi : t ≤ 2 * t := by linarith
  have h16t : 0 < (16 * t : ℝ) := by positivity
  have h32t : 0 < (32 * t : ℝ) := by positivity
  have hGauss16 : Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x - y‖ ^ 2 / (16 *
    t))) :=
    aux_gaussReal_int n x (16 * t) h16t
  have hGauss32 : Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x - y‖ ^ 2 / (32 *
    t))) :=
    aux_gaussReal_int n x (32 * t) h32t
  have hs : Set.Ioo ((x i) - 1) ((x i) + 1) ∈ 𝓝 (x i) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have h_upd_self : (WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) = x := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have hF_meas : Filter.Eventually (fun s : ℝ => AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)) volume) (𝓝 (x i))
          := by
    apply Filter.Eventually.of_forall
    intro s
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y) :=
      continuous_const.sub continuous_id
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussPolyKernel n Q k t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)) :=
      (aux_kernel_cont n Q k t).comp h1
    exact hg_meas.mul hcont.aestronglyMeasurable
  have hF0_eq : (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t
        ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y))
      = fun y => g y * gaussPolyKernel n Q k t (x - y) := by
    apply funext
    intro y
    rw [h_upd_self]
  have hF0_meas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t (x - y)) volume := by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) :=
      continuous_const.sub continuous_id
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussPolyKernel n Q k t (x - y)) :=
      (aux_kernel_cont n Q k t).comp h1
    exact hg_meas.mul hcont.aestronglyMeasurable
  have hBound0_int : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => (M0 * C) * Real.exp (-‖x - y‖ ^ 2 / (16 * t))) volume :=
    hGauss16.const_mul (M0 * C)
  have hF_int : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t
        ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)) volume := by
    rw [hF0_eq]
    apply Integrable.mono' hBound0_int hF0_meas
    filter_upwards [hg_bdd0] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hK : |gaussPolyKernel n Q k t (x - y)| ≤ C * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) :=
      hC ht_lo ht_hi (x - y)
    have hle : |g y| * |gaussPolyKernel n Q k t (x - y)|
        ≤ M0 * (C * Real.exp (-‖x - y‖ ^ 2 / (16 * t))) :=
      mul_le_mul hy hK (abs_nonneg _) hM0_nonneg
    have hring : M0 * (C * Real.exp (-‖x - y‖ ^ 2 / (16 * t)))
        = (M0 * C) * Real.exp (-‖x - y‖ ^ 2 / (16 * t)) := by ring
    rw [← hring]
    exact hle
  have hF'_meas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => g y * (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y))) volume :=
            by
    have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y) :=
      continuous_const.sub continuous_id
    have hc1 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)) :=
      (aux_kernel_cont n (MvPolynomial.pderiv i Q) k t).comp h1
    have hc2 : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)) :=
      (aux_kernel_cont n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t).comp h1
    have hsum : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)) :=
      hc1.add hc2
    exact hg_meas.mul hsum.aestronglyMeasurable
  have hC12_nonneg : 0 ≤ C1 + C2 := add_nonneg (le_of_lt hC1pos) (le_of_lt hC2pos)
  have hBound_int : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (M0 * ((C1 + C2) * Real.exp (1 / (16 * t)))) * Real.exp (-‖x - y‖ ^ 2 / (32 * t))) volume :=
    hGauss32.const_mul (M0 * ((C1 + C2) * Real.exp (1 / (16 * t))))
  have h_bound : ∀ᵐ y ∂volume, ∀ s ∈ Set.Ioo ((x i) - 1) ((x i) + 1),
      ‖g y * (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y))‖
      ≤ (M0 * ((C1 + C2) * Real.exp (1 / (16 * t)))) * Real.exp (-‖x - y‖ ^ 2 / (32 * t)) := by
    filter_upwards [hg_bdd0] with y hy
    intro s hs
    have hK1 : |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
        ≤ C1 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖
          ^ 2 / (16 * t)) :=
      hC1 ht_lo ht_hi _
    have hK2 : |gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
        ≤ C2 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y‖
          ^ 2 / (16 * t)) :=
      hC2 ht_lo ht_hi _
    have hsum : |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
        ≤ (C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin
          n)) - y‖ ^ 2 / (16 * t)) := by
      have h1 : |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
          ≤ |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
            + |gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
              ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)| :=
        abs_add_le _ _
      have h2 : |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
          + |gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
          ≤ C1 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) -
            y‖ ^ 2 / (16 * t))
            + C2 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) -
              y‖ ^ 2 / (16 * t)) :=
        add_le_add hK1 hK2
      have h3 : C1 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))
        - y‖ ^ 2 / (16 * t))
          + C2 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) -
            y‖ ^ 2 / (16 * t))
          = (C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin
            n)) - y‖ ^ 2 / (16 * t)) := by
        ring
      calc |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
            + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
              ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
          ≤ |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
              ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
              + |gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
                ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)| := h1
        _ ≤ C1 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) -
          y‖ ^ 2 / (16 * t))
              + C2 * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n))
                - y‖ ^ 2 / (16 * t)) := h2
        _ = (C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin
          n)) - y‖ ^ 2 / (16 * t)) := h3
    have hmul : |g y| * |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
        ≤ M0 * ((C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ
          (Fin n)) - y‖ ^ 2 / (16 * t))) :=
      mul_le_mul hy hsum (abs_nonneg _) hM0_nonneg
    have hexp_le : Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) -
      y‖ ^ 2 / (16 * t))
        ≤ Real.exp (1 / (16 * t)) * Real.exp (-‖x - y‖ ^ 2 / (32 * t)) :=
      aux_exp_bound _ _ t ht (aux_sq_bound n x y i s hs)
    have hle1 : (C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ
      (Fin n)) - y‖ ^ 2 / (16 * t))
        ≤ (C1 + C2) * (Real.exp (1 / (16 * t)) * Real.exp (-‖x - y‖ ^ 2 / (32 * t))) :=
      mul_le_mul_of_nonneg_left hexp_le hC12_nonneg
    have hle2 : M0 * ((C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) :
      EuclideanSpace ℝ (Fin n)) - y‖ ^ 2 / (16 * t)))
        ≤ M0 * ((C1 + C2) * (Real.exp (1 / (16 * t)) * Real.exp (-‖x - y‖ ^ 2 / (32 * t)))) :=
      mul_le_mul_of_nonneg_left hle1 hM0_nonneg
    have hring : M0 * ((C1 + C2) * (Real.exp (1 / (16 * t)) * Real.exp (-‖x - y‖ ^ 2 / (32 * t))))
        = (M0 * ((C1 + C2) * Real.exp (1 / (16 * t)))) * Real.exp (-‖x - y‖ ^ 2 / (32 * t)) := by
      ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |g y| * |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
            + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
              ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)|
          ≤ M0 * ((C1 + C2) * Real.exp (-‖(WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ
            (Fin n)) - y‖ ^ 2 / (16 * t))) := hmul
      _ ≤ M0 * ((C1 + C2) * (Real.exp (1 / (16 * t)) * Real.exp (-‖x - y‖ ^ 2 / (32 * t)))) := hle2
      _ = (M0 * ((C1 + C2) * Real.exp (1 / (16 * t)))) * Real.exp (-‖x - y‖ ^ 2 / (32 * t)) := hring
  have h_diff : ∀ᵐ y ∂volume, ∀ s ∈ Set.Ioo ((x i) - 1) ((x i) + 1),
      HasDerivAt (fun s0 : ℝ => g y * gaussPolyKernel n Q k t
        ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y))
        (g y * (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y))) s := by
    apply Filter.Eventually.of_forall
    intro y s0 _
    have hdiff_w0 : DifferentiableAt ℝ (fun u : ℝ => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
        ((((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) i) :=
      aux_kernelUpdate_diff n Q k t
        ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i _
    have hHas : HasDerivAt (fun u : ℝ => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
        (deriv (fun u : ℝ => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
          ((((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) i))
        ((((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) i) :=
      hdiff_w0.hasDerivAt
    have hderiv_eq : deriv (fun u : ℝ => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
          ((((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) i)
        = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) :=
      hSpaceClosThm n Q k ht
        ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i
    have Hg : HasDerivAt (fun u : ℝ => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
        (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y))
        ((((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) i) := by
      rwa [hderiv_eq] at hHas
    have Hh : HasDerivAt (fun s : ℝ => s - y i) (1 : ℝ) s0 :=
      (hasDerivAt_id s0).sub_const (y i)
    have Hw0i : ((((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) i)
        = s0 - y i := by
      simp
    have h_shift : ∀ s : ℝ, (WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y
        = (WithLp.toLp 2 (Function.update
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i (s - y i)) :
          EuclideanSpace ℝ (Fin n)) := by
      intro s
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have Hf_eq : (fun s : ℝ => gaussPolyKernel n Q k t
          ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y))
        = (fun u : ℝ => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
          ∘ (fun s : ℝ => s - y i) := by
      apply funext
      intro s
      simp only [Function.comp_apply]
      congr 1
      exact h_shift s
    have Hg' : HasDerivAt (fun u : ℝ => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
        (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y))
        ((fun s : ℝ => s - y i) s0) := by
      simpa [Hw0i] using Hg
    have Hcomp : HasDerivAt ((fun u : ℝ => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y) i u)))
        ∘ (fun s : ℝ => s - y i))
        ((gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) * 1) s0 :=
      Hg'.comp s0 Hh
    have Hf : HasDerivAt (fun s : ℝ => gaussPolyKernel n Q k t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y))
        (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            ((WithLp.toLp 2 (Function.update x i s0) : EuclideanSpace ℝ (Fin n)) - y)) s0 := by
      rw [Hf_eq]
      simpa using Hcomp
    exact HasDerivAt.const_mul (g y) Hf
  have hLemma := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => g y * gaussPolyKernel n Q k t
      ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y))
    (F' := fun s y => g y * (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
      ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)
      + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
        ((WithLp.toLp 2 (Function.update x i s) : EuclideanSpace ℝ (Fin n)) - y)))
    (bound := fun y => (M0 * ((C1 + C2) * Real.exp (1 / (16 * t))))
      * Real.exp (-‖x - y‖ ^ 2 / (32 * t)))
    (s := Set.Ioo ((x i) - 1) ((x i) + 1))
    (x₀ := x i)
    (μ := volume)
    hs hF_meas hF_int hF'_meas h_bound hBound_int h_diff
  obtain ⟨_, hHasDeriv⟩ := hLemma
  convert hHasDeriv using 2
  apply funext
  intro y
  have hw : ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y) = x - y :=
    by
    rw [h_upd_self]
  have hderiv : deriv (fun s => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)
      = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (x - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t (x - y) :=
    hSpaceClosThm n Q k ht (x - y) i
  have h_eq : g y * (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          ((WithLp.toLp 2 (Function.update x i (x i)) : EuclideanSpace ℝ (Fin n)) - y))
      = g y * deriv (fun s => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i) := by
    rw [hw, hderiv]
  exact h_eq.symm

end FirstPartialAsm

section JointAsm

open MeasureTheory
open scoped Topology
open Asymptotics


private theorem coord_le_norm (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h1 : (x i) ^ 2 ≤ ∑ j, (x j) ^ 2 := by
    apply Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [← EuclideanSpace.real_norm_sq_eq x] at h1
  have h2 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa [sq_abs] using h1
  have hnonneg : 0 ≤ ‖x‖ := norm_nonneg _
  calc |x i| = √(|x i| ^ 2) := by rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ := Real.sqrt_sq hnonneg

private theorem monomial_le (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (e : Fin n →₀ ℕ) :
    |∏ i ∈ e.support, x i ^ e i| ≤ (1 + ‖x‖) ^ (e.sum fun _ k => k) := by
  calc |∏ i ∈ e.support, x i ^ e i|
      = ∏ i ∈ e.support, |x i| ^ e i := by
        rw [Finset.abs_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [abs_pow]
    _ ≤ ∏ i ∈ e.support, (1 + ‖x‖) ^ e i := by
        apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
        intro i _
        apply pow_le_pow_left₀ (abs_nonneg _) _ _
        calc |x i| ≤ ‖x‖ := coord_le_norm n x i
          _ ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    _ = (1 + ‖x‖) ^ (e.sum fun _ k => k) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1

private theorem poly_le (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    |MvPolynomial.eval (fun i => x i) Q|
      ≤ (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖x‖) ^ Q.totalDegree := by
  rw [MvPolynomial.eval_eq]
  calc |∑ d ∈ Q.support, Q.coeff d * ∏ i ∈ d.support, x i ^ d i|
      ≤ ∑ d ∈ Q.support, |Q.coeff d * ∏ i ∈ d.support, x i ^ d i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ Q.support, |Q.coeff d| * |∏ i ∈ d.support, x i ^ d i| := by
        apply Finset.sum_congr rfl
        intro d _
        rw [abs_mul]
    _ ≤ ∑ d ∈ Q.support, |Q.coeff d| * (1 + ‖x‖) ^ Q.totalDegree := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∏ i ∈ d.support, x i ^ d i|
            ≤ (1 + ‖x‖) ^ (d.sum fun _ k => k) := monomial_le n x d
          _ ≤ (1 + ‖x‖) ^ Q.totalDegree :=
              pow_le_pow_right₀ (by linarith [norm_nonneg x]) (MvPolynomial.le_totalDegree hd)
    _ = (∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖x‖) ^ Q.totalDegree := by
        rw [Finset.sum_mul]

private theorem polyGauss_integrable (n : ℕ) (D : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ D)
      := by
  refine (integrable_poly_gauss_aux n D (1 / (4 * t)) (by positivity)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  change (1 + ‖z‖) ^ D * Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2)
    = Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ D
  rw [mul_comm]
  congr 2
  ring

/-- Coordinate linear functional: the continuous linear map sending `h` to `∑ i, h i * D i`. -/
private noncomputable def mkSpaceLin (n : ℕ) (D : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  let Llin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := fun h => ∑ i, h i * D i
      map_add' := by
        intro x y
        simp [PiLp.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [PiLp.smul_apply, smul_eq_mul, Real.ringHom_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  LinearMap.mkContinuous Llin (∑ i, |D i|) (fun h => by
    calc ‖∑ i, h i * D i‖
        ≤ ∑ i, ‖h i * D i‖ := norm_sum_le _ _
      _ = ∑ i, |h i| * |D i| := by
          congr with i
          simp [norm_mul, Real.norm_eq_abs]
      _ ≤ ∑ i, ‖h‖ * |D i| := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact coord_le_norm n h i
      _ = ‖h‖ * ∑ i, |D i| := by rw [← Finset.mul_sum]
      _ = (∑ i, |D i|) * ‖h‖ := by ring)

private theorem trans_preserving (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun y => x - y) (volume : Measure (EuclideanSpace ℝ (Fin n))) volume := by
  have h1 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin n) => -y) volume volume :=
    Measure.measurePreserving_neg volume
  have h2 : MeasurePreserving (fun z : EuclideanSpace ℝ (Fin n) => x + z) volume volume :=
    measurePreserving_add_left volume x
  have hcomp := h2.comp h1
  have hEq : (fun y : EuclideanSpace ℝ (Fin n) => x - y)
      = (fun z => x + z) ∘ (fun y => -y) := by
    funext y
    simp [sub_eq_add_neg]
  rw [hEq]
  exact hcomp

private theorem poly_cont (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => z i) Q) := by
  have h1 : Continuous (fun z : EuclideanSpace ℝ (Fin n) => (fun i => z i)) := by
    rw [continuous_pi_iff]
    intro i
    exact PiLp.continuous_apply _ _ i
  exact (MvPolynomial.continuous_eval Q).comp h1

private theorem kernel_cont_z (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ) (t : ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z) := by
  unfold gaussPolyKernel
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.mul
      · exact continuous_const
      · apply Real.continuous_exp.comp
        apply Continuous.div_const
        apply Continuous.neg
        exact continuous_norm.pow 2
    · exact poly_cont n Q
  · exact continuous_const

private theorem kernel_bound (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ) (t : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    |gaussPolyKernel n Q k t z|
      ≤ |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * |t ^ (-(k : ℤ))|
        * (∑ d ∈ Q.support, |Q.coeff d|)
        * (Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ Q.totalDegree) := by
  unfold gaussPolyKernel
  have hP := poly_le n Q z
  have hexp : (0:ℝ) < Real.exp (-‖z‖ ^ 2 / (4 * t)) := Real.exp_pos _
  rw [abs_mul, abs_mul, abs_mul]
  rw [abs_of_pos hexp]
  calc |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * |MvPolynomial.eval (fun i => z i) Q| * |t ^ (-(k : ℤ))|
      ≤ |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * ((∑ d ∈ Q.support, |Q.coeff d|) * (1 + ‖z‖) ^ Q.totalDegree) * |t ^ (-(k : ℤ))| := by
        gcongr
    _ = |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * |t ^ (-(k : ℤ))|
        * (∑ d ∈ Q.support, |Q.coeff d|)
        * (Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ Q.totalDegree) := by ring

private theorem kernel_integrable_z (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z) := by
  set Cc : ℝ := |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * |t ^ (-(k : ℤ))|
    * (∑ d ∈ Q.support, |Q.coeff d|) with hCc
  have hPG := polyGauss_integrable n Q.totalDegree t ht
  have hg : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      Cc * (Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ Q.totalDegree)) :=
    hPG.const_mul Cc
  have hmeas : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t z) volume :=
    (kernel_cont_z n Q k t).aestronglyMeasurable
  apply Integrable.mono' hg hmeas
  filter_upwards with z
  have hbd := kernel_bound n Q k t z
  simp only [hCc] at hbd ⊢
  rw [Real.norm_eq_abs]
  calc |gaussPolyKernel n Q k t z|
      ≤ |(4 * Real.pi * t) ^ (-(n : ℝ) / 2)| * |t ^ (-(k : ℤ))|
        * (∑ d ∈ Q.support, |Q.coeff d|)
        * (Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ Q.totalDegree) := hbd
    _ = Cc * (Real.exp (-‖z‖ ^ 2 / (4 * t)) * (1 + ‖z‖) ^ Q.totalDegree) := by
        simp only [hCc]

private theorem kernel_integrable_trans (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (x - y)) := by
  have hK := kernel_integrable_z n Q k t ht
  have hpres := trans_preserving n x
  have hcomp := hpres.integrable_comp_of_integrable hK
  -- hcomp : Integrable ((fun z => K t z) ∘ (fun y => x - y))
  simpa [Function.comp_def] using hcomp

private theorem classConv_integrable (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t (x - y)) := by
  obtain ⟨M, hM⟩ := hg_bdd
  have hK := kernel_integrable_trans n Q k t ht x
  have hKmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (x - y)) volume :=
    hK.aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t (x - y)) volume :=
    hg_meas.mul hKmeas
  have hg : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      |M| * |gaussPolyKernel n Q k t (x - y)|) := by
    have h1 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        |gaussPolyKernel n Q k t (x - y)|) := hK.norm
    exact h1.const_mul |M|
  apply Integrable.mono' hg hmeas
  filter_upwards [hM] with y hy
  have hM' : |g y| ≤ |M| := le_trans hy (le_abs_self M)
  rw [Real.norm_eq_abs, abs_mul]
  calc |g y| * |gaussPolyKernel n Q k t (x - y)|
      ≤ |M| * |gaussPolyKernel n Q k t (x - y)| := by
        apply mul_le_mul_of_nonneg_right hM' (abs_nonneg _)

private theorem timeDeriv_cont (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (hContThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ))
    (hClosTimeThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)),
      deriv (fun s => gaussPolyKernel n Q k s x) t
        = gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t x
          + gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2) t x)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (q.2 - y)) q.1) (t, x) := by
  set Q1 : MvPolynomial (Fin n) ℝ := -(((n : ℝ) / 2 + (k : ℝ)) • Q) with hQ1
  set Q2 : MvPolynomial (Fin n) ℝ := (1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2) with hQ2
  have hC1 := hContThm n Q1 (k + 1) hg_meas hg_bdd
  have hC2 := hContThm n Q2 (k + 2) hg_meas hg_bdd
  have hmem : (t, x) ∈ Set.Ioi (0:ℝ) ×ˢ Set.univ := ⟨ht, Set.mem_univ x⟩
  have hOpen : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.univ : Set (ℝ × EuclideanSpace ℝ (Fin n))) :=
    isOpen_Ioi.prod isOpen_univ
  have hNbhd : Set.Ioi (0:ℝ) ×ˢ Set.univ ∈ nhds (t, x) := hOpen.mem_nhds hmem
  have hAt1 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      ∫ y, g y * gaussPolyKernel n Q1 (k + 1) q.1 (q.2 - y)) (t, x) :=
    hC1.continuousAt hNbhd
  have hAt2 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      ∫ y, g y * gaussPolyKernel n Q2 (k + 2) q.1 (q.2 - y)) (t, x) :=
    hC2.continuousAt hNbhd
  have hAdd : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (∫ y, g y * gaussPolyKernel n Q1 (k + 1) q.1 (q.2 - y))
        + (∫ y, g y * gaussPolyKernel n Q2 (k + 2) q.1 (q.2 - y))) (t, x) :=
    hAt1.add hAt2
  have hEq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (∫ y, g y * gaussPolyKernel n Q1 (k + 1) q.1 (q.2 - y))
        + (∫ y, g y * gaussPolyKernel n Q2 (k + 2) q.1 (q.2 - y)))
      =ᶠ[nhds (t, x)] (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (q.2 - y)) q.1) := by
    filter_upwards [hNbhd] with q hq
    have hq1 : (0:ℝ) < q.1 := hq.1
    have hInt1 := classConv_integrable n Q1 (k + 1) g hg_meas hg_bdd q.1 hq1 q.2
    have hInt2 := classConv_integrable n Q2 (k + 2) g hg_meas hg_bdd q.1 hq1 q.2
    have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
        g y * deriv (fun u => gaussPolyKernel n Q k u (q.2 - y)) q.1
          = g y * gaussPolyKernel n Q1 (k + 1) q.1 (q.2 - y)
            + g y * gaussPolyKernel n Q2 (k + 2) q.1 (q.2 - y) := by
      intro y
      have hcl := hClosTimeThm n Q k hq1 (q.2 - y)
      simp only [hQ1, hQ2] at hcl ⊢
      rw [hcl]
      ring
    have hCong : (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (q.2 - y)) q.1)
        = ∫ y, (g y * gaussPolyKernel n Q1 (k + 1) q.1 (q.2 - y)
          + g y * gaussPolyKernel n Q2 (k + 2) q.1 (q.2 - y)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpt
    rw [hCong, integral_add hInt1 hInt2]
  exact hAdd.congr hEq

private theorem spaceDeriv_cont (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (hContThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ))
    (hClosSpaceThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s))) (x i)
        = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t x
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t x)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * deriv (fun s => gaussPolyKernel n Q k q.1
          (WithLp.toLp 2 (Function.update (q.2 - y) i s))) ((q.2 - y) i)) (t, x) := by
  set Q1 : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv i Q with hQ1
  set Q2 : MvPolynomial (Fin n) ℝ := (-1 / 2 : ℝ) • (MvPolynomial.X i * Q) with hQ2
  have hC1 := hContThm n Q1 k hg_meas hg_bdd
  have hC2 := hContThm n Q2 (k + 1) hg_meas hg_bdd
  have hmem : (t, x) ∈ Set.Ioi (0:ℝ) ×ˢ Set.univ := ⟨ht, Set.mem_univ x⟩
  have hOpen : IsOpen (Set.Ioi (0:ℝ) ×ˢ Set.univ : Set (ℝ × EuclideanSpace ℝ (Fin n))) :=
    isOpen_Ioi.prod isOpen_univ
  have hNbhd : Set.Ioi (0:ℝ) ×ˢ Set.univ ∈ nhds (t, x) := hOpen.mem_nhds hmem
  have hAt1 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      ∫ y, g y * gaussPolyKernel n Q1 k q.1 (q.2 - y)) (t, x) :=
    hC1.continuousAt hNbhd
  have hAt2 : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      ∫ y, g y * gaussPolyKernel n Q2 (k + 1) q.1 (q.2 - y)) (t, x) :=
    hC2.continuousAt hNbhd
  have hAdd : ContinuousAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (∫ y, g y * gaussPolyKernel n Q1 k q.1 (q.2 - y))
        + (∫ y, g y * gaussPolyKernel n Q2 (k + 1) q.1 (q.2 - y))) (t, x) :=
    hAt1.add hAt2
  have hEq : (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (∫ y, g y * gaussPolyKernel n Q1 k q.1 (q.2 - y))
        + (∫ y, g y * gaussPolyKernel n Q2 (k + 1) q.1 (q.2 - y)))
      =ᶠ[nhds (t, x)] (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * deriv (fun s => gaussPolyKernel n Q k q.1
          (WithLp.toLp 2 (Function.update (q.2 - y) i s))) ((q.2 - y) i)) := by
    filter_upwards [hNbhd] with q hq
    have hq1 : (0:ℝ) < q.1 := hq.1
    have hInt1 := classConv_integrable n Q1 k g hg_meas hg_bdd q.1 hq1 q.2
    have hInt2 := classConv_integrable n Q2 (k + 1) g hg_meas hg_bdd q.1 hq1 q.2
    have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
        g y * deriv (fun s => gaussPolyKernel n Q k q.1
            (WithLp.toLp 2 (Function.update (q.2 - y) i s))) ((q.2 - y) i)
          = g y * gaussPolyKernel n Q1 k q.1 (q.2 - y)
            + g y * gaussPolyKernel n Q2 (k + 1) q.1 (q.2 - y) := by
      intro y
      have hcl := hClosSpaceThm n Q k hq1 (q.2 - y) i
      simp only [hQ1, hQ2, WithLp.ofLp_sub] at hcl ⊢
      rw [hcl]
      ring
    have hCong : (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k q.1
            (WithLp.toLp 2 (Function.update (q.2 - y) i s))) ((q.2 - y) i))
        = ∫ y, (g y * gaussPolyKernel n Q1 k q.1 (q.2 - y)
          + g y * gaussPolyKernel n Q2 (k + 1) q.1 (q.2 - y)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpt
    rw [hCong, integral_add hInt1 hInt2]
  exact hAdd.congr hEq

private theorem mkSpaceLin_apply (n : ℕ) (D : Fin n → ℝ) (h : EuclideanSpace ℝ (Fin n)) :
    mkSpaceLin n D h = ∑ i, h i * D i := rfl

private theorem norm_le_of_coord_sq (n : ℕ) (w z₀ z : EuclideanSpace ℝ (Fin n))
    (h : ∀ j, (w j - z₀ j) ^ 2 ≤ ((z - z₀) j) ^ 2) :
    ‖w - z₀‖ ≤ ‖z - z₀‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [PiLp.sub_apply]
  exact h j

private theorem spaceSlice_hasFDerivAt (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (hSpaceThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s) - y))
        (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)) (x i))
    (hContThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ))
    (hClosSpaceThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s))) (x i)
        = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t x
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t x)
    (s : ℝ) (hs : 0 < s) (z₀ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun z => ∫ y, g y * gaussPolyKernel n Q k s (z - y))
      (mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k s
        (WithLp.toLp 2 (Function.update (z₀ - y) i r))) ((z₀ - y) i))) z₀ := by
  set D : Fin n → ℝ := fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k s
    (WithLp.toLp 2 (Function.update (z₀ - y) i r))) ((z₀ - y) i) with hD
  refine HasFDerivAt.of_isLittleO ?_
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  set N : ℕ := (Finset.univ : Finset (Fin n)).card with hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set ε : ℝ := c / ((N : ℝ) + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; exact div_pos hc hN1
  have hev_all : ∀ᶠ q in 𝓝 (s, z₀), ∀ i, |(∫ y, g y * deriv (fun s => gaussPolyKernel n Q k q.1
      (WithLp.toLp 2 (Function.update (q.2 - y) i s))) ((q.2 - y) i)) - D i| ≤ ε := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hcont := spaceDeriv_cont n Q k g hg_meas hg_bdd hContThm hClosSpaceThm s hs z₀ i
    have hmem := hcont (Metric.closedBall_mem_nhds _ hεpos)
    filter_upwards [hmem] with q hq
    simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] at hq
    exact hq
  have htrans : ContinuousAt (fun z : EuclideanSpace ℝ (Fin n) => (s, z)) z₀ :=
    (Continuous.prodMk_right s).continuousAt
  have htrans' : Filter.Tendsto (fun z : EuclideanSpace ℝ (Fin n) => (s, z)) (𝓝 z₀)
      (𝓝 (s, z₀)) := htrans
  have hev_z : ∀ᶠ (z : EuclideanSpace ℝ (Fin n)) in 𝓝 z₀, ∀ i,
      |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k s
      (WithLp.toLp 2 (Function.update (z - y) i r))) ((z - y) i)) - D i| ≤ ε := by
    have h := Filter.Tendsto.eventually htrans' hev_all
    simpa using h
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev_z
  refine Metric.eventually_nhds_iff_ball.mpr ⟨δ, hδ, fun z hz => ?_⟩
  have hz_dist : dist z z₀ < δ := Metric.mem_ball.mp hz
  have hkz : ‖z - z₀‖ < δ := by rwa [dist_eq_norm_sub] at hz_dist
  set w : Finset (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun S => WithLp.toLp 2 (fun j => if j ∈ S then z j else z₀ j) with hw
  have w_apply : ∀ (S : Finset (Fin n)) (j : Fin n),
      (w S) j = (if j ∈ S then z j else z₀ j) := by
    intro S j
    simp only [hw, PiLp.toLp_apply]
  have hcoord_upd : ∀ (S : Finset (Fin n)) (i : Fin n), i ∉ S → ∀ (r : ℝ),
      r ∈ segment ℝ ((w S) i) (z i) → ∀ j,
      (((WithLp.toLp 2 (Function.update (w S) i r)) j - z₀ j) ^ 2 ≤ ((z - z₀) j) ^ 2) := by
    intro S i hi r hr j
    rw [PiLp.toLp_apply]
    rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      have hwSi : (w S) j = z₀ j := by rw [w_apply, ite_eq_right hi]
      have hseg := norm_sub_le_of_mem_segment hr
      rw [hwSi, Real.norm_eq_abs, Real.norm_eq_abs] at hseg
      rw [PiLp.sub_apply]
      exact sq_le_sq.mpr hseg
    · rw [Function.update_of_ne hj, w_apply]
      by_cases hjS : j ∈ S
      · rw [ite_eq_left hjS]
        apply le_of_eq
        rw [PiLp.sub_apply]
      · rw [ite_eq_right hjS, sub_self, pow_two, mul_zero]
        exact sq_nonneg _
  have hupd_ball : ∀ (S : Finset (Fin n)) (i : Fin n), i ∉ S → ∀ (r : ℝ),
      r ∈ segment ℝ ((w S) i) (z i) →
      WithLp.toLp 2 (Function.update (w S) i r) ∈ Metric.ball z₀ δ := by
    intro S i hi r hr
    rw [Metric.mem_ball, dist_eq_norm_sub]
    refine lt_of_le_of_lt ?_ hkz
    refine norm_le_of_coord_sq n _ _ _ ?_
    exact hcoord_upd S i hi r hr
  have tele : ∀ S : Finset (Fin n), ‖(∫ y, g y * gaussPolyKernel n Q k s (w S - y))
      - (∫ y, g y * gaussPolyKernel n Q k s (z₀ - y))
      - ∑ j ∈ S, ((z j - z₀ j) * D j)‖ ≤ (S.card : ℝ) * (ε * ‖z - z₀‖) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      have hw0 : w ∅ = z₀ := by
        apply PiLp.ext
        intro j
        rw [w_apply, ite_eq_right (Finset.notMem_empty j)]
      simp [hw0, Finset.sum_empty, Finset.card_empty]
    | insert i S hi IH =>
      have hwSi : (w S) i = z₀ i := by rw [w_apply, ite_eq_right hi]
      have hstep : w (insert i S) = WithLp.toLp 2 (Function.update (w S) i (z i)) := by
        apply PiLp.ext
        intro j
        simp only [w_apply]
        rcases eq_or_ne j i with rfl | hj
        · rw [ite_eq_left (Finset.mem_insert_self j S), Function.update_self]
        · simp only [Finset.mem_insert, hj, false_or]
          rw [Function.update_of_ne hj, ← w_apply]
      have hbase : w S = WithLp.toLp 2 (Function.update (w S) i ((w S) i)) := by
        apply PiLp.ext
        intro j
        simp only [w_apply]
        rcases eq_or_ne j i with rfl | hj
        · rw [Function.update_self, ← w_apply]
        · rw [Function.update_of_ne hj, ← w_apply]
      have hψ1 : (fun r' => ∫ y, g y * gaussPolyKernel n Q k s
          (WithLp.toLp 2 (Function.update (w S) i r') - y)) (z i)
          = ∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y) := by
        rw [hstep]
      have hψ0 : (fun r' => ∫ y, g y * gaussPolyKernel n Q k s
          (WithLp.toLp 2 (Function.update (w S) i r') - y)) ((w S) i)
          = ∫ y, g y * gaussPolyKernel n Q k s (w S - y) := by
        change (∫ y, g y * gaussPolyKernel n Q k s
          (WithLp.toLp 2 (Function.update (w S) i ((w S) i)) - y))
          = ∫ y, g y * gaussPolyKernel n Q k s (w S - y)
        conv => rhs; rw [hbase]
      have hDeriv_all : ∀ r, HasDerivAt (fun r' => ∫ y, g y * gaussPolyKernel n Q k s
          (WithLp.toLp 2 (Function.update (w S) i r') - y))
          (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k s (WithLp.toLp 2
            (Function.update ((WithLp.toLp 2 (Function.update (w S) i r)) - y) i u)))
            (((WithLp.toLp 2 (Function.update (w S) i r)) - y) i)) r := by
        intro r
        have h0 := hSpaceThm n Q k hg_meas hg_bdd hs
          (WithLp.toLp 2 (Function.update (w S) i r)) i
        have hpt : (WithLp.toLp 2 (Function.update (w S) i r)) i = r := by
          rw [PiLp.toLp_apply, Function.update_self]
        have hupd : ∀ r', Function.update (WithLp.toLp 2 (Function.update (w S) i r)) i r'
            = Function.update (w S) i r' := by
          intro r'
          funext j
          rcases eq_or_ne j i with rfl | hj
          · rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hj, Function.update_of_ne hj, PiLp.toLp_apply,
              Function.update_of_ne hj]
        simpa only [hupd, hpt, Function.update_self] using h0
      have hlin_all : ∀ r, HasDerivAt (fun y : ℝ => D i * y) (D i * 1) r :=
        fun r => HasDerivAt.const_mul (D i) (hasDerivAt_id r)
      have hf : ∀ r_ ∈ segment ℝ ((w S) i) (z i), HasDerivWithinAt
          ((fun r' => ∫ y, g y * gaussPolyKernel n Q k s
            (WithLp.toLp 2 (Function.update (w S) i r') - y)) - fun y => D i * y)
          ((∫ y, g y * deriv (fun r => gaussPolyKernel n Q k s (WithLp.toLp 2
            (Function.update ((WithLp.toLp 2 (Function.update (w S) i r_)) - y) i r)))
            (((WithLp.toLp 2 (Function.update (w S) i r_)) - y) i)) - D i * 1)
          (segment ℝ ((w S) i) (z i)) r_ := by
        intro r_ _
        exact ((hDeriv_all r_).sub (hlin_all r_)).hasDerivWithinAt
      have hbound : ∀ r_ ∈ segment ℝ ((w S) i) (z i),
          ‖(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k s (WithLp.toLp 2
            (Function.update ((WithLp.toLp 2 (Function.update (w S) i r_)) - y) i r)))
            (((WithLp.toLp 2 (Function.update (w S) i r_)) - y) i)) - D i * 1‖ ≤ ε := by
        intro r_ hr_
        have hmem_ball : WithLp.toLp 2 (Function.update (w S) i r_) ∈ Metric.ball z₀ δ :=
          hupd_ball S i hi r_ hr_
        have hmi := (hball _ hmem_ball) i
        rw [mul_one, Real.norm_eq_abs]
        exact hmi
      have hMVT := (convex_segment ..).norm_image_sub_le_of_norm_hasDerivWithin_le
        hf hbound (left_mem_segment ..) (right_mem_segment ..)
      have hstep_eq : ((fun r' => ∫ y, g y * gaussPolyKernel n Q k s
            (WithLp.toLp 2 (Function.update (w S) i r') - y)) - fun y => D i * y) (z i)
            - ((fun r' => ∫ y, g y * gaussPolyKernel n Q k s
            (WithLp.toLp 2 (Function.update (w S) i r') - y)) - fun y => D i * y) ((w S) i)
          = (∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * (z i - z₀ i) := by
        simp only [Pi.sub_apply, hψ1, hψ0]
        rw [hwSi]
        change (∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y)) - D i * (z i)
          - ((∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * z₀ i)
          = (∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * (z i - z₀ i)
        ring
      have hrhs : ε * ‖z i - (w S) i‖ ≤ ε * ‖z - z₀‖ := by
        have h1 : ‖z i - (w S) i‖ ≤ ‖z - z₀‖ := by
          have h2 : |(z - z₀) i| ≤ ‖z - z₀‖ := coord_le_norm n (z - z₀) i
          rw [PiLp.sub_apply] at h2
          rw [hwSi, Real.norm_eq_abs]
          exact h2
        exact mul_le_mul_of_nonneg_left h1 hεpos.le
      have hstep_le : ‖(∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
          - (∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * (z i - z₀ i)‖
          ≤ ε * ‖z - z₀‖ := by
        rw [hstep_eq] at hMVT
        exact le_trans hMVT hrhs
      have hsum : (∑ j ∈ insert i S, ((z j - z₀ j) * D j))
          = ((z i - z₀ i) * D i) + (∑ j ∈ S, ((z j - z₀ j) * D j)) :=
        Finset.sum_insert hi
      have hsplit : ((∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
          - (∫ y, g y * gaussPolyKernel n Q k s (z₀ - y))
          - (∑ j ∈ insert i S, ((z j - z₀ j) * D j)))
          = (((∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * (z i - z₀ i))
          + ((∫ y, g y * gaussPolyKernel n Q k s (w S - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (z₀ - y))
            - (∑ j ∈ S, ((z j - z₀ j) * D j)))) := by
        rw [hsum]
        ring
      calc ‖(∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (z₀ - y))
            - (∑ j ∈ insert i S, ((z j - z₀ j) * D j))‖
          = ‖(((∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * (z i - z₀ i))
          + ((∫ y, g y * gaussPolyKernel n Q k s (w S - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (z₀ - y))
            - (∑ j ∈ S, ((z j - z₀ j) * D j))))‖ := by rw [hsplit]
        _ ≤ ‖(∫ y, g y * gaussPolyKernel n Q k s (w (insert i S) - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (w S - y)) - D i * (z i - z₀ i)‖
            + ‖(∫ y, g y * gaussPolyKernel n Q k s (w S - y))
            - (∫ y, g y * gaussPolyKernel n Q k s (z₀ - y))
            - (∑ j ∈ S, ((z j - z₀ j) * D j))‖ := norm_add_le _ _
        _ ≤ (ε * ‖z - z₀‖) + ((S.card : ℝ) * (ε * ‖z - z₀‖)) :=
            add_le_add hstep_le IH
        _ = (((insert i S).card : ℝ)) * (ε * ‖z - z₀‖) := by
            rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
            ring
  have htele := tele Finset.univ
  have hwU : w Finset.univ = z := by
    apply PiLp.ext
    intro j
    rw [w_apply, ite_eq_left (Finset.mem_univ j)]
  rw [hwU] at htele
  have hL : (∑ i ∈ Finset.univ, ((z i - z₀ i) * D i))
      = (mkSpaceLin n D) (z - z₀) := by
    rw [map_sub, mkSpaceLin_apply, mkSpaceLin_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_mul]
  rw [hL, ← hN] at htele
  have hNc : (N : ℝ) * ε ≤ c := by
    rw [hε]
    have h1 : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_iff₀ hN1, one_mul]
      exact le_add_of_nonneg_right zero_le_one
    calc (N : ℝ) * (c / ((N : ℝ) + 1)) = c * ((N : ℝ) / ((N : ℝ) + 1)) := by ring
      _ ≤ c * 1 := by exact mul_le_mul_of_nonneg_left h1 hc.le
      _ = c := mul_one c
  have hfin : (N : ℝ) * (ε * ‖z - z₀‖) ≤ c * ‖z - z₀‖ := by
    calc (N : ℝ) * (ε * ‖z - z₀‖) = (((N : ℝ) * ε)) * ‖z - z₀‖ := by ring
      _ ≤ c * ‖z - z₀‖ := by exact mul_le_mul_of_nonneg_right hNc (norm_nonneg _)
  exact le_trans htele hfin

/-- Joint differentiability of a class-member convolution, assembled
from its time and space partials. -/
private theorem classConv_hasFDerivAt_joint_asm (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (hTimeThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)),
      HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k s (x - y))
        (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k s (x - y)) t) t)
    (hSpaceThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s) - y))
        (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)) (x i))
    (hContThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ))
    (hClosTimeThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)),
      deriv (fun s => gaussPolyKernel n Q k s x) t
        = gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t x
          + gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2) t x)
    (hClosSpaceThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s))) (x i)
        = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t x
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t x)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (ContinuousLinearMap.coprod
          (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
            (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (x - y)) t))
          L)
        (t, x)
        ∧ ∀ h : EuclideanSpace ℝ (Fin n),
          L h = ∑ i, h i * (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
            (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)) := by
  have hNbhd : Set.Ioi (0 : ℝ) ×ˢ Set.univ ∈ 𝓝 (t, x) := by
    have hmem : (t, x) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ := ⟨ht, Set.mem_univ x⟩
    have hOpen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.univ : Set (ℝ × EuclideanSpace ℝ (Fin n))) :=
      isOpen_Ioi.prod isOpen_univ
    exact hOpen.mem_nhds hmem
  have df₁ : ∀ᶠ v in 𝓝 (t, x), HasFDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k s (v.2 - y))
      (ContinuousLinearMap.toSpanSingleton ℝ
        (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (v.2 - y)) v.1)) v.1 := by
    filter_upwards [hNbhd] with v hv
    have hv1 : (0 : ℝ) < v.1 := hv.1
    exact (hTimeThm n Q k hg_meas hg_bdd hv1 v.2).hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 (t, x), HasFDerivAt (fun z => ∫ y, g y * gaussPolyKernel n Q k v.1 (z - y))
      (mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
        (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))) v.2 := by
    filter_upwards [hNbhd] with v hv
    have hv1 : (0 : ℝ) < v.1 := hv.1
    exact spaceSlice_hasFDerivAt n Q k g hg_meas hg_bdd hSpaceThm hContThm hClosSpaceThm v.1 hv1 v.2
  have cf₁ : ContinuousAt (fun v : ℝ × EuclideanSpace ℝ (Fin n) =>
      ContinuousLinearMap.toSpanSingleton ℝ
        (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (v.2 - y)) v.1)) (t, x) := by
    have hDt := timeDeriv_cont n Q k g hg_meas hg_bdd hContThm hClosTimeThm t ht x
    have hcle : Continuous (fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ c) :=
      ContinuousLinearEquiv.continuous
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ))
    exact hcle.continuousAt.comp hDt
  have cf₂ : ContinuousAt (fun v : ℝ × EuclideanSpace ℝ (Fin n) => mkSpaceLin n
      (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
        (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))) (t, x) := by
    change Filter.Tendsto _ (𝓝 (t, x)) (𝓝 _)
    intro S hS
    obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.mp hS
    set N : ℕ := (Finset.univ : Finset (Fin n)).card with hN
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    set ε' : ℝ := ε / ((N : ℝ) + 1) with hε'
    have hε'pos : 0 < ε' := by rw [hε']; exact div_pos hε hN1
    have hev : ∀ᶠ v in 𝓝 (t, x), ∀ i, |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
        (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
        - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))| ≤ ε' := by
      refine Filter.eventually_all.mpr fun i => ?_
      have hcont := spaceDeriv_cont n Q k g hg_meas hg_bdd hContThm hClosSpaceThm t ht x i
      have hmem := hcont (Metric.closedBall_mem_nhds _ hε'pos)
      filter_upwards [hmem] with v hv
      simp only [Set.mem_preimage, Metric.mem_closedBall, Real.dist_eq] at hv
      exact hv
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    have hmem_ball : Metric.ball (t, x) δ ∈ 𝓝 (t, x) := Metric.ball_mem_nhds _ hδ
    have hsub : Metric.ball (t, x) δ ⊆ (fun v : ℝ × EuclideanSpace ℝ (Fin n) => mkSpaceLin n
        (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
          (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))) ⁻¹' S := by
      intro v hv
      have hper := hball v hv
      have hlt : dist (mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
          (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i)))
          (mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))) < ε := by
        have hop : ‖mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
            (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
            - mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
            (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))‖
            ≤ ∑ i, |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
              (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
              - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
              (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))| := by
          refine (mkSpaceLin n _ - mkSpaceLin n _).opNorm_le_bound ?_ ?_
          · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
          · intro h
            calc ‖(mkSpaceLin n _ - mkSpaceLin n _) h‖
                = ‖∑ i, (h i * (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                    (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                  - h i * (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                    (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i)))‖ := by
                  rw [sub_apply, mkSpaceLin_apply, mkSpaceLin_apply, ← Finset.sum_sub_distrib]
              _ ≤ ∑ i, ‖h i * (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                    (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                  - h i * (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                    (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))‖ :=
                  norm_sum_le _ _
              _ = ∑ i, |h i| * |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                    (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                  - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                    (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))| := by
                  apply Finset.sum_congr rfl
                  intro i _
                  have hmul : h i * (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                      (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                      - h i * (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                      (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))
                      = h i * ((∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                      (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                      - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                      (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))) :=
                    (mul_sub _ _ _).symm
                  rw [hmul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
              _ ≤ ∑ i, ‖h‖ * |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                    (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                  - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                    (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))| := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact mul_le_mul_of_nonneg_right (coord_le_norm n h i) (abs_nonneg _)
              _ = (∑ i, |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                    (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                  - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                    (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))|) * ‖h‖ := by
                  rw [← Finset.mul_sum]
                  exact mul_comm _ _
        have hsum : (∑ i, |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
            (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
            - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
            (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))|) < ε := by
          have hle : (∑ i, |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
              (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
              - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
              (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))|)
              ≤ (N : ℝ) * ε' := by
            calc (∑ i, |(∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
                (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
                - (∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
                (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))|)
                ≤ ∑ _i : Fin n, ε' := Finset.sum_le_sum (fun i _ => hper i)
              _ = (N : ℝ) * ε' := by rw [Finset.sum_const, hN, nsmul_eq_mul]
          have hlt' : (N : ℝ) * ε' < ε := by
            rw [hε']
            have h1 : (N : ℝ) / ((N : ℝ) + 1) < 1 := by
              rw [div_lt_iff₀ hN1, one_mul]
              exact lt_add_one _
            calc (N : ℝ) * (ε / ((N : ℝ) + 1)) = ε * ((N : ℝ) / ((N : ℝ) + 1)) := by ring
              _ < ε * 1 := by exact mul_lt_mul_of_pos_left h1 hε
              _ = ε := mul_one ε
          exact lt_of_le_of_lt hle hlt'
        rw [dist_eq_norm_sub]
        exact lt_of_le_of_lt hop hsum
      have hmem : mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k v.1
          (WithLp.toLp 2 (Function.update (v.2 - y) i r))) ((v.2 - y) i))
          ∈ Metric.ball (mkSpaceLin n (fun i => ∫ y, g y * deriv (fun r => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update (x - y) i r))) ((x - y) i))) ε :=
        Metric.mem_ball.mpr hlt
      exact hεS hmem
    simpa using Filter.mem_of_superset hmem_ball hsub
  have hJ := hasStrictFDerivAt_uncurry_coprod
    (f := fun s z => ∫ y, g y * gaussPolyKernel n Q k s (z - y))
    (f₁ := fun s z => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (z - y)) s))
    (f₂ := fun t z => mkSpaceLin n
      (fun i => ∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update (z - y) i s))) ((z - y) i)))
    (u := (t, x)) df₁ df₂ cf₁ cf₂
  refine ⟨mkSpaceLin n (fun i => ∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
    (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)), ?_, ?_⟩
  · exact hJ.hasFDerivAt
  · intro h
    exact mkSpaceLin_apply n _ h

end JointAsm

/-! ## F. Joint differentiability and `fderiv` decomposition -/

section DecompAsm

open MeasureTheory


/-- A power of `r ≥ 0` is bounded by a multiple of `exp (c * r ^ 2)`. -/
private theorem pow_le_const_mul_exp (c : ℝ) (hc : 0 < c) (D : ℕ) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ r : ℝ, 0 ≤ r → r ^ D ≤ C2 * Real.exp (c * r ^ 2) := by
  set m : ℕ := D + 1 with hm_def
  have hmpos : (0 : ℝ) < m := by
    rw [hm_def]
    positivity
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  refine ⟨1 + ((m : ℝ) / c) ^ m, add_nonneg zero_le_one
    (pow_nonneg (le_of_lt (div_pos hmpos hc)) _), fun r hr => ?_⟩
  have hpow : r ^ D ≤ 1 + (r ^ 2) ^ m := by
    have h2m : r ^ (2 * m) = (r ^ 2) ^ m := pow_mul r 2 m
    have hle : r ^ D ≤ 1 + r ^ (2 * m) := by
      by_cases hr1 : r ≤ 1
      · calc r ^ D ≤ 1 := pow_le_one₀ hr hr1
          _ ≤ 1 + r ^ (2 * m) := le_add_of_nonneg_right (pow_nonneg hr _)
      · have hr1' : (1 : ℝ) < r := lt_of_not_ge hr1
        calc r ^ D ≤ r ^ (2 * m) := pow_le_pow_right₀ (le_of_lt hr1') (by omega)
          _ ≤ 1 + r ^ (2 * m) := le_add_of_nonneg_left zero_le_one
    rwa [h2m] at hle
  have hE : (c * r ^ 2 / m) ^ m ≤ Real.exp (c * r ^ 2) := by
    have hu : (0 : ℝ) ≤ c * r ^ 2 / m := by positivity
    have hbase : (c * r ^ 2 / m) ^ m ≤ (Real.exp (c * r ^ 2 / m)) ^ m :=
      calc (c * r ^ 2 / m) ^ m ≤ (c * r ^ 2 / m + 1) ^ m :=
              pow_le_pow_left₀ hu (le_add_of_nonneg_right zero_le_one) m
        _ ≤ (Real.exp (c * r ^ 2 / m)) ^ m :=
              pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) m
    have hEm : Real.exp (c * r ^ 2) = (Real.exp (c * r ^ 2 / m)) ^ m := by
      have h1 : c * r ^ 2 = m * (c * r ^ 2 / m) := by field_simp
      conv_lhs => rw [h1]
      rw [Real.exp_nat_mul]
    rw [hEm]
    exact hbase
  have hK : (0 : ℝ) ≤ ((m : ℝ) / c) ^ m :=
    pow_nonneg (le_of_lt (div_pos hmpos hc)) _
  have h2 : (r ^ 2) ^ m = ((m : ℝ) / c) ^ m * (c * r ^ 2 / m) ^ m := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h3 : (r ^ 2) ^ m ≤ ((m : ℝ) / c) ^ m * Real.exp (c * r ^ 2) := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left hE hK
  have h1E : (1 : ℝ) ≤ Real.exp (c * r ^ 2) :=
    Real.one_le_exp (mul_nonneg hc.le (sq_nonneg r))
  calc r ^ D ≤ 1 + (r ^ 2) ^ m := hpow
    _ ≤ 1 + ((m : ℝ) / c) ^ m * Real.exp (c * r ^ 2) :=
          add_le_add_right h3 1
    _ ≤ Real.exp (c * r ^ 2) + ((m : ℝ) / c) ^ m * Real.exp (c * r ^ 2) :=
          add_le_add_left h1E _
    _ = (1 + ((m : ℝ) / c) ^ m) * Real.exp (c * r ^ 2) := by ring

/-- A multivariate polynomial is bounded by a multiple of `1 + ‖z‖ ^ D`. -/
private theorem mvpoly_eval_le_one_add_pow (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C1 : ℝ, ∃ D : ℕ, 0 ≤ C1 ∧ ∀ z : EuclideanSpace ℝ (Fin n),
      |MvPolynomial.eval (fun i => z i) Q| ≤ C1 * (1 + ‖z‖ ^ D) := by
  refine ⟨Q.support.sum (fun d => |Q.coeff d|),
    Q.support.sum (fun d => ∑ i, d i), Finset.sum_nonneg (fun d _ => abs_nonneg _),
    fun z => ?_⟩
  have hcoord : ∀ i : Fin n, |z i| ≤ ‖z‖ := fun i => PiLp.norm_apply_le z i
  have hr : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  have habs : ∀ (s : Finset (Fin n)) (f : Fin n → ℝ),
      |∏ i ∈ s, f i| = ∏ i ∈ s, |f i| := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, abs_mul, ih]
  have hterm : ∀ d ∈ Q.support,
      |Q.coeff d * ∏ i ∈ d.support, z i ^ d i|
        ≤ |Q.coeff d| * (1 + ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i)) := by
    intro d hd
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [habs]
    simp only [abs_pow]
    have hmono : ∏ i ∈ d.support, |z i| ^ d i ≤ ‖z‖ ^ (∑ i ∈ d.support, d i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      gcongr with i hi
      exact hcoord i
    have hexp : (∑ i ∈ d.support, d i) ≤ Q.support.sum (fun d => ∑ i, d i) := by
      calc (∑ i ∈ d.support, d i) ≤ ∑ i ∈ Finset.univ, d i :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun i _ _ => Nat.zero_le _)
        _ = ∑ i, d i := rfl
        _ ≤ Q.support.sum (fun d => ∑ i, d i) :=
              Finset.single_le_sum (f := fun d => ∑ i, d i)
                (fun d _ => Nat.zero_le _) hd
    have hpow : ‖z‖ ^ (∑ i ∈ d.support, d i)
        ≤ 1 + ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i) := by
      by_cases hr1 : ‖z‖ ≤ 1
      · calc ‖z‖ ^ (∑ i ∈ d.support, d i) ≤ 1 := pow_le_one₀ hr hr1
          _ ≤ 1 + ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i) :=
                le_add_of_nonneg_right (pow_nonneg hr _)
      · have hr1' : (1 : ℝ) < ‖z‖ := lt_of_not_ge hr1
        calc ‖z‖ ^ (∑ i ∈ d.support, d i) ≤ ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i) :=
                pow_le_pow_right₀ (le_of_lt hr1') hexp
          _ ≤ 1 + ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i) :=
                le_add_of_nonneg_left zero_le_one
    exact hmono.trans hpow
  rw [MvPolynomial.eval_eq]
  calc |∑ d ∈ Q.support, Q.coeff d * ∏ i ∈ d.support, z i ^ d i|
        = ‖∑ d ∈ Q.support, Q.coeff d * ∏ i ∈ d.support, z i ^ d i‖ :=
          (Real.norm_eq_abs _).symm
    _ ≤ ∑ d ∈ Q.support, ‖Q.coeff d * ∏ i ∈ d.support, z i ^ d i‖ :=
          norm_sum_le _ _
    _ = ∑ d ∈ Q.support, |Q.coeff d * ∏ i ∈ d.support, z i ^ d i| := by
          simp only [Real.norm_eq_abs]
    _ ≤ ∑ d ∈ Q.support, |Q.coeff d|
            * (1 + ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i)) :=
          Finset.sum_le_sum hterm
    _ = (∑ d ∈ Q.support, |Q.coeff d|)
            * (1 + ‖z‖ ^ (Q.support.sum fun d => ∑ i, d i)) :=
          (Finset.sum_mul _ _ _).symm

private theorem continuous_kernel (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (x - y) := by
  have hsub : Continuous fun y : EuclideanSpace ℝ (Fin n) => x - y :=
    continuous_const.sub continuous_id
  have hexp : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖x - y‖ ^ 2 / (4 * t)) :=
    Real.continuous_exp.comp (((hsub.norm.pow 2).neg).div_const _)
  have hinner : Continuous fun y : EuclideanSpace ℝ (Fin n) => (fun i => (x - y) i) :=
    continuous_pi_iff.mpr fun i => (PiLp.continuous_apply 2 (fun _ => ℝ) i).comp hsub
  have hpoly : Continuous fun y : EuclideanSpace ℝ (Fin n) =>
      MvPolynomial.eval (fun i => (x - y) i) Q :=
    (MvPolynomial.continuous_eval Q).comp hinner
  unfold gaussPolyKernel
  exact ((continuous_const.mul hexp).mul hpoly).mul continuous_const

private theorem integrable_kernel (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (x - y))
      volume := by
  obtain ⟨C1, D, hC1, hP⟩ := mvpoly_eval_le_one_add_pow n Q
  have hc : (0:ℝ) < 1 / (8 * t) := by positivity
  obtain ⟨C2, hC2, hE⟩ := pow_le_const_mul_exp (1 / (8 * t)) hc D
  have ht' : t ≠ 0 := ne_of_gt ht
  have h4t : (0:ℝ) < 4 * t := by positivity
  have h8t : (0:ℝ) < 8 * t := by positivity
  have h16t : (0:ℝ) < 16 * t := by positivity
  have hA : (0:ℝ) < (4 * Real.pi * t) ^ (-(n:ℝ)/2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hB : (0:ℝ) < t ^ (-(k:ℤ)) := zpow_pos ht _
  have hbound : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖gaussPolyKernel n Q k t (x - y)‖
        ≤ ((4 * Real.pi * t) ^ (-(n:ℝ)/2) * t ^ (-(k:ℤ)) * (C1 * (1 + C2))
            * Real.exp (‖x‖^2/(8*t))) * Real.exp (-‖y‖^2/(16*t)) := by
    intro y
    have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have h := norm_sub_le x (x - y)
      rwa [sub_sub_cancel] at h
    have hsq : ‖y‖^2 ≤ 2*‖x‖^2 + 2*‖x-y‖^2 := by
      have h1 : ‖y‖^2 ≤ (‖x‖ + ‖x - y‖)^2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      have h2 : (‖x‖ + ‖x - y‖)^2 ≤ 2*‖x‖^2 + 2*‖x-y‖^2 := by
        nlinarith [sq_nonneg (‖x‖ - ‖x - y‖)]
      exact h1.trans h2
    have hdiv : ‖y‖^2/(16*t) ≤ ‖x‖^2/(8*t) + ‖x-y‖^2/(8*t) := by
      have heq : (‖x‖^2/(8*t) + ‖x-y‖^2/(8*t)) * (16*t)
          = 2*‖x‖^2 + 2*‖x-y‖^2 := by field_simp; ring
      rw [div_le_iff₀ h16t, heq]
      exact hsq
    have hE2 : -‖x-y‖^2/(8*t) ≤ -‖y‖^2/(16*t) + ‖x‖^2/(8*t) := by
      rw [neg_div, neg_div]
      set A := ‖x-y‖^2/(8*t) with hAdef
      set B := ‖y‖^2/(16*t) with hBdef
      set C := ‖x‖^2/(8*t) with hCdef
      have hdiv' : B ≤ C + A := hdiv
      linarith [hdiv']
    have hE1 : -‖x-y‖^2/(4*t) + (1/(8*t)) * ‖x-y‖^2 = -‖x-y‖^2/(8*t) := by
      field_simp; ring
    have hPz := hP (x - y)
    have hEz := hE ‖x - y‖ (norm_nonneg _)
    have h1E : (1:ℝ) ≤ Real.exp ((1/(8*t)) * ‖x-y‖^2) :=
      Real.one_le_exp (mul_nonneg hc.le (sq_nonneg _))
    have hC3 : (0:ℝ) ≤ C1 * (1 + C2) := mul_nonneg hC1 (add_nonneg zero_le_one hC2)
    have hPle : |MvPolynomial.eval (fun i => (x - y) i) Q|
        ≤ (C1 * (1 + C2)) * Real.exp ((1/(8*t)) * ‖x-y‖^2) := by
      calc |MvPolynomial.eval (fun i => (x - y) i) Q|
            ≤ C1 * (1 + ‖x-y‖^D) := hPz
        _ ≤ C1 * (1 + C2 * Real.exp ((1/(8*t)) * ‖x-y‖^2)) :=
              mul_le_mul_of_nonneg_left (add_le_add_right hEz 1) hC1
        _ ≤ C1 * ((1 + C2) * Real.exp ((1/(8*t)) * ‖x-y‖^2)) := by
              apply mul_le_mul_of_nonneg_left _ hC1
              calc (1:ℝ) + C2 * Real.exp ((1/(8*t)) * ‖x-y‖^2)
                    ≤ Real.exp ((1/(8*t)) * ‖x-y‖^2)
                      + C2 * Real.exp ((1/(8*t)) * ‖x-y‖^2) :=
                      add_le_add_left h1E _
                _ = (1 + C2) * Real.exp ((1/(8*t)) * ‖x-y‖^2) := by ring
        _ = (C1 * (1 + C2)) * Real.exp ((1/(8*t)) * ‖x-y‖^2) := by ring
    have hK : ‖gaussPolyKernel n Q k t (x - y)‖
        = (4 * Real.pi * t) ^ (-(n:ℝ)/2) * Real.exp (-‖x-y‖^2/(4*t))
          * |MvPolynomial.eval (fun i => (x - y) i) Q| * t ^ (-(k:ℤ)) := by
      unfold gaussPolyKernel
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hA,
        abs_of_pos (Real.exp_pos _), abs_of_pos hB]
    rw [hK]
    calc (4 * Real.pi * t) ^ (-(n:ℝ)/2) * Real.exp (-‖x-y‖^2/(4*t))
            * |MvPolynomial.eval (fun i => (x - y) i) Q| * t ^ (-(k:ℤ))
          ≤ (4 * Real.pi * t) ^ (-(n:ℝ)/2) * Real.exp (-‖x-y‖^2/(4*t))
            * ((C1 * (1 + C2)) * Real.exp ((1/(8*t)) * ‖x-y‖^2)) * t ^ (-(k:ℤ)) := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hB)
            apply mul_le_mul_of_nonneg_left _ _
            · exact hPle
            · exact mul_nonneg (le_of_lt hA) (le_of_lt (Real.exp_pos _))
        _ = ((4 * Real.pi * t) ^ (-(n:ℝ)/2) * t ^ (-(k:ℤ)) * (C1 * (1 + C2)))
            * (Real.exp (-‖x-y‖^2/(4*t)) * Real.exp ((1/(8*t)) * ‖x-y‖^2)) := by ring
        _ = ((4 * Real.pi * t) ^ (-(n:ℝ)/2) * t ^ (-(k:ℤ)) * (C1 * (1 + C2)))
            * Real.exp (-‖x-y‖^2/(8*t)) := by rw [← Real.exp_add, hE1]
        _ ≤ ((4 * Real.pi * t) ^ (-(n:ℝ)/2) * t ^ (-(k:ℤ)) * (C1 * (1 + C2)))
            * Real.exp (-‖y‖^2/(16*t) + ‖x‖^2/(8*t)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE2)
              (mul_nonneg (mul_nonneg (le_of_lt hA) (le_of_lt hB)) hC3)
        _ = (((4 * Real.pi * t) ^ (-(n:ℝ)/2) * t ^ (-(k:ℤ)) * (C1 * (1 + C2)))
            * Real.exp (‖x‖^2/(8*t))) * Real.exp (-‖y‖^2/(16*t)) := by
            rw [Real.exp_add]; ring
  have hg : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (((4 * Real.pi * t) ^ (-(n:ℝ)/2) * t ^ (-(k:ℤ)) * (C1 * (1 + C2))
        * Real.exp (‖x‖^2/(8*t))) * Real.exp (-‖y‖^2/(16*t)))) volume := by
    have hexp : ∀ y : EuclideanSpace ℝ (Fin n),
        -‖y‖^2/(16*t) = -(1/(16*t)) * ‖y‖^2 := fun y => by field_simp
    simp only [hexp]
    exact (integrable_real_exp_neg_mul_sq_norm (Fin n)
      (show (0:ℝ) < 1/(16*t) by positivity)).const_mul _
  exact Integrable.mono' hg (continuous_kernel n Q k ht x).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The `fderiv` of a class-member convolution is a `coprod` of
class-member convolutions. -/
private theorem classConv_fderiv_decomp_asm (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (hJointThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
          (ContinuousLinearMap.coprod
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
              (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (x - y)) t))
            L)
          (t, x)
          ∧ ∀ h : EuclideanSpace ℝ (Fin n),
            L h = ∑ i, h i * (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
              (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)))
    (hClosTimeThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)),
      deriv (fun s => gaussPolyKernel n Q k s x) t
        = gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t x
          + gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2) t x)
    (hClosSpaceThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {t : ℝ} (_ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s))) (x i)
        = gaussPolyKernel n (MvPolynomial.pderiv i Q) k t x
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t x)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ L' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y)) (t, x)
        = ContinuousLinearMap.coprod
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
              ((∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t (x - y))
                + (∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k
                  + 2) t (x - y))))
            L'
      ∧ ∀ h : EuclideanSpace ℝ (Fin n),
        L' h = ∑ i, h i * ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (x - y))
          + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t (x -
            y))) := by
  obtain ⟨L, hDeriv, hL⟩ := hJointThm n Q k hg_meas hg_bdd ht x
  obtain ⟨M, hM⟩ := hg_bdd
  have hg_norm : ∀ᵐ y, ‖g y‖ ≤ M := hM.mono fun y hy => by rwa [Real.norm_eq_abs]
  have hint : ∀ (Q' : MvPolynomial (Fin n) ℝ) (k' : ℕ),
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        g y * gaussPolyKernel n Q' k' t (x - y)) volume :=
    fun Q' k' => Integrable.bdd_mul (integrable_kernel n Q' k' ht x) hg_meas hg_norm
  refine ⟨L, ?_, ?_⟩
  · rw [hDeriv.fderiv]
    congr 1
    congr 1
    have e1 := hint (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1)
    have e2 := hint ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2)
    have hcongr : (fun y : EuclideanSpace ℝ (Fin n) =>
            g y * deriv (fun u => gaussPolyKernel n Q k u (x - y)) t)
          =ᵐ[volume] (fun y =>
            (g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t (x - y))
            + (g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
              (k + 2) t (x - y))) :=
      Filter.Eventually.of_forall fun y => by
        change g y * deriv (fun u => gaussPolyKernel n Q k u (x - y)) t
          = (g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t (x - y))
            + (g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
              (k + 2) t (x - y))
        rw [hClosTimeThm n Q k ht (x - y)]
        ring
    rw [integral_congr_ae hcongr]
    exact integral_add e1 e2
  · intro h
    rw [hL h]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have e3 := hint (MvPolynomial.pderiv i Q) k
    have e4 := hint ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1)
    have hcongr : (fun y : EuclideanSpace ℝ (Fin n) =>
            g y * deriv (fun s => gaussPolyKernel n Q k t
              (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i))
          =ᵐ[volume] (fun y =>
            (g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (x - y))
            + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q))
              (k + 1) t (x - y))) :=
      Filter.Eventually.of_forall fun y => by
        change g y * deriv (fun s => gaussPolyKernel n Q k t
            (WithLp.toLp 2 (Function.update (x - y).ofLp i s))) ((x - y).ofLp i)
          = (g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (x - y))
            + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q))
              (k + 1) t (x - y))
        rw [hClosSpaceThm n Q k ht (x - y) i]
        ring
    rw [integral_congr_ae hcongr]
    exact integral_add e3 e4

end DecompAsm

/-! ## G. Induction to `ContDiffOn ∞` and specialization -/

section H3Step

open MeasureTheory


/-- Coordinate evaluation on `EuclideanSpace` as an inner product. -/
private theorem coordProj_apply (n : ℕ) (i : Fin n) (h : EuclideanSpace ℝ (Fin n)) :
    (innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) h = h i := by
  rw [innerSL_apply_apply, EuclideanSpace.inner_single_left]
  simp

/-- Induction step: `ContDiffOn (m+1)` for a class-member
convolution, from `ContDiffOn m` for all class members and the
`fderiv` decomposition. -/
private theorem classConv_contDiffOn_succ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (m : ℕ)
    (hIHThm : ∀ (Q' : MvPolynomial (Fin n) ℝ) (k' : ℕ)
      {g' : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g' volume → (∃ M : ℝ, ∀ᵐ y, |g' y| ≤ M) →
      ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g' y * gaussPolyKernel n Q' k' q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ))
    (hJointThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
          (ContinuousLinearMap.coprod
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
              (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (x - y)) t))
            L)
          (t, x)
          ∧ ∀ h : EuclideanSpace ℝ (Fin n),
            L h = ∑ i, h i * (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
              (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)))
    (hDecompThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ L' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y)) (t, x)
          = ContinuousLinearMap.coprod
              (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
                ((∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t (x - y))
                  + (∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
                    (k + 2) t (x - y))))
              L'
        ∧ ∀ h : EuclideanSpace ℝ (Fin n),
          L' h = ∑ i, h i * ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (x - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t (x -
              y)))) :
    ContDiffOn ℝ (m + 1) (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hs : IsOpen (Set.Ioi 0 ×ˢ Set.univ : Set (ℝ × EuclideanSpace ℝ (Fin n))) :=
    isOpen_Ioi.prod isOpen_univ
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨?_, fun h => absurd h (by simp), ?_⟩
  · intro q hq
    obtain ⟨ht, -⟩ := hq
    obtain ⟨L, hL, -⟩ := hJointThm n Q k hg_meas hg_bdd ht q.2
    exact hL.differentiableAt.differentiableWithinAt
  · have hA1 : ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      hIHThm _ _ hg_meas hg_bdd
    have hA2 : ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2) q.1
          (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      hIHThm _ _ hg_meas hg_bdd
    have hDt : ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        (∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) q.1 (q.2 - y))
          + (∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2)) (k + 2)
            q.1 (q.2 - y)))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      hA1.add hA2
    have hB1 : ∀ i : Fin n, ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      fun i => hIHThm _ _ hg_meas hg_bdd
    have hB2 : ∀ i : Fin n, ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) q.1
          (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      fun i => hIHThm _ _ hg_meas hg_bdd
    have hC : ∀ i : Fin n, ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1 (q.2 - y))
          + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) q.1
            (q.2 - y)))
        (Set.Ioi 0 ×ˢ Set.univ) :=
      fun i => (hB1 i).add (hB2 i)
    have hA : ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
          ((∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) q.1 (q.2 - y))
            + (∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
              (k + 2) q.1 (q.2 - y))))
        (Set.Ioi 0 ×ˢ Set.univ) := by
      have hconst : ContDiffOn ℝ m (fun _ : ℝ × EuclideanSpace ℝ (Fin n) =>
          ContinuousLinearMap.id ℝ ℝ) (Set.Ioi 0 ×ˢ Set.univ) := contDiffOn_const
      exact hconst.smulRight hDt
    have hB : ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∑ i, ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1 (q.2 - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1)
              q.1 (q.2 - y)))
          • innerSL ℝ (EuclideanSpace.single i (1 : ℝ)))
        (Set.Ioi 0 ×ˢ Set.univ) := by
      apply ContDiffOn.sum
      intro i _
      have hPconst : ContDiffOn ℝ m (fun _ : ℝ × EuclideanSpace ℝ (Fin n) =>
          innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) (Set.Ioi 0 ×ˢ Set.univ) := contDiffOn_const
      exact (hC i).smul hPconst
    have hG : ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ContinuousLinearMap.coprod
          (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
            ((∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) q.1
              (q.2 - y))
              + (∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
                (k + 2) q.1 (q.2 - y))))
          (∑ i, ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1 (q.2 - y))
              + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1)
                q.1 (q.2 - y)))
            • innerSL ℝ (EuclideanSpace.single i (1 : ℝ))))
        (Set.Ioi 0 ×ˢ Set.univ) := by
      have hfst : ContDiffOn ℝ m (fun _ : ℝ × EuclideanSpace ℝ (Fin n) =>
          ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))) (Set.Ioi 0 ×ˢ Set.univ) :=
        contDiffOn_const
      have hsnd : ContDiffOn ℝ m (fun _ : ℝ × EuclideanSpace ℝ (Fin n) =>
          ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) (Set.Ioi 0 ×ˢ Set.univ) :=
        contDiffOn_const
      have hcomp := (hA.clm_comp hfst).add (hB.clm_comp hsnd)
      refine ContDiffOn.congr hcomp (fun q _ => ?_)
      exact (ContinuousLinearMap.comp_fst_add_comp_snd _ _).symm
    refine ContDiffOn.congr hG (fun q hq => ?_)
    obtain ⟨ht, -⟩ := hq
    obtain ⟨L', hEq, hL'⟩ := hDecompThm n Q k hg_meas hg_bdd ht q.2
    change fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y)) (q.1, q.2) = _
    rw [hEq]
    have hL'eq : L' = ∑ i, ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1
        (q.2 - y))
        + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) q.1
          (q.2 - y)))
        • innerSL ℝ (EuclideanSpace.single i (1 : ℝ)) := by
      ext h
      rw [hL' h]
      have hsum : (∑ i, ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1
          (q.2 - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1)
              q.1 (q.2 - y)))
          • innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) h
          = ∑ i, ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k q.1 (q.2 - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1)
              q.1 (q.2 - y)))
            * ((innerSL ℝ (EuclideanSpace.single i (1 : ℝ))) h) := by
        simp [smul_eq_mul]
      rw [hsum]
      simp_rw [coordProj_apply]
      apply Finset.sum_congr rfl
      intro i _
      change h i * _ = _ * h i
      ring
    rw [hL'eq]

end H3Step

section H3Final

open MeasureTheory
open scoped Topology
open scoped ContDiff
open Filter


/-- Whole-space heat smoothing (C^∞): the Gaussian heat convolution of
bounded measurable data is `ContDiffOn ∞` at positive time. -/
private theorem heat_convolution_smooth_final (n : ℕ) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (hClassThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hbridge : ∀ (t : ℝ) (z : EuclideanSpace ℝ (Fin n)),
      Φ n t z = gaussPolyKernel n 1 0 t z := by
    intro t z
    simp [heatKernel, gaussPolyKernel]
  have hFG : (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2)
      = (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
        ∫ y, g y * gaussPolyKernel n 1 0 q.1 (q.2 - y)) := by
    funext p
    obtain ⟨t, x⟩ := p
    simp [heatConvolution, hbridge]
  rw [hFG]
  exact hClassThm n 1 0 hg_meas hg_bdd

end H3Final

section FinalGlueH3

open scoped ContDiff

/-- **The heat convolution is smooth at positive time.** Let `g` be a.e. strongly measurable on
`EuclideanSpace ℝ (Fin n)` with `|g y| ≤ M` for almost every `y`, for some `M`. Then
`(t, x) ↦ heatConvolution n g t x` is `ContDiffOn ℝ ∞` (`C^∞`) on
`(0, ∞) × EuclideanSpace ℝ (Fin n)`. This is `C^∞` regularity only: the theorem asserts neither
analyticity nor its failure. -/
theorem heat_convolution_smooth (n : ℕ) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hTime : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)),
      HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k s (x - y))
        (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k s (x - y)) t) t :=
    fun n Q k g h1 h2 t ht x =>
      classConv_hasDerivAt_time n Q k h1 h2 ht x gaussPolyKernel_deriv_time
        gaussPolyKernel_domination
  have hSpace : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s) - y))
        (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)) (x i) :=
    fun n Q k g h1 h2 t ht x i =>
      classConv_hasDerivAt_space_asm n Q k h1 h2 ht x i gaussPolyKernel_deriv_space
        gaussPolyKernel_domination
  have hCont : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContinuousOn (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ) :=
    fun n Q k g h1 h2 => classConv_continuousOn n Q k h1 h2
  have hJoint : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y))
          (ContinuousLinearMap.coprod
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
              (∫ y, g y * deriv (fun u => gaussPolyKernel n Q k u (x - y)) t))
            L)
          (t, x)
          ∧ ∀ h : EuclideanSpace ℝ (Fin n),
            L h = ∑ i, h i * (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k t
              (WithLp.toLp 2 (Function.update (x - y) i s))) ((x - y) i)) :=
    fun n Q k g h1 h2 t ht x =>
      classConv_hasFDerivAt_joint_asm n Q k h1 h2 hTime hSpace hCont
        gaussPolyKernel_deriv_time gaussPolyKernel_deriv_space ht x
  have hDecomp : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∃ L' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ∫ y, g y * gaussPolyKernel n Q k q.1 (q.2 - y)) (t, x)
          = ContinuousLinearMap.coprod
              (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
                ((∫ y, g y * gaussPolyKernel n (-(((n : ℝ) / 2 + (k : ℝ)) • Q)) (k + 1) t (x - y))
                  + (∫ y, g y * gaussPolyKernel n ((1 / 4 : ℝ) • (Q * ∑ i, MvPolynomial.X i ^ 2))
                    (k + 2) t (x - y))))
              L'
        ∧ ∀ h : EuclideanSpace ℝ (Fin n),
          L' h = ∑ i, h i * ((∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (x - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t (x -
              y))) :=
    fun n Q k g h1 h2 t ht x =>
      classConv_fderiv_decomp_asm n Q k h1 h2 hJoint gaussPolyKernel_deriv_time
        gaussPolyKernel_deriv_space ht x
  have hClass : ∀ (n : ℕ) (m : ℕ) (Q' : MvPolynomial (Fin n) ℝ) (k' : ℕ)
      {g' : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g' volume → (∃ M : ℝ, ∀ᵐ y, |g' y| ≤ M) →
      ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
          ∫ y, g' y * gaussPolyKernel n Q' k' q.1 (q.2 - y))
        (Set.Ioi 0 ×ˢ Set.univ) := by
    intro n
    have hall : ∀ (m : ℕ) (Q' : MvPolynomial (Fin n) ℝ) (k' : ℕ)
        {g' : EuclideanSpace ℝ (Fin n) → ℝ},
        AEStronglyMeasurable g' volume → (∃ M : ℝ, ∀ᵐ y, |g' y| ≤ M) →
        ContDiffOn ℝ m (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
            ∫ y, g' y * gaussPolyKernel n Q' k' q.1 (q.2 - y))
          (Set.Ioi 0 ×ˢ Set.univ) := by
      intro m
      induction m with
      | zero =>
        intro Q' k' g' h1 h2
        exact contDiffOn_zero.mpr (classConv_continuousOn n Q' k' h1 h2)
      | succ m ih =>
        intro Q' k' g' h1 h2
        exact classConv_contDiffOn_succ n Q' k' h1 h2 m ih hJoint hDecomp
    exact hall
  exact heat_convolution_smooth_final n hg_meas hg_bdd
    (fun n Q k g h1 h2 => contDiffOn_infty.mpr (fun m => hClass n m Q k h1 h2))


end FinalGlueH3

/-! ## H. Laplacian identification and the kernel PDE -/

section LapBridge

open MeasureTheory

private theorem hasDerivAt_line_single (n : ℕ) (i : Fin n) (y : EuclideanSpace ℝ (Fin n))
    (a : ℝ) :
    HasDerivAt (fun s : ℝ => y + (s - a) • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) a := by
  have h1 : HasDerivAt (fun s : ℝ => s - a) (1 : ℝ) a :=
    (hasDerivAt_id a).sub_const a
  have h2 := h1.smul_const (EuclideanSpace.single i (1 : ℝ))
  have h3 := HasDerivAt.const_add y h2
  simpa using h3

private theorem line_single_eq_update (n : ℕ) (i : Fin n) (y : EuclideanSpace ℝ (Fin n))
    (s : ℝ) :
    (y + (s - y.ofLp i) • EuclideanSpace.single i (1 : ℝ)) =
      WithLp.toLp 2 (Function.update y.ofLp i s) := by
  apply PiLp.ext
  intro j
  rw [PiLp.add_apply, PiLp.smul_apply]
  change y.ofLp j + (s - y.ofLp i) • (EuclideanSpace.single i (1 : ℝ)).ofLp j =
    Function.update y.ofLp i s j
  rw [PiLp.single_apply, Function.update_apply]
  by_cases h : j = i <;> simp [h]

private theorem deriv_comp_line_eq_fderiv (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : ℝ → EuclideanSpace ℝ (Fin n)) (g : ℝ → ℝ) (a : ℝ)
    (i : Fin n)
    (hc : HasDerivAt c (EuclideanSpace.single i (1 : ℝ)) a)
    (hcomp : φ ∘ c = g)
    (hd : DifferentiableAt ℝ φ (c a)) :
    deriv g a = (fderiv ℝ φ (c a)) (EuclideanSpace.single i (1 : ℝ)) := by
  have h := hd.hasFDerivAt.comp_hasDerivAt a hc
  rw [hcomp] at h
  exact h.deriv

private theorem deriv_slice_eq (n : ℕ) (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hd : ∀ y, DifferentiableAt ℝ φ y) :
    deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r))) t =
      (fderiv ℝ φ (WithLp.toLp 2 (Function.update x.ofLp i t)))
        (EuclideanSpace.single i (1 : ℝ)) := by
  have hyi : (WithLp.toLp 2 (Function.update x.ofLp i t)).ofLp i = t := by
    change Function.update x.ofLp i t i = t
    exact Function.update_self i t x.ofLp
  have hdeq : ∀ s : ℝ, ((WithLp.toLp 2 (Function.update x.ofLp i t)) +
      (s - t) • EuclideanSpace.single i (1 : ℝ)) =
      WithLp.toLp 2 (Function.update x.ofLp i s) := by
    intro s
    have hB := line_single_eq_update n i (WithLp.toLp 2 (Function.update x.ofLp i t)) s
    rw [hyi] at hB
    rw [hB]
    congr 1
    have hof : (WithLp.toLp 2 (Function.update x.ofLp i t)).ofLp =
        Function.update x.ofLp i t := rfl
    rw [hof]
    exact Function.update_idem t s x.ofLp
  have hcomp : φ ∘ (fun s : ℝ => (WithLp.toLp 2 (Function.update x.ofLp i t)) +
      (s - t) • EuclideanSpace.single i (1 : ℝ)) =
      (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r))) := by
    funext s
    change φ ((WithLp.toLp 2 (Function.update x.ofLp i t)) +
        (s - t) • EuclideanSpace.single i (1 : ℝ)) = _
    rw [hdeq s]
  have hc := hasDerivAt_line_single n i (WithLp.toLp 2 (Function.update x.ofLp i t)) t
  have h := deriv_comp_line_eq_fderiv n φ _ _ t i hc hcomp
    (hd ((fun s : ℝ => (WithLp.toLp 2 (Function.update x.ofLp i t)) +
      (s - t) • EuclideanSpace.single i (1 : ℝ)) t))
  have hpt : ((WithLp.toLp 2 (Function.update x.ofLp i t)) +
      (t - t) • EuclideanSpace.single i (1 : ℝ)) =
      WithLp.toLp 2 (Function.update x.ofLp i t) := by simp
  rw [hpt] at h
  exact h

private theorem differentiableAt_eval_fderiv (n : ℕ) (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n))
    (hd : DifferentiableAt ℝ (fderiv ℝ φ) y) :
    DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ φ y) (EuclideanSpace.single i (1 : ℝ))) y :=
  (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ))
    y)).differentiableAt

private theorem fderiv_eval_eq (n : ℕ) (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (hd : DifferentiableAt ℝ (fderiv ℝ φ) x) :
    (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ φ y) (EuclideanSpace.single i (1 : ℝ))) x)
      (EuclideanSpace.single i (1 : ℝ)) =
      ((fderiv ℝ (fderiv ℝ φ) x) (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single i (1 : ℝ)) := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ φ y) (EuclideanSpace.single i (1 : ℝ)))
      ((fderiv ℝ φ x) ∘SL 0 + (fderiv ℝ (fderiv ℝ φ) x).flip (EuclideanSpace.single i (1 : ℝ))) x :=
    hd.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)
  rw [h1.fderiv]
  simp [ContinuousLinearMap.flip_apply]

private theorem deriv2_slice_eq (n : ℕ) (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (hd : ∀ y, DifferentiableAt ℝ φ y)
    (hd2 : ∀ y, DifferentiableAt ℝ (fderiv ℝ φ) y) :
    deriv (deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r)))) (x.ofLp i) =
      ((fderiv ℝ (fderiv ℝ φ) x) (EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single i (1 : ℝ)) := by
  have hder : deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r))) =
      (fun y : EuclideanSpace ℝ (Fin n) => (fderiv ℝ φ y) (EuclideanSpace.single i (1 : ℝ))) ∘
        (fun s : ℝ => x + (s - x.ofLp i) • EuclideanSpace.single i (1 : ℝ)) := by
    funext t
    change deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r))) t =
      (fderiv ℝ φ (x + (t - x.ofLp i) • EuclideanSpace.single i (1 : ℝ)))
        (EuclideanSpace.single i (1 : ℝ))
    rw [deriv_slice_eq n i φ x t hd]
    have hline := line_single_eq_update n i x t
    rw [← hline]
  rw [hder]
  have hc := hasDerivAt_line_single n i x (x.ofLp i)
  have hψd := ((differentiableAt_eval_fderiv n i φ _ (hd2 _)).hasFDerivAt).comp_hasDerivAt
    (x.ofLp i) hc
  have hpt2 : (x + ((x.ofLp i) - x.ofLp i) • EuclideanSpace.single i (1 : ℝ)) =
      x := by simp
  rw [hpt2] at hψd
  rw [hψd.deriv]
  exact fderiv_eval_eq n i φ x (hd2 x)

private theorem deriv2_slice_eq_pinned_rhs (n : ℕ) (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r)))) (x.ofLp i) =
      deriv (fun v : ℝ => deriv (fun r : ℝ => φ (WithLp.toLp 2
        (Function.update (WithLp.toLp 2 (Function.update x.ofLp i v)) i r)))
        ((WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp i)) (x.ofLp i) := by
  congr 1
  funext v
  show deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update x.ofLp i r))) v =
    deriv (fun r : ℝ => φ (WithLp.toLp 2
      (Function.update (WithLp.toLp 2 (Function.update x.ofLp i v)) i r)))
      ((WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp i)
  congr 1
  · funext r
    show φ (WithLp.toLp 2 (Function.update x.ofLp i r)) =
      φ (WithLp.toLp 2 (Function.update (WithLp.toLp 2 (Function.update x.ofLp i v)) i r))
    congr 1
    congr 1
    change Function.update x.ofLp i r =
      Function.update (WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp i r
    have hof : (WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp =
        Function.update x.ofLp i v := rfl
    rw [hof]
    exact (Function.update_idem v r x.ofLp).symm
  · change v = Function.update x.ofLp i v i
    exact (Function.update_self i v x.ofLp).symm

/-- The Laplacian is the sum of the diagonal iterated coordinate
second partials. -/
private theorem laplacian_eq_sum_diag_secondPartial (n : ℕ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian φ x
      = ∑ i, deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) i r)))
          ((WithLp.toLp 2 (Function.update x i v)) i))
          (x i) := by
  have hd : ∀ y, DifferentiableAt ℝ φ y := by
    intro y
    exact hφ.contDiffAt.differentiableAt two_ne_zero
  have hd2 : ∀ y, DifferentiableAt ℝ (fderiv ℝ φ) y := by
    intro y
    exact (hφ.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hvi : ∀ i : Fin n, (OrthonormalBasis.ofRepr
      (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)))) i =
      EuclideanSpace.single i 1 := by
    intro i
    rw [OrthonormalBasis.coe_ofRepr]
    rfl
  have hLap := InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (OrthonormalBasis.ofRepr (LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))))
  rw [hLap]
  apply Finset.sum_congr rfl
  intro i _
  rw [hvi i]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hA := deriv2_slice_eq n i φ x hd hd2
  have hB := deriv2_slice_eq_pinned_rhs n i φ x
  rw [← hA, hB]

/-- The heat kernel satisfies the heat equation pointwise, written in coordinates: this is
`heatKernel_hasDerivAt_time_eq_laplacian` at `E = EuclideanSpace ℝ (Fin n)`, with the Laplacian
expanded by `laplacian_eq_sum_diag_secondPartial`. -/
private theorem heatKernel_pde (n : ℕ) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => (4 * Real.pi * s) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖x‖ ^ 2 / (4 * s))) t
      = ∑ i : Fin n, deriv (fun s => deriv (fun r =>
          (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖WithLp.toLp 2 (Function.update x i r)‖ ^ 2 / (4 * t))) s) (x i) := by
  have hK : ContDiff ℝ 2 (Φ n t) := by
    have hq : ContDiff ℝ 2 fun y : EuclideanSpace ℝ (Fin n) => -‖y‖ ^ 2 / (4 * t) :=
      (contDiff_norm_sq ℝ).neg.div_const _
    exact contDiff_const.mul hq.exp
  simp only [← heatKernel_euclideanSpace]
  rw [(heatKernel_hasDerivAt_time_eq_laplacian ht x).deriv,
    laplacian_eq_sum_diag_secondPartial n hK x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← deriv2_slice_eq_pinned_rhs]

end LapBridge

section LapConvH3

open MeasureTheory
open scoped ContDiff Topology


/-- Laplacian of a heat convolution = sum of diagonal iterated
coordinate second partials, from smoothness + the general
Laplacian identification. -/
private theorem laplacian_heatConvolution_via_smooth (n : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (hSmoothThm : ∀ (n : ℕ) {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.univ))
    (hLapBridgeThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x : EuclideanSpace ℝ (Fin n)),
      Laplacian.laplacian φ x
        = ∑ i, deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) i r)))
            ((WithLp.toLp 2 (Function.update x i v)) i))
            (x i)) :
    Laplacian.laplacian (fun y => heatConvolution n g t y) x
      = ∑ i, deriv (fun s => deriv (fun r => heatConvolution n g t
        (WithLp.toLp 2 (Function.update x i r))) s) (x i) := by
  have hSmooth : ContDiffOn ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ) :=
    hSmoothThm n hg_meas hg_bdd
  have hOpen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) :=
    isOpen_Ioi.prod isOpen_univ
  have hAt : ∀ y : EuclideanSpace ℝ (Fin n),
      ContDiffAt ℝ ∞ (fun y => heatConvolution n g t y) y := by
    intro y
    have hmem : (t, y) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
      Set.mk_mem_prod (Set.mem_Ioi.mpr ht) (Set.mem_univ y)
    have hnhds : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) ∈ 𝓝 (t, y) :=
      hOpen.mem_nhds hmem
    have hJ : ContDiffAt ℝ ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2) (t, y) :=
      hSmooth.contDiffAt hnhds
    have hInner : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (t, y)) y :=
      contDiffAt_const.prodMk contDiffAt_id
    have hComp : ContDiffAt ℝ ∞
        ((fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatConvolution n g p.1 p.2) ∘
          (fun y : EuclideanSpace ℝ (Fin n) => (t, y))) y :=
      hJ.comp y hInner
    exact hComp
  have hInf : ContDiff ℝ ∞ (fun y => heatConvolution n g t y) :=
    contDiff_iff_contDiffAt.mpr hAt
  have h2 : ContDiff ℝ 2 (fun y => heatConvolution n g t y) :=
    hInf.of_le (by simp)
  have hBridge := hLapBridgeThm n h2 x
  rw [hBridge]
  apply Finset.sum_congr rfl
  intro i _
  have hOuter : (fun v : ℝ => deriv
      (fun r : ℝ => heatConvolution n g t (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update x i v)) i r)))
      ((WithLp.toLp 2 (Function.update x i v)) i))
      = (fun s : ℝ => deriv
        (fun r : ℝ => heatConvolution n g t (WithLp.toLp 2 (Function.update x i r))) s) := by
    funext v
    have hPt : ((WithLp.toLp 2 (Function.update x i v)) i) = v := by
      simp only [Function.update_self]
    have hFun : (fun r : ℝ => heatConvolution n g t (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update x i v)) i r)))
        = (fun r : ℝ => heatConvolution n g t (WithLp.toLp 2 (Function.update x i r))) := by
      funext r
      congr 1
      congr 1
      simp only [Function.update_idem]
    rw [hFun, hPt]
  rw [hOuter]

end LapConvH3

section FourTerm

open MeasureTheory


private theorem normUpdate_sq (n : ℕ) (i : Fin n) (z : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2
      = ‖z‖ ^ 2 - (z i) ^ 2 + r ^ 2 := by
  have h1 : ‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2
      = ∑ j, (Function.update (fun k => z k) i r j) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    ext j
    simp [Real.norm_eq_abs, sq_abs]
  have h2 : ‖z‖ ^ 2 = ∑ j, (z j) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
    ext j
    simp [Real.norm_eq_abs, sq_abs]
  rw [h1, h2]
  have hsum : ∀ (g : Fin n → ℝ) (a : ℝ),
      (∑ x, if x = i then a else g x) = (∑ x, g x) - g i + a := by
    intro g a
    have hh1 : (∑ x, if x = i then a else g x)
        = a + ∑ x ∈ Finset.univ.erase i, g x := by
      have h := Finset.add_sum_erase Finset.univ (fun x => if x = i then a else g x)
        (Finset.mem_univ i)
      simp only [ite_true] at h
      have hcongr : ∑ x ∈ Finset.univ.erase i, (if x = i then a else g x)
          = ∑ x ∈ Finset.univ.erase i, g x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp at hx
        simp [hx]
      rw [hcongr] at h
      linarith
    have hh2 : (∑ x, g x) = g i + ∑ x ∈ Finset.univ.erase i, g x := by
      have h := Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)
      linarith
    linarith
  have heq : ∀ j, (Function.update (fun k => z k) i r j) ^ 2
      = (if j = i then r ^ 2 else (z j) ^ 2) := by
    intro j
    by_cases hji : j = i
    · simp [hji, Function.update]
    · simp [hji, Function.update]
  simp_rw [heq]
  exact hsum (fun j => (z j) ^ 2) (r ^ 2)

private theorem firstDeriv_gauss {t : ℝ} (ht : 0 < t) (C A : ℝ) (s : ℝ) :
    deriv (fun r : ℝ => C * Real.exp (-(A + r ^ 2) / (4 * t))) s
      = C * (Real.exp (-(A + s ^ 2) / (4 * t)) * (-s / (2 * t))) := by
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    have h := hasDerivAt_pow 2 (s : ℝ)
    simpa using h
  have hadd : HasDerivAt (fun r : ℝ => A + r ^ 2) (0 + 2 * s) s :=
    (hasDerivAt_const s A).add h2
  have hneg := hadd.neg
  have hdiv := hneg.div_const (4 * t)
  have hder : (-(0 + 2 * s)) / (4 * t) = -s / (2 * t) := by
    field_simp
    ring
  rw [hder] at hdiv
  have hexp := hdiv.exp
  have hmul := hexp.const_mul C
  exact hmul.deriv

private theorem secondDeriv_gauss {t : ℝ} (ht : 0 < t) (C A : ℝ) (p : ℝ) :
    deriv (fun s : ℝ => C * (Real.exp (-(A + s ^ 2) / (4 * t)) * (-s / (2 * t)))) p
      = C * (Real.exp (-(A + p ^ 2) / (4 * t)) * (p ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) := by
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * p) p := by
    have h := hasDerivAt_pow 2 (p : ℝ)
    simpa using h
  have hadd : HasDerivAt (fun r : ℝ => A + r ^ 2) (0 + 2 * p) p :=
    (hasDerivAt_const p A).add h2
  have hneg : HasDerivAt (fun r : ℝ => -(A + r ^ 2)) (-(0 + 2 * p)) p :=
    hadd.neg
  have hdiv : HasDerivAt (fun r : ℝ => -(A + r ^ 2) / (4 * t)) ((-(0 + 2 * p)) / (4 * t)) p :=
    hneg.div_const (4 * t)
  have hder : (-(0 + 2 * p)) / (4 * t) = -p / (2 * t) := by
    field_simp
    ring
  rw [hder] at hdiv
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-(A + r ^ 2) / (4 * t)))
      (Real.exp (-(A + p ^ 2) / (4 * t)) * (-p / (2 * t))) p :=
    hdiv.exp
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) p := hasDerivAt_id' p
  have hneg2 : HasDerivAt (fun s : ℝ => -s) (-(1 : ℝ)) p := hid.neg
  have hv : HasDerivAt (fun s : ℝ => -s / (2 * t)) ((-(1 : ℝ)) / (2 * t)) p :=
    hneg2.div_const (2 * t)
  have hder2 : ((-(1 : ℝ)) / (2 * t)) = -1 / (2 * t) := by ring
  rw [hder2] at hv
  have huv : HasDerivAt (fun s : ℝ => Real.exp (-(A + s ^ 2) / (4 * t)) * (-s / (2 * t)))
      ((Real.exp (-(A + p ^ 2) / (4 * t)) * (-p / (2 * t))) * (-p / (2 * t))
        + Real.exp (-(A + p ^ 2) / (4 * t)) * (-1 / (2 * t))) p :=
    hexp.mul hv
  have hmul : HasDerivAt (fun s : ℝ => C * (Real.exp (-(A + s ^ 2) / (4 * t)) * (-s / (2 * t))))
      (C * ((Real.exp (-(A + p ^ 2) / (4 * t)) * (-p / (2 * t))) * (-p / (2 * t))
        + Real.exp (-(A + p ^ 2) / (4 * t)) * (-1 / (2 * t)))) p :=
    huv.const_mul C
  have hderiv := hmul.deriv
  rw [hderiv]
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp
  ring

/-- Four-term kernel sum equals the iterated coordinate derivative
of the plain heat kernel. -/
private theorem fourTermKernel_eq_iteratedDeriv (n : ℕ) (i : Fin n) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) :
    (gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t z
      + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1)) 1 t z
      + gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))) 1 t z
      + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i *
        1)))) 2 t z)
      = deriv (fun s => deriv (fun r =>
          (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2 / (4 * t))) s) (z i) := by
  have e1 : MvPolynomial.eval (fun j => z j)
      (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) = 0 := by simp
  have e2 : MvPolynomial.eval (fun j => z j)
      ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1)) = 0 := by simp
  have e3 : MvPolynomial.eval (fun j => z j)
      (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))) = -1/2 := by simp
  have e4 : MvPolynomial.eval (fun j => z j)
      ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))))
      = (1/4) * (z i)^2 := by simp; ring
  have hLHS : (gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t z
      + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1)) 1 t z
      + gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))) 1 t z
      + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i *
        1)))) 2 t z)
      = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * t))
        * ((-1/2) * (1/t) + (1/4) * (z i)^2 * (1/t^2)) := by
    simp only [gaussPolyKernel, e1, e2, e3, e4]
    simp
    ring
  have hfun_inner : (fun r : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2 / (4 * t)))
      = (fun r : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-((‖z‖ ^ 2 - (z i) ^ 2) + r ^ 2) / (4 * t))) := by
    funext r
    have hnorm := normUpdate_sq n i z r
    rw [hnorm]
  have hfirst : ∀ s : ℝ, deriv (fun r : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2 / (4 * t))) s
      = (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * (Real.exp (-((‖z‖ ^ 2 - (z i) ^ 2) + s ^ 2) / (4 * t)) * (-s / (2 * t))) := by
    intro s
    rw [hfun_inner]
    exact firstDeriv_gauss ht _ _ s
  have hfun_outer : (fun s : ℝ => deriv (fun r : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2 / (4 * t))) s)
      = (fun s : ℝ => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * (Real.exp (-((‖z‖ ^ 2 - (z i) ^ 2) + s ^ 2) / (4 * t)) * (-s / (2 * t)))) := by
    funext s
    exact hfirst s
  have hsecond := secondDeriv_gauss ht ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))
    ((‖z‖ ^ 2 - (z i) ^ 2)) (z i)
  rw [hLHS, hfun_outer, hsecond]
  have hA : ((‖z‖ ^ 2 - (z i) ^ 2)) + (z i) ^ 2 = ‖z‖ ^ 2 := by ring
  rw [hA]
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp
  ring

end FourTerm

section IntBdd

open MeasureTheory

/-- Polynomial growth bound for `MvPolynomial.eval` on Euclidean space. -/
private theorem gaussPoly_polyBound (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, ∃ D : ℕ, 0 ≤ C ∧
      ∀ z : EuclideanSpace ℝ (Fin n),
        |MvPolynomial.eval (fun i => z i) Q| ≤ C * (1 + ‖z‖) ^ D := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨|a|, 0, abs_nonneg a, fun z => ?_⟩
    rw [MvPolynomial.eval_C, pow_zero, mul_one]
  | add p q hp hq =>
    obtain ⟨Cp, Dp, hCp, hp⟩ := hp
    obtain ⟨Cq, Dq, hCq, hq⟩ := hq
    refine ⟨Cp + Cq, max Dp Dq, add_nonneg hCp hCq, fun z => ?_⟩
    rw [MvPolynomial.eval_add]
    have h1 : (1 : ℝ) ≤ 1 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hp' : Cp * (1 + ‖z‖) ^ Dp ≤ Cp * (1 + ‖z‖) ^ max Dp Dq :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (Nat.le_max_left _ _)) hCp
    have hq' : Cq * (1 + ‖z‖) ^ Dq ≤ Cq * (1 + ‖z‖) ^ max Dp Dq :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (Nat.le_max_right _ _)) hCq
    calc |MvPolynomial.eval (fun i => z i) p + MvPolynomial.eval (fun i => z i) q|
        ≤ |MvPolynomial.eval (fun i => z i) p| + |MvPolynomial.eval (fun i => z i) q| :=
          abs_add_le _ _
      _ ≤ Cp * (1 + ‖z‖) ^ Dp + Cq * (1 + ‖z‖) ^ Dq := add_le_add (hp z) (hq z)
      _ ≤ Cp * (1 + ‖z‖) ^ max Dp Dq + Cq * (1 + ‖z‖) ^ max Dp Dq :=
          add_le_add hp' hq'
      _ = (Cp + Cq) * (1 + ‖z‖) ^ max Dp Dq := by ring
  | mul_X p i hp =>
    obtain ⟨Cp, Dp, hCp, hp⟩ := hp
    refine ⟨Cp, Dp + 1, hCp, fun z => ?_⟩
    have hcoord : |z i| ≤ 1 + ‖z‖ := by
      have h1 : ‖z i‖ ≤ ‖z‖ := PiLp.norm_apply_le z i
      rw [Real.norm_eq_abs] at h1
      exact h1.trans (le_add_of_nonneg_left zero_le_one)
    have hnn : (0 : ℝ) ≤ Cp * (1 + ‖z‖) ^ Dp :=
      mul_nonneg hCp (pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) _)
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    calc |MvPolynomial.eval (fun i => z i) p * z i|
        = |MvPolynomial.eval (fun i => z i) p| * |z i| := abs_mul _ _
      _ ≤ Cp * (1 + ‖z‖) ^ Dp * (1 + ‖z‖) := mul_le_mul (hp z) hcoord (abs_nonneg _) hnn
      _ = Cp * (1 + ‖z‖) ^ (Dp + 1) := by rw [pow_succ]; ring

/-- Polynomial growth is dominated by Gaussian growth. -/
private theorem gaussPoly_polyExpBound (D : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ r : ℝ, 0 ≤ r → (1 + r) ^ D ≤ C * Real.exp (r ^ 2 / (8 * t)) := by
  have ht8 : (0 : ℝ) < 8 * t := by linarith
  have ht8' : (0 : ℝ) ≤ 8 * t := le_of_lt ht8
  have hCnn : (0 : ℝ) ≤ 2 ^ D * (2 + (8 * t) ^ D * D.factorial) := by
    have h1 : (0 : ℝ) ≤ (8 * t) ^ D := pow_nonneg ht8' D
    have h2 : (0 : ℝ) ≤ (D.factorial : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (8 * t) ^ D * D.factorial := mul_nonneg h1 h2
    have h4 : (0 : ℝ) ≤ 2 + (8 * t) ^ D * D.factorial := by linarith [h3]
    exact mul_nonneg (pow_nonneg zero_le_two D) h4
  refine ⟨2 ^ D * (2 + (8 * t) ^ D * D.factorial), hCnn, fun r hr => ?_⟩
  have h2nn : (0 : ℝ) ≤ 2 ^ D := pow_nonneg zero_le_two D
  have h8nn : (0 : ℝ) ≤ (8 * t) ^ D := pow_nonneg ht8' D
  set s : ℝ := r ^ 2 / (8 * t) with hs
  have hsnn : 0 ≤ s := div_nonneg (sq_nonneg r) ht8'
  have hexp1 : (1 : ℝ) ≤ Real.exp s := Real.one_le_exp hsnn
  have hfact : s ^ D ≤ D.factorial * Real.exp s := by
    have h := Real.pow_div_factorial_le_exp s hsnn D
    have hF : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
    rw [div_le_iff₀ hF] at h
    rwa [mul_comm]
  have hr2 : r ^ (2 * D) = (8 * t) ^ D * s ^ D := by
    have h8t : (8 : ℝ) * t ≠ 0 := ne_of_gt ht8
    have hbase : r ^ 2 = 8 * t * s := by
      rw [hs, mul_comm (8 * t) _, div_mul_cancel₀ _ h8t]
    calc r ^ (2 * D) = (r ^ 2) ^ D := by rw [pow_mul]
      _ = (8 * t * s) ^ D := by rw [hbase]
      _ = (8 * t) ^ D * s ^ D := mul_pow _ _ _
  have hpow : r ^ D ≤ 1 + r ^ (2 * D) := by
    have h : r ^ D ≤ 1 + (r ^ D) ^ 2 := by nlinarith [sq_nonneg (r ^ D - 1 / 2)]
    have hsq2 : (r ^ D) ^ 2 = r ^ (2 * D) := by rw [← pow_mul, mul_comm D 2]
    rwa [hsq2] at h
  have hsplit : (1 + r) ^ D ≤ 2 ^ D * (1 + r ^ D) := by
    rcases le_total r 1 with hr1 | hr1
    · have hbase : (1 : ℝ) + r ≤ 2 := by linarith
      have hnn : (0 : ℝ) ≤ 1 + r := by linarith [hr]
      calc (1 + r) ^ D ≤ 2 ^ D := pow_le_pow_left₀ hnn hbase D
        _ ≤ 2 ^ D * (1 + r ^ D) :=
            le_mul_of_one_le_right (pow_nonneg zero_le_two D)
              (le_add_of_nonneg_right (pow_nonneg hr D))
    · have hbase : (1 : ℝ) + r ≤ 2 * r := by linarith
      have hnn : (0 : ℝ) ≤ 1 + r := by linarith [hr]
      calc (1 + r) ^ D ≤ (2 * r) ^ D := pow_le_pow_left₀ hnn hbase D
        _ = 2 ^ D * r ^ D := mul_pow _ _ _
        _ ≤ 2 ^ D * (1 + r ^ D) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
              (pow_nonneg zero_le_two D)
  have step1 : 2 ^ D * (1 + r ^ D) ≤ 2 ^ D * (1 + (1 + r ^ (2 * D))) :=
    mul_le_mul_of_nonneg_left (add_le_add_right hpow 1) h2nn
  have step2 : 2 ^ D * (2 + (8 * t) ^ D * s ^ D)
      ≤ 2 ^ D * (2 + (8 * t) ^ D * (D.factorial * Real.exp s)) :=
    mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hfact h8nn) 2) h2nn
  have step3 : 2 ^ D * (2 + (8 * t) ^ D * (D.factorial * Real.exp s))
      ≤ 2 ^ D * (2 + (8 * t) ^ D * D.factorial) * Real.exp s := by
    have h2 : 2 + (8 * t) ^ D * (D.factorial * Real.exp s)
        ≤ (2 + (8 * t) ^ D * D.factorial) * Real.exp s := by
      linarith [hexp1]
    calc 2 ^ D * (2 + (8 * t) ^ D * (D.factorial * Real.exp s))
        ≤ 2 ^ D * ((2 + (8 * t) ^ D * D.factorial) * Real.exp s) :=
          mul_le_mul_of_nonneg_left h2 h2nn
      _ = 2 ^ D * (2 + (8 * t) ^ D * D.factorial) * Real.exp s := by ring
  calc (1 + r) ^ D ≤ 2 ^ D * (1 + r ^ D) := hsplit
    _ ≤ 2 ^ D * (1 + (1 + r ^ (2 * D))) := step1
    _ = 2 ^ D * (2 + (8 * t) ^ D * s ^ D) := by rw [hr2]; ring
    _ ≤ 2 ^ D * (2 + (8 * t) ^ D * (D.factorial * Real.exp s)) := step2
    _ ≤ 2 ^ D * (2 + (8 * t) ^ D * D.factorial) * Real.exp s := step3

/-- Unshifted Gaussians are integrable on Euclidean space. -/
private theorem gaussPoly_integrable_gauss (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2 / (16 * t))) volume := by
  refine (integrable_real_exp_neg_mul_sq_norm (Fin n) (b := 1 / (16 * t)) (by positivity)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  change Real.exp (-(1 / (16 * t)) * ‖y‖ ^ 2) = Real.exp (-‖y‖ ^ 2 / (16 * t))
  congr 1
  ring


/-- A bounded a.e. measurable weight times a Gaussian-polynomial kernel is
integrable: Gaussian decay dominates polynomial growth and the bounded
measurable factor. -/
private theorem integrable_bddMul_gaussPolyKernel (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => g y * gaussPolyKernel n Q k t (x - y)) volume := by
  obtain ⟨M, hM⟩ := hg_bdd
  obtain ⟨Cp, Dp, hCp, hpoly⟩ := gaussPoly_polyBound n Q
  obtain ⟨Ce, hCe, hexp⟩ := gaussPoly_polyExpBound Dp ht
  have ht4 : (0 : ℝ) < 4 * t := by linarith
  have hC0 : (0 : ℝ) < (4 * Real.pi * t) ^ (-(n : ℝ) / 2) := by
    apply Real.rpow_pos_of_pos
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hT : (0 : ℝ) < t ^ (-(k : ℤ)) := zpow_pos ht _
  set Ctot : ℝ := |M| * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
    * (t ^ (-(k : ℤ)) * (Cp * (Ce * Real.exp (‖x‖ ^ 2 / (8 * t)))))) with hCtot
  have hCtotnn : 0 ≤ Ctot := by
    rw [hCtot]
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (le_of_lt hC0)
        (mul_nonneg (le_of_lt hT)
          (mul_nonneg hCp (mul_nonneg hCe (Real.exp_nonneg _)))))
  have hdom : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => Ctot * Real.exp (-‖y‖ ^ 2 / (16 * t))) volume :=
    (gaussPoly_integrable_gauss n ht).const_mul Ctot
  have hKmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (x - y)) volume := by
    apply Continuous.aestronglyMeasurable
    have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) :=
      continuous_const.sub continuous_id
    have hnorm2 : Continuous (fun y : EuclideanSpace ℝ (Fin n) => -‖x - y‖ ^ 2 / (4 * t)) := by
      apply Continuous.div _ continuous_const (fun _ => ne_of_gt ht4)
      exact ((continuous_norm.comp hsub).pow 2).neg
    have hexpc : Continuous
        (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x - y‖ ^ 2 / (4 * t))) :=
      Real.continuous_exp.comp hnorm2
    have hcoord : ∀ i : Fin n, Continuous (fun z : EuclideanSpace ℝ (Fin n) => z i) :=
      fun i => PiLp.continuous_apply 2 _ i
    have hpoly_cts : Continuous
        (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => (x - y) i) Q) :=
      (MvPolynomial.continuous_eval Q).comp (continuous_pi (fun i => (hcoord i).comp hsub))
    unfold gaussPolyKernel
    exact ((continuous_const.mul hexpc).mul hpoly_cts).mul continuous_const
  have hFmeas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => g y * gaussPolyKernel n Q k t (x - y)) volume :=
    hg_meas.mul hKmeas
  refine Integrable.mono' hdom hFmeas ?_
  have hM' : ∀ᵐ y : EuclideanSpace ℝ (Fin n), |g y| ≤ |M| :=
    hM.mono fun y hy => hy.trans (le_abs_self M)
  filter_upwards [hM'] with y hy
  change ‖g y * gaussPolyKernel n Q k t (x - y)‖ ≤ Ctot * Real.exp (-‖y‖ ^ 2 / (16 * t))
  have hKabs : |gaussPolyKernel n Q k t (x - y)|
      = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / (4 * t))
        * |MvPolynomial.eval (fun i => (x - y) i) Q| * t ^ (-(k : ℤ)) := by
    unfold gaussPolyKernel
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (le_of_lt hC0),
      abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (le_of_lt hT)]
  have hpoly_y := hpoly (x - y)
  have hexp_y := hexp ‖x - y‖ (norm_nonneg _)
  have hexp_split : Real.exp (-‖x - y‖ ^ 2 / (4 * t))
      = Real.exp (-‖x - y‖ ^ 2 / (8 * t)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) := by
    have h : (-‖x - y‖ ^ 2 / (4 * t) : ℝ) = -‖x - y‖ ^ 2 / (8 * t) + -‖x - y‖ ^ 2 / (8 * t) := by
      ring
    rw [h, Real.exp_add]
  have hcancel : Real.exp (‖x - y‖ ^ 2 / (8 * t)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) = 1 := by
    rw [← Real.exp_add]
    have h : (‖x - y‖ ^ 2 / (8 * t) : ℝ) + -‖x - y‖ ^ 2 / (8 * t) = 0 := by ring
    rw [h, Real.exp_zero]
  have hnorm_ineq : ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have h := norm_add_le x (y - x)
      rw [add_sub_cancel] at h
      rwa [norm_sub_rev y x] at h
    have hsq := pow_le_pow_left₀ (norm_nonneg y) htri 2
    have h2sq : (‖x‖ + ‖x - y‖) ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - ‖x - y‖)]
    exact hsq.trans h2sq
  have heq : (2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2) / (16 * t)
      = ‖x‖ ^ 2 / (8 * t) + ‖x - y‖ ^ 2 / (8 * t) := by
    have e1 : (16 : ℝ) * t = 2 * ((8 : ℝ) * t) := by ring
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [e1, add_div, mul_div_mul_left _ _ h2, mul_div_mul_left _ _ h2]
  have hdiv : ‖y‖ ^ 2 / (16 * t) ≤ ‖x‖ ^ 2 / (8 * t) + ‖x - y‖ ^ 2 / (8 * t) := by
    have ht16 : (0 : ℝ) < 16 * t := by linarith
    have h2 : ‖y‖ ^ 2 / (16 * t) ≤ (2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2) / (16 * t) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnorm_ineq (inv_nonneg.mpr (le_of_lt ht16))
    rwa [heq] at h2
  have hshift : Real.exp (-‖x - y‖ ^ 2 / (8 * t))
      ≤ Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by
    have hexp_ineq : (-‖x - y‖ ^ 2 / (8 * t) : ℝ) ≤ ‖x‖ ^ 2 / (8 * t) + -‖y‖ ^ 2 / (16 * t) := by
      have h1 : (-‖x - y‖ ^ 2 / (8 * t) : ℝ) = -(‖x - y‖ ^ 2 / (8 * t)) := by ring
      have h2 : (-‖y‖ ^ 2 / (16 * t) : ℝ) = -(‖y‖ ^ 2 / (16 * t)) := by ring
      rw [h1, h2]
      linarith [hdiv]
    calc Real.exp (-‖x - y‖ ^ 2 / (8 * t))
        ≤ Real.exp (‖x‖ ^ 2 / (8 * t) + -‖y‖ ^ 2 / (16 * t)) :=
          Real.exp_le_exp.mpr hexp_ineq
      _ = Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)) :=
          Real.exp_add _ _
  have hK : |gaussPolyKernel n Q k t (x - y)|
      ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * ((t ^ (-(k : ℤ)))
          * (Cp * (Ce * (Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)))))) := by
    rw [hKabs, hexp_split]
    have e1 : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (Real.exp (-‖x - y‖ ^ 2 / (8 * t))
          * Real.exp (-‖x - y‖ ^ 2 / (8 * t))) * |MvPolynomial.eval (fun i => (x - y) i) Q|
          * t ^ (-(k : ℤ))
        ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (Real.exp (-‖x - y‖ ^ 2 / (8 * t))
          * Real.exp (-‖x - y‖ ^ 2 / (8 * t))) * (Cp * (1 + ‖x - y‖) ^ Dp)
          * t ^ (-(k : ℤ)) := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hT)
      apply mul_le_mul_of_nonneg_left _ _
      · exact hpoly_y
      · positivity
    calc (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (Real.exp (-‖x - y‖ ^ 2 / (8 * t))
            * Real.exp (-‖x - y‖ ^ 2 / (8 * t))) * |MvPolynomial.eval (fun i => (x - y) i) Q|
            * t ^ (-(k : ℤ))
        ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (Real.exp (-‖x - y‖ ^ 2 / (8 * t))
            * Real.exp (-‖x - y‖ ^ 2 / (8 * t))) * (Cp * (1 + ‖x - y‖) ^ Dp)
            * t ^ (-(k : ℤ)) := e1
      _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * t ^ (-(k : ℤ))
          * (Cp * ((1 + ‖x - y‖) ^ Dp * (Real.exp (-‖x - y‖ ^ 2 / (8 * t))
            * Real.exp (-‖x - y‖ ^ 2 / (8 * t))))) := by ring
      _ ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * t ^ (-(k : ℤ))
          * (Cp * ((Ce * Real.exp (‖x - y‖ ^ 2 / (8 * t)))
            * (Real.exp (-‖x - y‖ ^ 2 / (8 * t)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t))))) := by
          gcongr
      _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * t ^ (-(k : ℤ))
          * (Cp * (Ce * Real.exp (-‖x - y‖ ^ 2 / (8 * t)))) := by
          have hcc : (Ce * Real.exp (‖x - y‖ ^ 2 / (8 * t)))
              * (Real.exp (-‖x - y‖ ^ 2 / (8 * t)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t)))
              = Ce * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) := by
            calc (Ce * Real.exp (‖x - y‖ ^ 2 / (8 * t)))
                  * (Real.exp (-‖x - y‖ ^ 2 / (8 * t)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t)))
                = Ce * (Real.exp (‖x - y‖ ^ 2 / (8 * t)) * Real.exp (-‖x - y‖ ^ 2 / (8 * t)))
                  * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) := by ring
              _ = Ce * 1 * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) := by rw [hcancel]
              _ = Ce * Real.exp (-‖x - y‖ ^ 2 / (8 * t)) := by ring
          rw [hcc]
      _ ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * t ^ (-(k : ℤ))
          * (Cp * (Ce * (Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t))))) := by
          gcongr
      _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * ((t ^ (-(k : ℤ)))
            * (Cp * (Ce * (Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t)))))) := by
          ring
  rw [Real.norm_eq_abs, abs_mul]
  calc |g y| * |gaussPolyKernel n Q k t (x - y)|
      ≤ |M| * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * ((t ^ (-(k : ℤ)))
          * (Cp * (Ce * (Real.exp (‖x‖ ^ 2 / (8 * t)) * Real.exp (-‖y‖ ^ 2 / (16 * t))))))) :=
        mul_le_mul hy hK (abs_nonneg _) (abs_nonneg _)
    _ = Ctot * Real.exp (-‖y‖ ^ 2 / (16 * t)) := by rw [hCtot]; ring

end IntBdd

section SecondRep

open MeasureTheory
open scoped Topology


/-- A coordinate is bounded by the Euclidean norm. -/
private lemma coord_le_norm_aux (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    |z j| ≤ ‖z‖ := by
  have h : (z j) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ j)
  calc |z j| = √((z j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ √(‖z‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

/-- MvPolynomial evaluation is bounded by a constant times `(1 + ‖z‖)^D`. -/
private lemma mvpoly_eval_bound_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    ∃ C : ℝ, ∃ D : ℕ, 0 ≤ C ∧
      ∀ z : EuclideanSpace ℝ (Fin n), |MvPolynomial.eval (fun i => z i) Q| ≤ C * (1 + ‖z‖) ^ D := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨|a|, 0, abs_nonneg _, fun z => ?_⟩
    simp [MvPolynomial.eval_C]
  | add P Q ihP ihQ =>
    obtain ⟨C1, D1, hC1, h1⟩ := ihP
    obtain ⟨C2, D2, hC2, h2⟩ := ihQ
    refine ⟨C1 + C2, max D1 D2, by positivity, fun z => ?_⟩
    have hP := h1 z
    have hQ := h2 z
    have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by
      have : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      linarith
    have e1 : C1 * (1 + ‖z‖) ^ D1 ≤ C1 * (1 + ‖z‖) ^ (max D1 D2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_left D1 D2)) hC1
    have e2 : C2 * (1 + ‖z‖) ^ D2 ≤ C2 * (1 + ‖z‖) ^ (max D1 D2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_right D1 D2)) hC2
    calc |MvPolynomial.eval (fun i => z i) (P + Q)|
        = |MvPolynomial.eval (fun i => z i) P + MvPolynomial.eval (fun i => z i) Q| := by
          rw [MvPolynomial.eval_add]
      _ ≤ |MvPolynomial.eval (fun i => z i) P| + |MvPolynomial.eval (fun i => z i) Q| := abs_add_le
        _ _
      _ ≤ C1 * (1 + ‖z‖) ^ D1 + C2 * (1 + ‖z‖) ^ D2 := add_le_add hP hQ
      _ ≤ C1 * (1 + ‖z‖) ^ (max D1 D2) + C2 * (1 + ‖z‖) ^ (max D1 D2) := add_le_add e1 e2
      _ = (C1 + C2) * (1 + ‖z‖) ^ (max D1 D2) := by ring
  | mul_X P j ihP =>
    obtain ⟨C1, D1, hC1, h1⟩ := ihP
    refine ⟨C1, D1 + 1, hC1, fun z => ?_⟩
    have hP := h1 z
    have hcoord : |z j| ≤ 1 + ‖z‖ := by
      have h := coord_le_norm_aux n z j
      have hn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      linarith
    have hmul : |MvPolynomial.eval (fun i => z i) P * z j|
        ≤ (C1 * (1 + ‖z‖) ^ D1) * (1 + ‖z‖) := by
      rw [abs_mul]
      exact mul_le_mul hP hcoord (by positivity) (by positivity)
    calc |MvPolynomial.eval (fun i => z i) (P * MvPolynomial.X j)|
        = |MvPolynomial.eval (fun i => z i) P * z j| := by
          rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      _ ≤ (C1 * (1 + ‖z‖) ^ D1) * (1 + ‖z‖) := hmul
      _ = C1 * (1 + ‖z‖) ^ (D1 + 1) := by rw [pow_add, pow_one]; ring

/-- Gaussian shift bound: moving the center by a bounded amount costs a constant factor
and halves the decay rate. -/
private lemma gauss_shift_bound_aux (n : ℕ) (R t : ℝ) (_hR : 0 ≤ R) (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ ≤ R) (y : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-‖w - y‖ ^ 2 / (4 * t))
      ≤ Real.exp (R ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t)) := by
  have htri : ‖y‖ ≤ ‖y - w‖ + ‖w‖ := by
    have h := norm_add_le (y - w) w
    have heq : (y - w) + w = y := by abel
    rw [heq] at h
    exact h
  have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hw 2
  have hsq1 : ‖y‖ ^ 2 ≤ (‖y - w‖ + ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg y) htri 2
  have hsq2 : (‖y - w‖ + ‖w‖) ^ 2 ≤ 2 * ‖y - w‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖y - w‖ - ‖w‖)]
  have hrev : ‖y - w‖ = ‖w - y‖ := norm_sub_rev y w
  have h1 : ‖y‖ ^ 2 ≤ 2 * ‖w - y‖ ^ 2 + 2 * R ^ 2 := by
    rw [← hrev]
    linarith [hsq1, hsq2, hw2]
  have h4t : (4 : ℝ) * t ≠ 0 := by positivity
  have h8t : (8 : ℝ) * t ≠ 0 := by positivity
  have h8pos : (0 : ℝ) < 8 * t := by positivity
  have e1 : -‖w - y‖ ^ 2 / (4 * t) = (-2 * ‖w - y‖ ^ 2) / (8 * t) := by
    field_simp [h4t, h8t]
    ring
  have e2 : R ^ 2 / (4 * t) + (-‖y‖ ^ 2 / (8 * t)) = (2 * R ^ 2 - ‖y‖ ^ 2) / (8 * t) := by
    field_simp [h4t, h8t]
    ring
  have hexp : -‖w - y‖ ^ 2 / (4 * t) ≤ R ^ 2 / (4 * t) + (-‖y‖ ^ 2 / (8 * t)) := by
    rw [e1, e2, div_le_div_iff_of_pos_right h8pos]
    linarith [h1]
  calc Real.exp (-‖w - y‖ ^ 2 / (4 * t))
      ≤ Real.exp (R ^ 2 / (4 * t) + (-‖y‖ ^ 2 / (8 * t))) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (R ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t)) := Real.exp_add _ _

/-- A class-member kernel at a shifted point is bounded by a constant times a
polynomial-Gaussian bound in `y`, uniformly for `w` in a ball of radius `R`. -/
private lemma gaussPolyKernel_le_bound_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (t R : ℝ) (ht : 0 < t) (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ D : ℕ, 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ (Fin n), ∀ y : EuclideanSpace ℝ (Fin n),
      ‖w‖ ≤ R → |gaussPolyKernel n Q k t (w - y)|
        ≤ C * ((1 + ‖y‖) ^ D * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by
  obtain ⟨CQ, DQ, hCQ, hQ⟩ := mvpoly_eval_bound_aux n Q
  have hA1pos : (0 : ℝ) < (4 * Real.pi * t) ^ (-(n : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hA2pos : (0 : ℝ) < t ^ (-(k : ℤ)) := zpow_pos ht _
  refine ⟨(4 * Real.pi * t) ^ (-(n : ℝ) / 2) * t ^ (-(k : ℤ)) * CQ * (1 + R) ^ DQ
    * Real.exp (R ^ 2 / (4 * t)), DQ, ?_, fun w y hw => ?_⟩
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg hA1pos.le hA2pos.le
        · exact hCQ
      · apply pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + R)
    · exact (Real.exp_pos _).le
  · have hwy : ‖w - y‖ ≤ R + ‖y‖ := by
      calc ‖w - y‖ ≤ ‖w‖ + ‖y‖ := norm_sub_le w y
        _ ≤ R + ‖y‖ := by linarith [hw]
    have hexpand : (1 + R) * (1 + ‖y‖) = 1 + (R + ‖y‖) + R * ‖y‖ := by ring
    have hRy : (0 : ℝ) ≤ R * ‖y‖ := mul_nonneg hR (norm_nonneg y)
    have hbase : 1 + ‖w - y‖ ≤ (1 + R) * (1 + ‖y‖) := by
      rw [hexpand]
      linarith [hwy, hRy]
    have hPle : |MvPolynomial.eval (fun i => (w - y) i) Q|
        ≤ CQ * (1 + R) ^ DQ * (1 + ‖y‖) ^ DQ := by
      calc |MvPolynomial.eval (fun i => (w - y) i) Q|
          ≤ CQ * (1 + ‖w - y‖) ^ DQ := hQ (w - y)
        _ ≤ CQ * ((1 + R) * (1 + ‖y‖)) ^ DQ := by
            apply mul_le_mul_of_nonneg_left _ hCQ
            exact pow_le_pow_left₀ (by positivity) hbase DQ
        _ = CQ * (1 + R) ^ DQ * (1 + ‖y‖) ^ DQ := by
            rw [mul_pow]
            ring
    have hEle := gauss_shift_bound_aux n R t hR ht w hw y
    have hu1 : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖w - y‖ ^ 2 / (4 * t))
        ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * (Real.exp (R ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_left hEle hA1pos.le
    have hu2 : |MvPolynomial.eval (fun i => (w - y) i) Q| * t ^ (-(k : ℤ))
        ≤ (CQ * (1 + R) ^ DQ * (1 + ‖y‖) ^ DQ) * t ^ (-(k : ℤ)) :=
      mul_le_mul_of_nonneg_right hPle hA2pos.le
    have hC0 : (0 : ℝ) ≤ |MvPolynomial.eval (fun i => (w - y) i) Q| * t ^ (-(k : ℤ)) :=
      mul_nonneg (abs_nonneg _) hA2pos.le
    have hU1 : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * (Real.exp (R ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t))) :=
      mul_nonneg hA1pos.le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    have hfin := mul_le_mul hu1 hu2 hC0 hU1
    have habs : |gaussPolyKernel n Q k t (w - y)|
        = ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖w - y‖ ^ 2 / (4 * t)))
          * (|MvPolynomial.eval (fun i => (w - y) i) Q| * t ^ (-(k : ℤ))) := by
      unfold gaussPolyKernel
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hA1pos.le,
        abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hA2pos.le]
      ring
    rw [habs]
    calc ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖w - y‖ ^ 2 / (4 * t)))
          * (|MvPolynomial.eval (fun i => (w - y) i) Q| * t ^ (-(k : ℤ)))
        ≤ ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (Real.exp (R ^ 2 / (4 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t))))
          * ((CQ * (1 + R) ^ DQ * (1 + ‖y‖) ^ DQ) * t ^ (-(k : ℤ))) := hfin
      _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * t ^ (-(k : ℤ)) * CQ * (1 + R) ^ DQ
          * Real.exp (R ^ 2 / (4 * t)) * ((1 + ‖y‖) ^ DQ * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by
          ring

/-- Coordinates of an updated point, at the updated index. -/
private lemma toLp_update_same_aux (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (r : ℝ) :
    (WithLp.toLp 2 (Function.update x i r)) i = r := by
  change Function.update x i r i = r
  simp

/-- Coordinates of an updated point, away from the updated index. -/
private lemma toLp_update_of_ne_aux (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) (r : ℝ)
    (h : j ≠ i) : (WithLp.toLp 2 (Function.update x i r)) j = x j := by
  change Function.update x i r j = x j
  exact Function.update_of_ne h _ _

/-- Derivative of a coordinate of the shifted point along the line `r ↦ update x i r`. -/
private lemma coord_update_hasDerivAt_aux (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n)
    (y : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    HasDerivAt (fun r' => (WithLp.toLp 2 (Function.update x i r') - y) j)
      (if j = i then 1 else 0) r := by
  by_cases h : j = i
  · subst h
    have heq : (fun r' => (WithLp.toLp 2 (Function.update x j r') - y) j)
        = (fun r' => r' - y j) := by
      funext r'
      have e2 : ((WithLp.toLp 2 (Function.update x j r')) - y) j
          = (WithLp.toLp 2 (Function.update x j r')) j - y j :=
        Pi.sub_apply _ _ _
      rw [e2, toLp_update_same_aux n x j r']
    have hif : (if j = j then (1 : ℝ) else 0) = 1 := by simp
    rw [heq, hif]
    exact (hasDerivAt_id r).sub_const (y j)
  · have heq : (fun r' => (WithLp.toLp 2 (Function.update x i r') - y) j)
        = (fun _ => x j - y j) := by
      funext r'
      have e2 : ((WithLp.toLp 2 (Function.update x i r')) - y) j
          = (WithLp.toLp 2 (Function.update x i r')) j - y j :=
        Pi.sub_apply _ _ _
      rw [e2, toLp_update_of_ne_aux n x i j r' h]
    have hif : (if j = i then (1 : ℝ) else 0) = 0 := by simp [h]
    rw [heq, hif]
    exact hasDerivAt_const r (x j - y j)

/-- Derivative of a polynomial evaluated along the line `r ↦ update x i r`
is the evaluation of the partial derivative. -/
private lemma poly_line_hasDerivAt_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    HasDerivAt (fun r' => MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r') - y)
      j) Q)
      (MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j)
        (MvPolynomial.pderiv i Q)) r := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have heq : (fun r' => MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r') - y)
      j)
          (MvPolynomial.C a)) = (fun _ => a) := by
      funext r'
      simp
    have hval : MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j)
        (MvPolynomial.pderiv i (MvPolynomial.C a)) = 0 := by
      rw [MvPolynomial.pderiv_C]
      simp
    rw [heq, hval]
    exact hasDerivAt_const r a
  | add P Q ihP ihQ =>
    have heq : (fun r' => MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r') - y)
      j) (P + Q))
        = (fun r' => MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r') - y) j) P
          + MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r') - y) j) Q) := by
      funext r'
      rw [MvPolynomial.eval_add]
    have hval : MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j)
          (MvPolynomial.pderiv i (P + Q))
        = MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j)
          (MvPolynomial.pderiv i P)
          + MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j)
            (MvPolynomial.pderiv i Q) := by
      rw [map_add (MvPolynomial.pderiv i), MvPolynomial.eval_add]
    rw [heq, hval]
    exact ihP.add ihQ
  | mul_X P j ihP =>
    have hcoord := coord_update_hasDerivAt_aux n x i j y r
    have hcoordval : MvPolynomial.eval (fun j' => (WithLp.toLp 2 (Function.update x i r) - y) j')
        (MvPolynomial.pderiv i (MvPolynomial.X j)) = (if j = i then (1 : ℝ) else 0) := by
      by_cases h : j = i
      · subst h
        rw [MvPolynomial.pderiv_X_self]
        simp
      · rw [MvPolynomial.pderiv_X_of_ne h]
        simp [h]
    have heq : (fun r' => MvPolynomial.eval (fun j' => (WithLp.toLp 2 (Function.update x i r') - y)
      j')
          (P * MvPolynomial.X j))
        = (fun r' => MvPolynomial.eval (fun j' => (WithLp.toLp 2 (Function.update x i r') - y) j') P
          * (WithLp.toLp 2 (Function.update x i r') - y) j) := by
      funext r'
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    have hval : MvPolynomial.eval (fun j' => (WithLp.toLp 2 (Function.update x i r) - y) j')
          (MvPolynomial.pderiv i (P * MvPolynomial.X j))
        = MvPolynomial.eval (fun j' => (WithLp.toLp 2 (Function.update x i r) - y) j')
          (MvPolynomial.pderiv i P)
          * (WithLp.toLp 2 (Function.update x i r) - y) j
          + MvPolynomial.eval (fun j' => (WithLp.toLp 2 (Function.update x i r) - y) j') P
          * (if j = i then (1 : ℝ) else 0) := by
      rw [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_mul,
        MvPolynomial.eval_X, hcoordval]
    rw [heq, hval]
    exact ihP.mul hcoord

/-- Derivative of the squared norm along the line `r ↦ update x i r`. -/
private lemma normSq_line_hasDerivAt_aux (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (y : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    HasDerivAt (fun r' => ‖WithLp.toLp 2 (Function.update x i r') - y‖ ^ 2)
      (2 * (WithLp.toLp 2 (Function.update x i r) - y) i) r := by
  have hterm : ∀ j : Fin n, HasDerivAt
      (fun r' => ((WithLp.toLp 2 (Function.update x i r') - y) j) ^ 2)
      ((if j = i then (1 : ℝ) else 0) * (WithLp.toLp 2 (Function.update x i r) - y) j
        + (WithLp.toLp 2 (Function.update x i r) - y) j * (if j = i then (1 : ℝ) else 0)) r := by
    intro j
    have h := coord_update_hasDerivAt_aux n x i j y r
    have hm := h.mul h
    have hpow : (fun r' => ((WithLp.toLp 2 (Function.update x i r') - y) j) ^ 2)
        = (fun r' => (WithLp.toLp 2 (Function.update x i r') - y) j)
          * (fun r' => (WithLp.toLp 2 (Function.update x i r') - y) j) := by
      funext r'
      simp only [pow_two, Pi.mul_apply]
    rw [hpow]
    exact hm
  have hfun : (fun r' => ‖WithLp.toLp 2 (Function.update x i r') - y‖ ^ 2)
      = (∑ j ∈ Finset.univ, (fun r' => ((WithLp.toLp 2 (Function.update x i r') - y) j) ^ 2)) := by
    funext r'
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_apply]
  have h0 : ∀ j ∈ Finset.univ, j ≠ i →
      ((if j = i then (1 : ℝ) else 0) * (WithLp.toLp 2 (Function.update x i r) - y) j
        + (WithLp.toLp 2 (Function.update x i r) - y) j * (if j = i then (1 : ℝ) else 0)) = 0 := by
    intro j _ hji
    simp [hji]
  have hval : (∑ j ∈ Finset.univ, ((if j = i then (1 : ℝ) else 0)
          * (WithLp.toLp 2 (Function.update x i r) - y) j
          + (WithLp.toLp 2 (Function.update x i r) - y) j * (if j = i then (1 : ℝ) else 0)))
      = 2 * (WithLp.toLp 2 (Function.update x i r) - y) i := by
    rw [Finset.sum_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h)]
    have e1 : (if i = i then (1 : ℝ) else 0) = 1 := by simp
    rw [e1]
    ring
  rw [hfun, ← hval]
  exact HasDerivAt.sum (fun j _ => hterm j)

/-- Derivative of the Gaussian factor along the line `r ↦ update x i r`. -/
private lemma gauss_line_hasDerivAt_aux (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (y : EuclideanSpace ℝ (Fin n)) (t r : ℝ) :
    HasDerivAt (fun r' => Real.exp (-‖WithLp.toLp 2 (Function.update x i r') - y‖ ^ 2 / (4 * t)))
      (Real.exp (-‖WithLp.toLp 2 (Function.update x i r) - y‖ ^ 2 / (4 * t))
        * (-(2 * (WithLp.toLp 2 (Function.update x i r) - y) i) / (4 * t))) r := by
  have hS := normSq_line_hasDerivAt_aux n x i y r
  exact (hS.neg.div_const (4 * t)).exp

/-- Evaluation commutes with scalar multiplication. -/
private lemma eval_smul_eq_aux (n : ℕ) (z : Fin n → ℝ) (c : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval z (c • P) = c * MvPolynomial.eval z P := by
  exact MvPolynomial.smul_eval z P c

/-- Pointwise first partial of a class-member kernel along the line,
as a sum of two class members. -/
private lemma kernel_line_hasDerivAt_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r' => g y * gaussPolyKernel n Q k t (WithLp.toLp 2 (Function.update x i r') -
      y))
      (g y * (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (WithLp.toLp 2 (Function.update x i
        r) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          (WithLp.toLp 2 (Function.update x i r) - y))) r := by
  have hE := gauss_line_hasDerivAt_aux n x i y t r
  have hP := poly_line_hasDerivAt_aux n Q x i y r
  have hA1E := hE.const_mul ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))
  have hmul := hA1E.mul hP
  have hKraw := hmul.mul_const (t ^ (-(k : ℤ)))
  have htne : t ≠ 0 := ne_of_gt ht
  have h4t : (4 : ℝ) * t ≠ 0 := by positivity
  have hz : t ^ (-(((k + 1 : ℕ)) : ℤ)) = t ^ (-(k : ℤ)) * t⁻¹ := by
    have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by norm_cast
    have hexp : (-(((k + 1 : ℕ)) : ℤ)) = (-(k : ℤ)) + (-1) := by rw [hcast]; ring
    rw [hexp, zpow_add₀ htne, zpow_neg_one]
  have hK : HasDerivAt (fun r' => gaussPolyKernel n Q k t (WithLp.toLp 2 (Function.update x i r') -
    y))
      (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (WithLp.toLp 2 (Function.update x i r) - y)
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          (WithLp.toLp 2 (Function.update x i r) - y)) r := by
    have hfun : (fun r' => gaussPolyKernel n Q k t (WithLp.toLp 2 (Function.update x i r') - y))
        = (fun r' => ((fun r'' => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖WithLp.toLp 2 (Function.update x i r'') - y‖ ^ 2 / (4 * t)))
          * (fun r'' => MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r'') - y)
            j) Q)) r'
          * t ^ (-(k : ℤ))) := by
      funext r'
      unfold gaussPolyKernel
      simp only [Pi.mul_apply]
    have hval : (gaussPolyKernel n (MvPolynomial.pderiv i Q) k t (WithLp.toLp 2 (Function.update x
      i r) - y)
          + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            (WithLp.toLp 2 (Function.update x i r) - y))
        = (((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (Real.exp (-‖WithLp.toLp 2 (Function.update x i r) - y‖ ^ 2 / (4 * t))
              * (-(2 * (WithLp.toLp 2 (Function.update x i r) - y) i) / (4 * t))))
            * MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j) Q
          + (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖WithLp.toLp 2 (Function.update x i r) - y‖ ^ 2 / (4 * t))
            * MvPolynomial.eval (fun j => (WithLp.toLp 2 (Function.update x i r) - y) j)
              (MvPolynomial.pderiv i Q)) * t ^ (-(k : ℤ)) := by
      unfold gaussPolyKernel
      rw [eval_smul_eq_aux, MvPolynomial.eval_mul, MvPolynomial.eval_X, hz]
      field_simp [htne, h4t]
      ring
    rw [hfun, hval]
    exact hKraw
  exact hK.const_mul (g y)

/-- Coordinate evaluation on EuclideanSpace is continuous (it is 1-Lipschitz). -/
private lemma coord_continuous_aux (n : ℕ) (j : Fin n) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => y j) := by
  have hLip : LipschitzWith 1 (fun y : EuclideanSpace ℝ (Fin n) => y j) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have e : ((y - z : EuclideanSpace ℝ (Fin n)) j) = y j - z j := Pi.sub_apply _ _ _
    have h := coord_le_norm_aux n (y - z) j
    rw [e] at h
    rw [Real.dist_eq, dist_eq_norm]
    simpa using h
  exact hLip.continuous

/-- A class-member kernel is continuous in the integration variable. -/
private lemma kernel_continuous_in_y_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (t : ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => gaussPolyKernel n Q k t (w - y)) := by
  have hcoord : ∀ j : Fin n, Continuous (fun y : EuclideanSpace ℝ (Fin n) => (w - y) j) := by
    intro j
    have heq : (fun y : EuclideanSpace ℝ (Fin n) => (w - y) j) = (fun y => w j - y j) := by
      funext y
      exact Pi.sub_apply w y j
    rw [heq]
    exact continuous_const.sub (coord_continuous_aux n j)
  have hpoly : ∀ P : MvPolynomial (Fin n) ℝ,
      Continuous (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => (w - y) j) P) :=
        by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      have heq : (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun j => (w - y) j) (MvPolynomial.C a)) = (fun _ => a) := by
        funext y
        simp
      rw [heq]
      exact continuous_const
    | add P Q ihP ihQ =>
      have heq : (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun j => (w - y) j) (P + Q))
          = (fun y => MvPolynomial.eval (fun j => (w - y) j) P
            + MvPolynomial.eval (fun j => (w - y) j) Q) := by
        funext y
        rw [MvPolynomial.eval_add]
      rw [heq]
      exact ihP.add ihQ
    | mul_X P j ihP =>
      have heq : (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun j' => (w - y) j') (P * MvPolynomial.X j))
          = (fun y => MvPolynomial.eval (fun j' => (w - y) j') P * (w - y) j) := by
        funext y
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [heq]
      exact ihP.mul (hcoord j)
  have hnorm : Continuous (fun y : EuclideanSpace ℝ (Fin n) => ‖w - y‖) :=
    continuous_norm.comp (continuous_const.sub continuous_id)
  have hE : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖w - y‖ ^ 2 / (4 * t))) :=
    Real.continuous_exp.comp ((hnorm.pow 2).neg.div_const (4 * t))
  have hP := hpoly Q
  unfold gaussPolyKernel
  exact ((continuous_const.mul hE).mul hP).mul continuous_const

/-- Integrability of the domination bound in division form. -/
private lemma integrable_polygauss_divform_aux (n : ℕ) (D : ℕ) (t : ℝ) (ht : 0 < t) (C : ℝ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => C * ((1 + ‖y‖) ^ D * Real.exp (-‖y‖ ^ 2 / (8 *
      t))))
      volume := by
  have htne : t ≠ 0 := ne_of_gt ht
  have h8t : (8 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) htne
  have hexp : ∀ y : EuclideanSpace ℝ (Fin n),
      Real.exp (-‖y‖ ^ 2 / (8 * t)) = Real.exp (-(1 / (8 * t)) * ‖y‖ ^ 2) := by
    intro y
    congr 1
    field_simp [h8t]
  have heq : (fun y : EuclideanSpace ℝ (Fin n) => C * ((1 + ‖y‖) ^ D * Real.exp (-‖y‖ ^ 2 / (8 *
    t))))
      = (fun y => C * ((1 + ‖y‖) ^ D * Real.exp (-(1 / (8 * t)) * ‖y‖ ^ 2))) := by
    funext y
    rw [hexp y]
  rw [heq]
  have hpos : (0 : ℝ) < 1 / (8 * t) := by positivity
  exact (integrable_poly_gauss_aux n D (1 / (8 * t)) hpos).const_mul C

/-- The line `r ↦ update x i r` stays in a ball for `r` near `s₀`. -/
private lemma w_ball_bound_aux (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s₀ : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ Metric.ball s₀ 1, ‖WithLp.toLp 2 (Function.update x i r)‖ ≤ R := by
  refine ⟨|s₀| + 1 + ‖x‖, by positivity, fun r hr => ?_⟩
  have hdist : dist r s₀ < 1 := Metric.mem_ball.mp hr
  have habs : |r - s₀| < 1 := by
    rw [dist_eq_norm] at hdist
    simpa [Real.norm_eq_abs] using hdist
  have hr_le : |r| ≤ |s₀| + 1 := by
    have h1 : |r| ≤ |r - s₀| + |s₀| := by
      have e : r = (r - s₀) + s₀ := by ring
      conv_lhs => rw [e]
      exact abs_add_le (r - s₀) s₀
    linarith [habs]
  have hwi : (WithLp.toLp 2 (Function.update x i r)) i = r :=
    toLp_update_same_aux n x i r
  have hrest : ∀ j ∈ Finset.univ.erase i, (WithLp.toLp 2 (Function.update x i r)) j = x j := by
    intro j hj
    exact toLp_update_of_ne_aux n x i j r (Finset.ne_of_mem_erase hj)
  have hsq : ‖WithLp.toLp 2 (Function.update x i r)‖ ^ 2
      = r ^ 2 + ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hwi]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hrest j hj]
  have hle1 : r ^ 2 ≤ (|s₀| + 1) ^ 2 := by
    have h1 : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
    have h2 : |r| ^ 2 ≤ (|s₀| + 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg r) hr_le 2
    rwa [h1]
  have hle2 : ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsplit : ∑ j ∈ (Finset.univ : Finset (Fin n)), (x j) ^ 2
        = (x i) ^ 2 + ∑ j ∈ Finset.univ.erase i, (x j) ^ 2 :=
      (Finset.add_sum_erase Finset.univ (fun j => (x j) ^ 2) (Finset.mem_univ i)).symm
    rw [hsplit]
    have hnn : (0 : ℝ) ≤ (x i) ^ 2 := sq_nonneg (x i)
    linarith [hnn]
  have hsq_le : ‖WithLp.toLp 2 (Function.update x i r)‖ ^ 2 ≤ (|s₀| + 1) ^ 2 + ‖x‖ ^ 2 := by
    rw [hsq]
    exact add_le_add hle1 hle2
  have hR2 : (|s₀| + 1) ^ 2 + ‖x‖ ^ 2 ≤ (|s₀| + 1 + ‖x‖) ^ 2 := by
    have e : (|s₀| + 1 + ‖x‖) ^ 2 = (|s₀| + 1) ^ 2 + ‖x‖ ^ 2 + 2 * ((|s₀| + 1) * ‖x‖) := by ring
    rw [e]
    have hnn : (0 : ℝ) ≤ 2 * ((|s₀| + 1) * ‖x‖) := by positivity
    linarith [hnn]
  have hfin : ‖WithLp.toLp 2 (Function.update x i r)‖ ^ 2 ≤ (|s₀| + 1 + ‖x‖) ^ 2 :=
    le_trans hsq_le hR2
  have hRnn : (0 : ℝ) ≤ |s₀| + 1 + ‖x‖ := by positivity
  calc ‖WithLp.toLp 2 (Function.update x i r)‖
      = √(‖WithLp.toLp 2 (Function.update x i r)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((|s₀| + 1 + ‖x‖) ^ 2) := Real.sqrt_le_sqrt hfin
    _ = |s₀| + 1 + ‖x‖ := Real.sqrt_sq hRnn

/-- A class-member convolution integrand is integrable at any fixed center. -/
private lemma integrable_kernel_conv_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (t : ℝ) (ht : 0 < t) (w : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => g y * gaussPolyKernel n Q k t (w - y)) volume := by
  obtain ⟨M, hM⟩ := hg_bdd
  obtain ⟨C0, D0, hC0, hK⟩ := gaussPolyKernel_le_bound_aux n Q k t ‖w‖ ht (norm_nonneg w)
  have hBint : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (|M| * C0) * ((1 + ‖y‖) ^ D0 * Real.exp (-‖y‖ ^ 2 / (8 * t)))) volume :=
    integrable_polygauss_divform_aux n D0 t ht (|M| * C0)
  have hmeas : AEStronglyMeasurable (fun y => g y * gaussPolyKernel n Q k t (w - y)) volume :=
    hg_meas.mul (kernel_continuous_in_y_aux n Q k t w).aestronglyMeasurable
  refine hBint.mono' hmeas ?_
  filter_upwards [hM] with y hy
  rw [Real.norm_eq_abs, abs_mul]
  have hKy := hK w y le_rfl
  have hgM : |g y| ≤ |M| := le_trans hy (le_abs_self M)
  calc |g y| * |gaussPolyKernel n Q k t (w - y)|
      ≤ |M| * (C0 * ((1 + ‖y‖) ^ D0 * Real.exp (-‖y‖ ^ 2 / (8 * t)))) :=
        mul_le_mul hgM hKy (abs_nonneg _) (abs_nonneg _)
    _ = (|M| * C0) * ((1 + ‖y‖) ^ D0 * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by ring

/-- First coordinate partial of a class-member convolution, as a sum of two
class-member convolutions (differentiate once under the integral). -/
private lemma firstPartial_conv_aux (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (s₀ : ℝ) :
    HasDerivAt (fun r => ∫ y, g y * gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update x i r) - y))
      (∫ y, (g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          (WithLp.toLp 2 (Function.update x i s₀) - y)
        + g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          (WithLp.toLp 2 (Function.update x i s₀) - y))) s₀ := by
  obtain ⟨M, hM⟩ := hg_bdd
  obtain ⟨R, hR, hwR⟩ := w_ball_bound_aux n x i s₀
  obtain ⟨C₁, D₁, hC₁, hK₁⟩ :=
    gaussPolyKernel_le_bound_aux n (MvPolynomial.pderiv i Q) k t R ht hR
  obtain ⟨C₂, D₂, hC₂, hK₂⟩ := gaussPolyKernel_le_bound_aux n
    ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t R ht hR
  have hF_meas : ∀ᶠ r in 𝓝 s₀, AEStronglyMeasurable
      (fun y => g y * gaussPolyKernel n Q k t (WithLp.toLp 2 (Function.update x i r) - y))
      volume :=
    Filter.Eventually.of_forall fun r =>
      hg_meas.mul (kernel_continuous_in_y_aux n Q k t
        (WithLp.toLp 2 (Function.update x i r))).aestronglyMeasurable
  have hF_int : Integrable
      (fun y => g y * gaussPolyKernel n Q k t (WithLp.toLp 2 (Function.update x i s₀) - y))
      volume :=
    integrable_kernel_conv_aux n Q k g hg_meas ⟨M, hM⟩ t ht _
  have hF'_meas : AEStronglyMeasurable
      (fun y => g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          (WithLp.toLp 2 (Function.update x i s₀) - y)
        + g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          (WithLp.toLp 2 (Function.update x i s₀) - y)) volume :=
    (hg_meas.mul (kernel_continuous_in_y_aux n (MvPolynomial.pderiv i Q) k t
      (WithLp.toLp 2 (Function.update x i s₀))).aestronglyMeasurable).add
      (hg_meas.mul (kernel_continuous_in_y_aux n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q))
        (k + 1) t (WithLp.toLp 2 (Function.update x i s₀))).aestronglyMeasurable)
  have hbound_int : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => (|M| * (C₁ + C₂))
        * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t)))) volume :=
    integrable_polygauss_divform_aux n (max D₁ D₂) t ht (|M| * (C₁ + C₂))
  have h_bound : ∀ᵐ y ∂volume, ∀ r ∈ Metric.ball s₀ 1,
      ‖g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          (WithLp.toLp 2 (Function.update x i r) - y)
        + g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          (WithLp.toLp 2 (Function.update x i r) - y)‖
        ≤ (|M| * (C₁ + C₂)) * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by
    filter_upwards [hM] with y hy
    intro r hr
    have hwr : ‖WithLp.toLp 2 (Function.update x i r)‖ ≤ R := hwR r hr
    have hK1 := hK₁ _ y hwr
    have hK2 := hK₂ _ y hwr
    have hgM : |g y| ≤ |M| := le_trans hy (le_abs_self M)
    have hbase1 : (1 : ℝ) ≤ 1 + ‖y‖ := by
      have hn := norm_nonneg y
      linarith
    have eD1 : (1 + ‖y‖) ^ D₁ ≤ (1 + ‖y‖) ^ max D₁ D₂ :=
      pow_le_pow_right₀ hbase1 (le_max_left D₁ D₂)
    have eD2 : (1 + ‖y‖) ^ D₂ ≤ (1 + ‖y‖) ^ max D₁ D₂ :=
      pow_le_pow_right₀ hbase1 (le_max_right D₁ D₂)
    have hexpnn : (0 : ℝ) ≤ Real.exp (-‖y‖ ^ 2 / (8 * t)) := (Real.exp_pos _).le
    have eB1 : (1 + ‖y‖) ^ D₁ * Real.exp (-‖y‖ ^ 2 / (8 * t))
        ≤ (1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t)) :=
      mul_le_mul_of_nonneg_right eD1 hexpnn
    have eB2 : (1 + ‖y‖) ^ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t))
        ≤ (1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t)) :=
      mul_le_mul_of_nonneg_right eD2 hexpnn
    have eC1 : C₁ * ((1 + ‖y‖) ^ D₁ * Real.exp (-‖y‖ ^ 2 / (8 * t)))
        ≤ C₁ * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_left eB1 hC₁
    have eC2 : C₂ * ((1 + ‖y‖) ^ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t)))
        ≤ C₂ * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_left eB2 hC₂
    rw [Real.norm_eq_abs]
    calc |g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            (WithLp.toLp 2 (Function.update x i r) - y)
          + g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            (WithLp.toLp 2 (Function.update x i r) - y)|
        ≤ |g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            (WithLp.toLp 2 (Function.update x i r) - y)|
          + |g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            (WithLp.toLp 2 (Function.update x i r) - y)| := abs_add_le _ _
      _ = |g y| * |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            (WithLp.toLp 2 (Function.update x i r) - y)|
          + |g y| * |gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            (WithLp.toLp 2 (Function.update x i r) - y)| := by rw [abs_mul, abs_mul]
      _ ≤ |M| * |gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
            (WithLp.toLp 2 (Function.update x i r) - y)|
          + |M| * |gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
            (WithLp.toLp 2 (Function.update x i r) - y)| := by
          apply add_le_add <;> exact mul_le_mul_of_nonneg_right hgM (abs_nonneg _)
      _ ≤ |M| * (C₁ * ((1 + ‖y‖) ^ D₁ * Real.exp (-‖y‖ ^ 2 / (8 * t))))
          + |M| * (C₂ * ((1 + ‖y‖) ^ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t)))) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hK1 (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_left hK2 (abs_nonneg _)
      _ ≤ |M| * (C₁ * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t))))
          + |M| * (C₂ * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t)))) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left eC1 (abs_nonneg _)
          · exact mul_le_mul_of_nonneg_left eC2 (abs_nonneg _)
      _ = (|M| * (C₁ + C₂)) * ((1 + ‖y‖) ^ max D₁ D₂ * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by
          ring
  have h_diff : ∀ᵐ y ∂volume, ∀ r ∈ Metric.ball s₀ 1,
      HasDerivAt (fun s => g y * gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i s) - y))
        (g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
          (WithLp.toLp 2 (Function.update x i r) - y)
          + g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
          (WithLp.toLp 2 (Function.update x i r) - y)) r := by
    refine Filter.Eventually.of_forall fun y r _ => ?_
    have h := kernel_line_hasDerivAt_aux n Q k x i g y t r ht
    rwa [mul_add] at h
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ zero_lt_one)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- Second coordinate partial of a class-member convolution, as a sum
of four class-member convolutions (closure applied twice). -/
private theorem classConv_secondPartial_space_standalone (n : ℕ)
    (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    deriv (fun s => deriv (fun r => ∫ y, g y * gaussPolyKernel n Q k t
        (WithLp.toLp 2 (Function.update x i r) - y)) s) (x i)
      = (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) k t (x - y))
        + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i
          Q)) (k + 1) t (x - y))
        + (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i *
          Q))) (k + 1) t (x - y))
        + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
          (MvPolynomial.X i * Q)))) (k + 2) t (x - y)) := by
  have hDeriv : ∀ s : ℝ, deriv (fun r => ∫ y, g y * gaussPolyKernel n Q k t
      (WithLp.toLp 2 (Function.update x i r) - y)) s
      = ∫ y, (g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
        (WithLp.toLp 2 (Function.update x i s) - y)
        + g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
        (WithLp.toLp 2 (Function.update x i s) - y)) :=
    fun s => (firstPartial_conv_aux n Q k g hg_meas hg_bdd t ht x i s).deriv
  have hInt1 : ∀ s : ℝ, Integrable (fun y => g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
      (WithLp.toLp 2 (Function.update x i s) - y)) volume :=
    fun s => integrable_kernel_conv_aux n _ _ g hg_meas hg_bdd t ht _
  have hInt2 : ∀ s : ℝ, Integrable (fun y => g y * gaussPolyKernel n
      ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
      (WithLp.toLp 2 (Function.update x i s) - y)) volume :=
    fun s => integrable_kernel_conv_aux n _ _ g hg_meas hg_bdd t ht _
  set E₁ : ℝ → ℝ := fun s => ∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i Q) k t
    (WithLp.toLp 2 (Function.update x i s) - y) with hE₁def
  set E₂ : ℝ → ℝ := fun s => ∫ y, g y * gaussPolyKernel n
      ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) t
      (WithLp.toLp 2 (Function.update x i s) - y) with hE₂def
  have hE : (fun s => deriv (fun r => ∫ y, g y * gaussPolyKernel n Q k t
      (WithLp.toLp 2 (Function.update x i r) - y)) s) = E₁ + E₂ := by
    funext s
    simp only [Pi.add_apply]
    rw [hDeriv s]
    exact integral_add (hInt1 s) (hInt2 s)
  have hDiff1 : DifferentiableAt ℝ E₁ (x i) :=
    (firstPartial_conv_aux n (MvPolynomial.pderiv i Q) k g hg_meas hg_bdd t ht x i (x
      i)).differentiableAt
  have hDiff2 : DifferentiableAt ℝ E₂ (x i) :=
    (firstPartial_conv_aux n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) g hg_meas hg_bdd t ht
      x i
      (x i)).differentiableAt
  have hD1 : deriv E₁ (x i)
      = ∫ y, (g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) k t
        (WithLp.toLp 2 (Function.update x i (x i)) - y)
        + g y * gaussPolyKernel n
          ((-1 / 2 : ℝ) • (MvPolynomial.X i * (MvPolynomial.pderiv i Q))) (k + 1) t
          (WithLp.toLp 2 (Function.update x i (x i)) - y)) :=
    (firstPartial_conv_aux n (MvPolynomial.pderiv i Q) k g hg_meas hg_bdd t ht x i (x i)).deriv
  have hD2 : deriv E₂ (x i)
      = ∫ y, (g y * gaussPolyKernel n
        (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q))) (k + 1) t
        (WithLp.toLp 2 (Function.update x i (x i)) - y)
        + g y * gaussPolyKernel n
          ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)))) (k + 2) t
          (WithLp.toLp 2 (Function.update x i (x i)) - y)) :=
    (firstPartial_conv_aux n ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)) (k + 1) g hg_meas hg_bdd t ht
      x i
      (x i)).deriv
  have hcx : WithLp.toLp 2 (Function.update x i (x i)) = x := by
    rw [Function.update_eq_self, WithLp.toLp_ofLp]
  have hI1 := integrable_kernel_conv_aux n (MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) k g
    hg_meas hg_bdd t ht (WithLp.toLp 2 (Function.update x i (x i)))
  have hI2 := integrable_kernel_conv_aux n
    ((-1 / 2 : ℝ) • (MvPolynomial.X i * (MvPolynomial.pderiv i Q))) (k + 1) g hg_meas hg_bdd t ht
      (WithLp.toLp 2 (Function.update x i (x i)))
  have hI3 := integrable_kernel_conv_aux n
    (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q))) (k + 1) g hg_meas hg_bdd t ht
      (WithLp.toLp 2 (Function.update x i (x i)))
  have hI4 := integrable_kernel_conv_aux n
    ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i * Q)))) (k + 2) g hg_meas
    hg_bdd t ht (WithLp.toLp 2 (Function.update x i (x i)))
  rw [hE, deriv_add hDiff1 hDiff2, hD1, hD2, integral_add hI1 hI2, integral_add hI3 hI4, hcx]
  abel

end SecondRep

/-! ## I. Heat equation assembly -/

section H4cFinal

open MeasureTheory


/-- The heat convolution satisfies the heat equation, assembled from
the time partial, the second partials, the kernel PDE, the four-term
kernel identity, and the integrability lemma. -/
private theorem heatConvolution_satisfies_heat_equation_final_asm (n : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (hTimeThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)),
      HasDerivAt (fun s => ∫ y, g y * gaussPolyKernel n Q k s (x - y))
        (∫ y, g y * deriv (fun s => gaussPolyKernel n Q k s (x - y)) t) t)
    (hSecondThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)) (i : Fin n),
      deriv (fun s => deriv (fun r => ∫ y, g y * gaussPolyKernel n Q k t
          (WithLp.toLp 2 (Function.update x i r) - y)) s) (x i)
        = (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) k t (x -
          y))
          + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i
            Q)) (k + 1) t (x - y))
          + (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i
            * Q))) (k + 1) t (x - y))
          + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
            (MvPolynomial.X i * Q)))) (k + 2) t (x - y)))
    (hKernelPDEThm : ∀ (n : ℕ) {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)),
      deriv (fun s => (4 * Real.pi * s) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖x‖ ^ 2 / (4 * s))) t
        = ∑ i : Fin n, deriv (fun s => deriv (fun r =>
            (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖WithLp.toLp 2 (Function.update x i r)‖ ^ 2 / (4 * t))) s) (x i))
    (hFourTermThm : ∀ (n : ℕ) (i : Fin n) {t : ℝ}, 0 < t →
      ∀ (z : EuclideanSpace ℝ (Fin n)),
      (gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t z
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1)) 1 t z
        + gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))) 1 t z
        + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i *
          1)))) 2 t z)
        = deriv (fun s => deriv (fun r =>
            (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖WithLp.toLp 2 (Function.update z i r)‖ ^ 2 / (4 * t))) s) (z i))
    (hIntBddThm : ∀ (n : ℕ) (Q : MvPolynomial (Fin n) ℝ) (k : ℕ)
      {g : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable g volume → (∃ M : ℝ, ∀ᵐ y, |g y| ≤ M) →
      ∀ {t : ℝ}, 0 < t → ∀ (x : EuclideanSpace ℝ (Fin n)),
      Integrable (fun y => g y * gaussPolyKernel n Q k t (x - y)) volume) :
    deriv (fun s => heatConvolution n g s x) t
      = Laplacian.laplacian (fun y => heatConvolution n g t y) x := by
  -- The class kernel at `(Q, k) = (1, 0)` is the heat kernel.
  have hKeq : ∀ (s : ℝ) (z : EuclideanSpace ℝ (Fin n)),
      gaussPolyKernel n 1 0 s z = Φ n s z := by
    intro s z
    simp [heatKernel, gaussPolyKernel]
  -- The convolution in class-kernel form.
  have hCeq : ∀ (s : ℝ) (z : EuclideanSpace ℝ (Fin n)),
      heatConvolution n g s z = ∫ y, g y * gaussPolyKernel n 1 0 s (z - y) := by
    intro s z
    change ∫ (y : EuclideanSpace ℝ (Fin n)), g y * Φ n s (z - y)
      = ∫ y, g y * gaussPolyKernel n 1 0 s (z - y)
    apply integral_congr_ae
    filter_upwards with y
    rw [hKeq]
  -- LHS of the heat equation, via the time-partial hypothesis.
  have hTime := hTimeThm n 1 0 hg_meas hg_bdd ht x
  have hLHS : deriv (fun s => heatConvolution n g s x) t
      = ∫ y, g y * deriv (fun s => gaussPolyKernel n 1 0 s (x - y)) t := by
    have hfun : (fun s => heatConvolution n g s x)
        = fun s => ∫ y, g y * gaussPolyKernel n 1 0 s (x - y) :=
      funext fun s => hCeq s x
    rw [hfun]
    exact hTime.deriv
  -- Each second partial of the convolution equals the integral of the iterated
  -- kernel derivative, which is integrable.
  have hPerI : ∀ i : Fin n,
      (deriv (fun s => deriv (fun r => heatConvolution n g t
            (WithLp.toLp 2 (Function.update x i r))) s) (x i)
          = ∫ y, g y * deriv (fun s => deriv (fun r =>
              (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x -
                  y) i))
        ∧ Integrable (fun y => g y * deriv (fun s => deriv (fun r =>
              (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x -
                  y) i)) volume := by
    intro i
    have hI1 := hIntBddThm n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0
      hg_meas hg_bdd ht x
    have hI2 := hIntBddThm n
      ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1)) 1
      hg_meas hg_bdd ht x
    have hI3 := hIntBddThm n
      (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))) 1
      hg_meas hg_bdd ht x
    have hI4 := hIntBddThm n
      ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1)))) 2
      hg_meas hg_bdd ht x
    have h12 : Integrable (fun y =>
        (g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t (x - y))
          + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1))
            1 t (x - y)))
        volume :=
      hI1.add hI2
    have h123 : Integrable (fun y =>
        ((g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t (x - y))
          + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1))
            1 t (x - y)))
          + (g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i *
            1))) 1 t (x - y)))
        volume :=
      h12.add hI3
    have h1234 : Integrable (fun y =>
        (((g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t (x - y))
          + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1))
            1 t (x - y)))
          + (g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i *
            1))) 1 t (x - y)))
          + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
            (MvPolynomial.X i * 1)))) 2 t (x - y)))
        volume :=
      h123.add hI4
    have hPt : ∀ y, (((g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0
      t (x - y))
            + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i
              1)) 1 t (x - y)))
            + (g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i *
              1))) 1 t (x - y)))
            + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
              (MvPolynomial.X i * 1)))) 2 t (x - y))
          = g y * deriv (fun s => deriv (fun r =>
              (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x -
                  y) i) := by
      intro y
      have h4t := hFourTermThm n i ht (x - y)
      calc (((g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t (x - y))
              + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i
                1)) 1 t (x - y)))
              + (g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i *
                1))) 1 t (x - y)))
              + (g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
                (MvPolynomial.X i * 1)))) 2 t (x - y))
            = g y * (((gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t (x -
              y)
              + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv i 1)) 1 t
                (x - y))
              + gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X i * 1))) 1
                t (x - y))
              + gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
                (MvPolynomial.X i * 1)))) 2 t (x - y)) := by
              ring
          _ = g y * deriv (fun s => deriv (fun r =>
              (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x -
                  y) i) := by
              rw [h4t]
    have hEq : (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t
      (x - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv
              i 1)) 1 t (x - y))
            + (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X
              i * 1))) 1 t (x - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
              (MvPolynomial.X i * 1)))) 2 t (x - y))
          = ∫ y, g y * deriv (fun s => deriv (fun r =>
              (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
                * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x -
                  y) i) := by
      simp only [← integral_add hI1 hI2, ← integral_add h12 hI3, ← integral_add h123 hI4]
      apply integral_congr_ae
      filter_upwards with y
      exact hPt y
    have hSecEq : deriv (fun s => deriv (fun r => heatConvolution n g t
            (WithLp.toLp 2 (Function.update x i r))) s) (x i)
          = (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i (MvPolynomial.pderiv i 1)) 0 t (x
            - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * MvPolynomial.pderiv
              i 1)) 1 t (x - y))
            + (∫ y, g y * gaussPolyKernel n (MvPolynomial.pderiv i ((-1 / 2 : ℝ) • (MvPolynomial.X
              i * 1))) 1 t (x - y))
            + (∫ y, g y * gaussPolyKernel n ((-1 / 2 : ℝ) • (MvPolynomial.X i * ((-1 / 2 : ℝ) •
              (MvPolynomial.X i * 1)))) 2 t (x - y)) := by
      simp only [hCeq]
      exact hSecondThm n 1 0 hg_meas hg_bdd ht x i
    refine ⟨?_, ?_⟩
    · exact hSecEq.trans hEq
    · exact h1234.congr (Filter.Eventually.of_forall hPt)
  have hSecEqAll : ∀ i : Fin n, deriv (fun s => deriv (fun r => heatConvolution n g t
          (WithLp.toLp 2 (Function.update x i r))) s) (x i)
        = ∫ y, g y * deriv (fun s => deriv (fun r =>
            (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x -
                y) i) :=
    fun i => (hPerI i).1
  -- Sum/integral interchange for the iterated kernel derivatives.
  have hSwap : (∫ y, g y * (∑ i, deriv (fun s => deriv (fun r =>
          (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x - y)
              i)))
        = ∑ i, ∫ y, g y * deriv (fun s => deriv (fun r =>
          (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖WithLp.toLp 2 (Function.update (x - y) i r)‖ ^ 2 / (4 * t))) s) ((x - y)
              i) := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun i _ => (hPerI i).2)
  -- Laplacian identification. This is the one step not provable from the five
  -- hypotheses alone: it needs second-order spatial differentiability of the
  -- convolution, which none of the hypotheses provides (see report).
  have hLap : Laplacian.laplacian (fun y => heatConvolution n g t y) x
      = ∑ i, deriv (fun s => deriv (fun r => heatConvolution n g t
        (WithLp.toLp 2 (Function.update x i r))) s) (x i) := by
    exact laplacian_heatConvolution_via_smooth n hg_meas hg_bdd ht x
      (fun n g h1 h2 => heat_convolution_smooth n h1 h2)
      (fun n φ hφ x => laplacian_eq_sum_diag_secondPartial n hφ x)
  rw [hLHS, hLap]
  simp only [hSecEqAll]
  rw [← hSwap]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  have hGK : (fun s => gaussPolyKernel n 1 0 s (x - y))
      = (fun s => Φ n s (x - y)) :=
    funext fun s => hKeq s (x - y)
  rw [hGK]
  simpa only [heatKernel_euclideanSpace] using hKernelPDEThm n ht (x - y)

end H4cFinal

section FinalGlueH4

/-- **The heat convolution solves the heat equation.** Let `g` be a.e. strongly measurable on
`EuclideanSpace ℝ (Fin n)` with `|g y| ≤ M` for almost every `y`, for some `M`, and let
`u t x = heatConvolution n g t x`. Then at every time `t > 0` and point `x`, `u_t = Δu`: the
derivative of `s ↦ u s x` at `t` equals the Laplacian of `u t` at `x`. -/
theorem heat_convolution_satisfies_heat_equation (n : ℕ)
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg_meas : AEStronglyMeasurable g volume)
    (hg_bdd : ∃ M : ℝ, ∀ᵐ y, |g y| ≤ M)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => heatConvolution n g s x) t
      = Laplacian.laplacian (fun y => heatConvolution n g t y) x :=
  heatConvolution_satisfies_heat_equation_final_asm n hg_meas hg_bdd ht x
    (fun n Q k _g h1 h2 _t ht x =>
      classConv_hasDerivAt_time n Q k h1 h2 ht x gaussPolyKernel_deriv_time
        gaussPolyKernel_domination)
    (fun n Q k _g h1 h2 _t ht x i =>
      classConv_secondPartial_space_standalone n Q k h1 h2 ht x i)
    (fun n _t ht x => heatKernel_pde n ht x)
    (fun n i _t ht z => fourTermKernel_eq_iteratedDeriv n i ht z)
    (fun n Q k _g h1 h2 _t ht x =>
      integrable_bddMul_gaussPolyKernel n Q k h1 h2 ht x)


end FinalGlueH4

/-! ## J. Constant-one -/

section H1new

open MeasureTheory
open scoped Topology
open Filter


/-- **The heat convolution preserves the constant one.** For `t > 0` and every `x`,
`heatConvolution n (fun _ => 1) t x = 1`. After the translation `y ↦ x - y`, this is the total
mass `integral_heatKernel` of the heat kernel. -/
theorem heat_convolution_const_one (n : ℕ) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatConvolution n (fun _ => 1) t x = 1 := by
  simp only [heatConvolution, one_mul]
  have hneg := integral_neg_eq_self (fun z => Φ n t (x + z))
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
  simp only [← sub_eq_add_neg] at hneg
  rw [hneg, integral_add_left_eq_self]
  exact integral_heatKernel ht

end H1new

/-! ## K. Remainder, modulus, and the `L^p` estimate -/

section Split

open MeasureTheory

private theorem hasDerivAt_eucl_update (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) (i : Fin n) (v0 : ℝ) :
    HasDerivAt (fun v : ℝ => WithLp.toLp 2 (Function.update p i v))
      (EuclideanSpace.single i (1 : ℝ)) v0 := by
  have heq : (fun v : ℝ => WithLp.toLp 2 (Function.update p i v))
      = fun v => p + (v - p i) • EuclideanSpace.single i (1 : ℝ) := by
    ext v j
    simp [Function.update, EuclideanSpace.single]
    by_cases h : j = i <;> simp [h]
  rw [heq]
  have h1 : HasDerivAt (fun v : ℝ => v - p i) (1 : ℝ) v0 :=
    (hasDerivAt_id' v0).sub_const _
  have h2 : HasDerivAt (fun v : ℝ => (v - p i) • EuclideanSpace.single i (1 : ℝ))
      ((1 : ℝ) • EuclideanSpace.single i (1 : ℝ)) v0 :=
    h1.smul_const _
  simpa using h2.const_add p

private theorem eucl_update_self (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (WithLp.toLp 2 (Function.update p i (p i))) = p := by
  ext j
  simp [Function.update]
  by_cases h : j = i <;> simp [h]

private theorem first_partial_eq_fderiv (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hφ : DifferentiableAt ℝ φ p) :
    deriv (fun v : ℝ => φ (WithLp.toLp 2 (Function.update p i v))) (p i)
      = fderiv ℝ φ p (EuclideanSpace.single i (1 : ℝ)) := by
  have hline := hasDerivAt_eucl_update n p i (p i)
  have hφ' : HasFDerivAt φ (fderiv ℝ φ p) p := hφ.hasFDerivAt
  have hpt := eucl_update_self n p i
  have hcomp : HasDerivAt (φ ∘ (fun v : ℝ => WithLp.toLp 2 (Function.update p i v)))
      ((fderiv ℝ φ p) (EuclideanSpace.single i (1 : ℝ))) (p i) :=
    HasFDerivAt.comp_hasDerivAt_of_eq (p i) hφ' hline hpt.symm
  exact hcomp.deriv

private theorem second_partial_eq (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (p : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    deriv (fun v : ℝ => deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update p i v)) j r)))
          ((WithLp.toLp 2 (Function.update p i v)) j))
          (p i)
      = fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j (1 :
        ℝ)))
          p (EuclideanSpace.single i (1 : ℝ)) := by
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hP : ContDiff ℝ 1 (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j
    (1 : ℝ))) :=
    (hφ.fderiv_right (by decide)).clm_apply contDiff_const
  have hPdiff : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q
    (EuclideanSpace.single j (1 : ℝ))) p :=
    (hP.differentiable (by decide)).differentiableAt
  have hfun : (fun v : ℝ => deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update p i v)) j r)))
            ((WithLp.toLp 2 (Function.update p i v)) j))
      = fun v : ℝ => (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j (1
        : ℝ)))
          (WithLp.toLp 2 (Function.update p i v)) := by
    funext v
    exact first_partial_eq_fderiv n φ (WithLp.toLp 2 (Function.update p i v)) j
      (hφdiff.differentiableAt)
  rw [hfun]
  exact first_partial_eq_fderiv n _ p i hPdiff

private theorem continuous_second_partial_in_s (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (x y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    Continuous (fun s : ℝ => deriv (fun v : ℝ => deriv (fun r : ℝ => φ (WithLp.toLp 2
      (Function.update
          (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
          ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
          ((x - s • y) i)) := by
  have hP : ContDiff ℝ 1 (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j
    (1 : ℝ))) :=
    (hφ.fderiv_right (by decide)).clm_apply contDiff_const
  have hcontD2 : Continuous (fun p : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j (1 : ℝ)))
        p (EuclideanSpace.single i (1 : ℝ))) := by
    have hcont : Continuous (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q
      (EuclideanSpace.single j (1 : ℝ)))) :=
      hP.continuous_fderiv (by decide)
    exact hcont.clm_apply continuous_const
  have hline : Continuous (fun s : ℝ => x - s • y) := by fun_prop
  have hcomp : Continuous (fun s : ℝ => fderiv ℝ
      (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j (1 : ℝ)))
        (x - s • y) (EuclideanSpace.single i (1 : ℝ))) :=
    hcontD2.comp hline
  have heq : (fun s : ℝ => deriv (fun v : ℝ => deriv (fun r : ℝ => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i))
      = fun s : ℝ => fderiv ℝ
        (fun q : EuclideanSpace ℝ (Fin n) => fderiv ℝ φ q (EuclideanSpace.single j (1 : ℝ)))
          (x - s • y) (EuclideanSpace.single i (1 : ℝ)) := by
    funext s
    exact second_partial_eq n φ hφ (x - s • y) i j
  rw [heq]
  exact hcomp

private theorem integral_one_sub : (∫ s in (0 : ℝ)..1, (1 - s)) = 1 / 2 := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s : ℝ => s) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  have hsub := intervalIntegral.integral_sub h1 h2
  have h_one : (∫ _ in (0 : ℝ)..1, (1 : ℝ)) = 1 := by simp
  have h_id : (∫ s in (0 : ℝ)..1, s) = 1 / 2 := by simp [integral_id]
  calc (∫ s in (0 : ℝ)..1, (1 - s)) = (∫ _ in (0 : ℝ)..1, (1 : ℝ)) - ∫ s in (0 : ℝ)..1, s := hsub
    _ = 1 - 1 / 2 := by rw [h_one, h_id]
    _ = 1 / 2 := by ring

/-- The `s`-integral split for the Taylor remainder. -/
private theorem s_integral_split (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x y : EuclideanSpace ℝ (Fin n)) :
    ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
          ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
          ((x - s • y) i)
      = (1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i)
        + ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
          - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i)) := by
  have hD : ∀ i j : Fin n, Continuous (fun s : ℝ => deriv (fun v => deriv (fun r => φ (WithLp.toLp
    2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)) :=
    fun i j => continuous_second_partial_in_s n φ hφ x y i j
  have hGcont : Continuous (fun s : ℝ => ∑ i, ∑ j, y i * y j *
      (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
        - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))) := by fun_prop
  have h12 : Continuous (fun s : ℝ => (1 - s)) := continuous_const.sub continuous_id
  have hcont1 : Continuous (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j *
      deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update x i v)) j r)))
        ((WithLp.toLp 2 (Function.update x i v)) j))
        (x i)) :=
    h12.mul continuous_const
  have hcont2 : Continuous (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j *
      (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
        - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))) :=
    h12.mul hGcont
  have hI1 : IntervalIntegrable (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j *
      deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update x i v)) j r)))
        ((WithLp.toLp 2 (Function.update x i v)) j))
        (x i)) volume 0 1 :=
    hcont1.intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j *
      (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
        - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))) volume 0 1 :=
    hcont2.intervalIntegrable _ _
  have hsum : ∀ s : ℝ, (∑ i, ∑ j, y i * y j *
      deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
        ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
        ((x - s • y) i))
      = (∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
        + ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
                ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
                ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i)) := by
    intro s
    have h1 : ∀ i j : Fin n, y i * y j *
        (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
          - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))
        = y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
          - y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i) := fun i j => by ring
    simp_rw [h1, Finset.sum_sub_distrib]
    ring
  have hcongr : (∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
          ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
          ((x - s • y) i))
      = ∫ s in (0 : ℝ)..1, ((1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i)
        + (1 - s) * ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
                ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
                ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i))) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [hsum s]
    ring
  have hsplit : (∫ s in (0 : ℝ)..1, ((1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i)
        + (1 - s) * ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
                ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
                ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i))))
      = (∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))
        + ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
                ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
                ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i)) :=
    intervalIntegral.integral_add hI1 hI2
  have hconst : (∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
      = (1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i) := by
    have h : (∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))
        = (∫ s in (0 : ℝ)..1, (1 - s)) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i) :=
      intervalIntegral.integral_mul_const _ _
    rw [h, integral_one_sub]
  rw [hcongr, hsplit, hconst]

end Split

section Remainder

open MeasureTheory


/-- Remainder identity assembled from Taylor, moments, half, split. -/
private theorem heatConvolution_sub_eq_remainder_asm (n : ℕ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (hMomentsThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hTaylorThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x y : EuclideanSpace ℝ (Fin n)),
      φ (x - y) - φ x + ∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)
        = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i))
    (hHalfThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        * ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))
        = t * Laplacian.laplacian φ x)
    (hSplitThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x y : EuclideanSpace ℝ (Fin n)),
      ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
        = (1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)
          + ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))) :
    heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x
      = ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        * ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
          - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i)) := by
  obtain ⟨hM1, hM2, hM3⟩ := hMomentsThm n ht
  have hK_pos : ∀ y : EuclideanSpace ℝ (Fin n),
      0 < (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) := by
    intro y
    have h4pt : 0 < 4 * Real.pi * t := by
      have hpi : 0 < Real.pi := Real.pi_pos
      positivity
    exact mul_pos (Real.rpow_pos_of_pos h4pt _) (Real.exp_pos _)
  have hK_nn : ∀ y : EuclideanSpace ℝ (Fin n),
      0 ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) :=
    fun y => le_of_lt (hK_pos y)
  have hK_cont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) :=
    continuous_const.mul (Real.continuous_exp.comp
      ((continuous_norm.pow 2).neg.div_const _))
  have hK_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) :=
    Integrable.of_integral_ne_zero (by rw [hM1]; exact one_ne_zero)
  have hdiag_int : ∀ i : Fin n, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i)) := by
    intro i
    have h_if : (if i = i then (2:ℝ) * t else 0) = 2 * t := by simp
    have h := hM3 i i
    rw [h_if] at h
    exact Integrable.of_integral_ne_zero
      (by rw [h]; exact ne_of_gt (by positivity : (0:ℝ) < 2 * t))
  have h2_int : ∀ i j : Fin n, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)) := by
    intro i j
    by_cases hij : i = j
    · have h_if : (if i = j then (2:ℝ) * t else 0) = 2 * t := by simp [hij]
      have h := hM3 i j
      rw [h_if] at h
      exact Integrable.of_integral_ne_zero
        (by rw [h]; exact ne_of_gt (by positivity : (0:ℝ) < 2 * t))
    · have hsum := (hdiag_int i).add (hdiag_int j)
      have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)) :=
        hK_cont.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.mul
          (EuclideanSpace.proj (𝕜 := ℝ) j).continuous)
      refine hsum.mono' hcont.aestronglyMeasurable ?_
      filter_upwards with y
      have hKnn := hK_nn y
      have hineq : |y i * y j| ≤ y i * y i + y j * y j := by
        have h1 : |y i * y j| = |y i| * |y j| := abs_mul _ _
        have h2 : y i * y i = |y i| * |y i| := (abs_mul_abs_self _).symm
        have h3' : y j * y j = |y j| * |y j| := (abs_mul_abs_self _).symm
        rw [h1, h2, h3']
        nlinarith only [sq_nonneg (|y i| - |y j|), abs_nonneg (y i), abs_nonneg (y j),
          mul_nonneg (abs_nonneg (y i)) (abs_nonneg (y j))]
      calc ‖((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)‖
          = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) * |y i * y j| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKnn]
        _ ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) * (y i * y i + y j *
          y j) :=
            mul_le_mul_of_nonneg_left hineq hKnn
        _ = ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i) +
            ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y j * y j) := by
            ring
  have h1_int : ∀ i : Fin n, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) := by
    intro i
    have hsum : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) +
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i)) :=
      hK_int.add (hdiag_int i)
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) :=
      hK_cont.mul (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
    refine hsum.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with y
    have hKnn := hK_nn y
    have hineq : |y i| ≤ 1 + y i * y i := by
      have h2 : y i * y i = |y i| * |y i| := (abs_mul_abs_self _).symm
      rw [h2]
      nlinarith only [sq_nonneg (|y i| - 1), abs_nonneg (y i),
        mul_nonneg (abs_nonneg (y i)) (abs_nonneg (y i))]
    calc ‖((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i‖
        = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) * |y i| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKnn]
      _ ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) * (1 + y i * y i) :=
          mul_le_mul_of_nonneg_left hineq hKnn
      _ = ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) +
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i) := by
          ring
  have hφcont : Continuous φ := hφ.continuous
  have hF1_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) := by
    have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) :=
      continuous_const.sub continuous_id
    have hcomp_cont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => φ (x - y)) :=
      hφcont.comp hsub
    have hprod_cont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
        φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) :=
      hcomp_cont.mul hK_cont
    have hcomp_supp : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => φ (x - y)) :=
      hφ_supp.comp_homeomorph (Homeomorph.subLeft x)
    have hprod_supp : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) =>
        φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) :=
      hcomp_supp.mul_right
    exact hprod_cont.integrable_of_hasCompactSupport hprod_supp
  have hF2_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) :=
    hK_int.const_mul (φ x)
  have hconv_eq : heatConvolution n φ t x
      = ∫ (y : EuclideanSpace ℝ (Fin n)),
        φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) := by
    unfold heatConvolution heatKernel
    rw [finrank_euclideanSpace_fin]
    have hsub : (∫ (y : EuclideanSpace ℝ (Fin n)),
        φ y * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / (4 * t))))
        = ∫ (y : EuclideanSpace ℝ (Fin n)),
          (fun z : EuclideanSpace ℝ (Fin n) =>
            φ z * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x - z‖ ^ 2 / (4 * t)))) (x - y)
              :=
      (integral_sub_left_eq_self (fun z : EuclideanSpace ℝ (Fin n) =>
        φ z * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x - z‖ ^ 2 / (4 * t)))) volume
          x).symm
    rw [hsub]
    apply integral_congr_ae
    filter_upwards with y
    simp only [sub_sub_cancel]
  have hF3_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) := by
    have hG_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
          deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) := by
      apply integrable_finsetSum Finset.univ
      intro i _
      exact (h1_int i).mul_const _
    have h_eq : ∀ y : EuclideanSpace ℝ (Fin n),
        (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        = ∑ i, (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
          deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i) := by
      intro y
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    exact hG_int.congr (Filter.Eventually.of_forall fun y => (h_eq y).symm)
  have hF4_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
      ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))) := by
    have hG_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, ∑ j, (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y
          j)) *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i)) := by
      apply integrable_finsetSum Finset.univ
      intro i _
      apply integrable_finsetSum Finset.univ
      intro j _
      exact (h2_int i j).mul_const _
    have hKS_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
        (∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))) := by
      have h_eq : ∀ y : EuclideanSpace ℝ (Fin n),
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          (∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))
          = ∑ i, ∑ j, (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i
            * y j)) *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i) := by
        intro y
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      exact hG_int.congr (Filter.Eventually.of_forall fun y => (h_eq y).symm)
    have h_eq2 : ∀ y : EuclideanSpace ℝ (Fin n),
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
        ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))
        = (1 / 2 : ℝ) * (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          (∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))) := by
      intro y
      ring
    have h_half : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (1 / 2 : ℝ) * (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          (∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)))) :=
      hKS_int.const_mul (1 / 2)
    exact h_half.congr (Filter.Eventually.of_forall fun y => (h_eq2 y).symm)
  have hK : ∀ y : EuclideanSpace ℝ (Fin n),
      φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
      = φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        - (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))
        + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)) := by
    intro y
    have hT := hTaylorThm n hφ x y
    have hS := hSplitThm n hφ x y
    linear_combination (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) * hT +
      (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) * hS
  have hF5_int : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
      ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
          ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
          ((x - s • y) i)
        - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))) := by
    have hG_int := ((hF1_int.sub hF2_int).add hF3_int).sub hF4_int
    have hF5_eq : ∀ y : EuclideanSpace ℝ (Fin n),
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
        ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
          - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))
        = φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          - φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          + (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
            ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          - ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
            ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
              deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i)) := by
      intro y
      linarith only [hK y]
    exact hG_int.congr (Filter.Eventually.of_forall fun y => (hF5_eq y).symm)
  have hF2_eq : (∫ y : EuclideanSpace ℝ (Fin n),
      φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) = φ x := by
    rw [integral_const_mul, hM1, mul_one]
  have hF3_eq : (∫ y : EuclideanSpace ℝ (Fin n),
      (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) = 0 := by
    have h_eq : ∀ y : EuclideanSpace ℝ (Fin n),
        (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        = ∑ i, (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
          deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i) := by
      intro y
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_each : ∀ i ∈ Finset.univ, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
        deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) :=
      fun i _ => (h1_int i).mul_const _
    calc (∫ y : EuclideanSpace ℝ (Fin n),
          (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))))
          = ∫ y : EuclideanSpace ℝ (Fin n),
            ∑ i, (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
            deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i) :=
            integral_congr_ae (Filter.Eventually.of_forall h_eq)
        _ = ∑ i, ∫ y : EuclideanSpace ℝ (Fin n),
            (((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
            deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i) :=
            integral_finsetSum Finset.univ h_each
        _ = ∑ i, ((∫ y : EuclideanSpace ℝ (Fin n),
            ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
            deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [integral_mul_const]
        _ = 0 := by
            have h0 : ∀ i ∈ Finset.univ, ((∫ y : EuclideanSpace ℝ (Fin n),
                ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
                deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) = 0 := by
              intro i _
              rw [hM2 i, zero_mul]
            calc (∑ i, ((∫ y : EuclideanSpace ℝ (Fin n),
                  ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i) *
                  deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)))
                  = ∑ i ∈ Finset.univ, (0:ℝ) := Finset.sum_congr rfl h0
                _ = 0 := Finset.sum_const_zero
  have hF4_eq : (∫ y : EuclideanSpace ℝ (Fin n),
      ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
      ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))) = t * Laplacian.laplacian φ x :=
    hHalfThm n hφ hφ_supp ht x
  have hF1_split : (∫ y : EuclideanSpace ℝ (Fin n),
      φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))))
      = (∫ y : EuclideanSpace ℝ (Fin n),
        φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))))
        - (∫ y : EuclideanSpace ℝ (Fin n),
          (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))))
        + (∫ y : EuclideanSpace ℝ (Fin n),
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)))
        + (∫ y : EuclideanSpace ℝ (Fin n),
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))) := by
    have h_congr : (∫ y : EuclideanSpace ℝ (Fin n),
        φ (x - y) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))))
        = ∫ y : EuclideanSpace ℝ (Fin n),
          (φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          - (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
            ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
            ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
              deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i))
          + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
            ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
              (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
                ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
                ((x - s • y) i)
              - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
                (WithLp.toLp 2 (Function.update x i v)) j r)))
                ((WithLp.toLp 2 (Function.update x i v)) j))
                (x i))) :=
      integral_congr_ae (Filter.Eventually.of_forall hK)
    have h12 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        - (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))) :=
      hF2_int.sub hF3_int
    have h123 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (φ x * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        - (∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)) *
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        + ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) *
          ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)))) :=
      h12.add hF4_int
    rw [h_congr]
    rw [integral_add h123 hF5_int]
    rw [integral_add h12 hF4_int]
    rw [integral_sub hF2_int hF3_int]
  rw [hconv_eq, hF1_split, hF2_eq, hF3_eq, hF4_eq]
  ring

end Remainder

section DijProps

open MeasureTheory


private theorem Dij_upd_line (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (v : ℝ) :
    WithLp.toLp 2 (Function.update x.ofLp i v)
      = (x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ))
        + v • EuclideanSpace.single i (1:ℝ) := by
  have h1 : WithLp.toLp 2 (Function.update x.ofLp i v)
      = x + (v - x.ofLp i) • EuclideanSpace.single i (1:ℝ) := by
    apply PiLp.ext
    intro k
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.ofLp_single]
    rw [WithLp.ofLp_toLp]
    by_cases h : k = i
    · subst h
      simp [Function.update_self, Pi.single_eq_same]
    · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]
  rw [h1]
  module

private theorem Dij_inner_bridge (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (y : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    deriv (fun r => φ (WithLp.toLp 2 (Function.update y.ofLp j r))) (y.ofLp j)
      = (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ)) := by
  have hupd : ∀ r : ℝ, WithLp.toLp 2 (Function.update y.ofLp j r)
      = (y - (y.ofLp j) • EuclideanSpace.single j (1:ℝ))
        + r • EuclideanSpace.single j (1:ℝ) :=
    fun r => Dij_upd_line n y j r
  have hfun : (fun r => φ (WithLp.toLp 2 (Function.update y.ofLp j r)))
      = (fun r => φ ((y - (y.ofLp j) • EuclideanSpace.single j (1:ℝ))
        + r • EuclideanSpace.single j (1:ℝ))) := by
    funext r
    rw [hupd r]
  rw [hfun]
  have hdiff : DifferentiableAt ℝ φ
      ((y - (y.ofLp j) • EuclideanSpace.single j (1:ℝ))
        + (y.ofLp j) • EuclideanSpace.single j (1:ℝ)) := by
    have h : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hrec : (y - (y.ofLp j) • EuclideanSpace.single j (1:ℝ))
        + (y.ofLp j) • EuclideanSpace.single j (1:ℝ) = y := by module
    rw [hrec]
    exact h.differentiableAt
  have h := hdiff.deriv_comp_add_smul (y := EuclideanSpace.single j (1:ℝ))
    (x := (y - (y.ofLp j) • EuclideanSpace.single j (1:ℝ)))
    (t := y.ofLp j)
  rw [h]
  have hrec : (y - (y.ofLp j) • EuclideanSpace.single j (1:ℝ))
      + (y.ofLp j) • EuclideanSpace.single j (1:ℝ) = y := by module
  rw [hrec]

private theorem Dij_firstPartial_contDiff (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (j : Fin n) :
    ContDiff ℝ 1 (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) := by
  have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) φ := by
    have heq : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
    rw [heq]
    exact hφ
  have h := (contDiff_succ_iff_fderiv_apply (n := 1)).mp h2
  exact h.2.2 (EuclideanSpace.single j (1:ℝ))

private theorem Dij_secondPartial_eq (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    secondPartialFn n φ i j x
      = (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) x)
        (EuclideanSpace.single i (1:ℝ)) := by
  unfold secondPartialFn
  have hinner : ∀ v : ℝ,
      deriv (fun r => φ (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp j r)))
        ((WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp j)
      = (fderiv ℝ φ (WithLp.toLp 2 (Function.update x.ofLp i v)))
        (EuclideanSpace.single j (1:ℝ)) := by
    intro v
    exact Dij_inner_bridge n φ hφ (WithLp.toLp 2 (Function.update x.ofLp i v)) j
  have houter_fun : (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
        (WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp j r)))
        ((WithLp.toLp 2 (Function.update x.ofLp i v)).ofLp j))
      = (fun v => (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ)))
        (WithLp.toLp 2 (Function.update x.ofLp i v))) := by
    funext v
    exact hinner v
  rw [houter_fun]
  have hg : ContDiff ℝ 1 (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) :=
    Dij_firstPartial_contDiff n φ hφ j
  have hupd2 : ∀ v : ℝ, WithLp.toLp 2 (Function.update x.ofLp i v)
      = (x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ))
        + v • EuclideanSpace.single i (1:ℝ) :=
    fun v => Dij_upd_line n x i v
  have hfun2 : (fun v => (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ)))
        (WithLp.toLp 2 (Function.update x.ofLp i v)))
      = (fun v => (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ)))
        ((x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ))
          + v • EuclideanSpace.single i (1:ℝ))) := by
    funext v
    rw [hupd2 v]
  rw [hfun2]
  have hdiff2 : DifferentiableAt ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ)))
      ((x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ))
        + (x.ofLp i) • EuclideanSpace.single i (1:ℝ)) := by
    have h : Differentiable ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) :=
      hg.differentiable (by norm_num)
    have hrec : (x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ))
        + (x.ofLp i) • EuclideanSpace.single i (1:ℝ) = x := by module
    rw [hrec]
    exact h.differentiableAt
  have h := hdiff2.deriv_comp_add_smul (y := EuclideanSpace.single i (1:ℝ))
    (x := (x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ)))
    (t := x.ofLp i)
  rw [h]
  have hrec : (x - (x.ofLp i) • EuclideanSpace.single i (1:ℝ))
      + (x.ofLp i) • EuclideanSpace.single i (1:ℝ) = x := by module
  rw [hrec]

/-- `D_{ij} φ` for `C²` compactly supported `φ` is continuous, compactly
supported, uniformly continuous, and its modulus tends to `0`. -/
private theorem secondPartial_props (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ) (i j : Fin n) :
    Continuous (secondPartialFn n φ i j)
      ∧ HasCompactSupport (secondPartialFn n φ i j)
      ∧ UniformContinuous (secondPartialFn n φ i j)
      ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
      ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
          |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
            ≤ secondPartialModulus n φ i j ‖z‖)
      ∧ Filter.Tendsto (secondPartialModulus n φ i j)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hg1 : ContDiff ℝ 1 (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) :=
    Dij_firstPartial_contDiff n φ hφ j
  have heq : secondPartialFn n φ i j
      = fun x => (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) x)
        (EuclideanSpace.single i (1:ℝ)) := by
    funext x
    exact Dij_secondPartial_eq n φ hφ i j x
  have hcont : Continuous (secondPartialFn n φ i j) := by
    rw [heq]
    have hfc : Continuous (fderiv ℝ (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ)))) :=
      hg1.continuous_fderiv (by norm_num)
    exact hfc.clm_apply continuous_const
  have hsupp_g : HasCompactSupport (fun y => (fderiv ℝ φ y) (EuclideanSpace.single j (1:ℝ))) :=
    HasCompactSupport.fderiv_apply ℝ hφ_supp (EuclideanSpace.single j (1:ℝ))
  have hsupp : HasCompactSupport (secondPartialFn n φ i j) := by
    rw [heq]
    exact HasCompactSupport.fderiv_apply ℝ hsupp_g (EuclideanSpace.single i (1:ℝ))
  have hunif : UniformContinuous (secondPartialFn n φ i j) :=
    hsupp.uniformContinuous_of_continuous hcont
  have hBdd_all : ∀ r : ℝ, BddAbove {v : ℝ | ∃ x z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ r
      ∧ v = |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|} := by
    intro r
    obtain ⟨U, hU⟩ := hcont.bddAbove_range_of_hasCompactSupport hsupp
    obtain ⟨L, hL⟩ := hcont.bddBelow_range_of_hasCompactSupport hsupp
    use U - L
    intro v hv
    obtain ⟨x', z', _, rfl⟩ := hv
    have h1 : secondPartialFn n φ i j (x' - z') ≤ U := hU (Set.mem_range_self _)
    have h2 : secondPartialFn n φ i j x' ≤ U := hU (Set.mem_range_self _)
    have h3 : L ≤ secondPartialFn n φ i j (x' - z') := hL (Set.mem_range_self _)
    have h4 : L ≤ secondPartialFn n φ i j x' := hL (Set.mem_range_self _)
    rw [abs_le]
    constructor
    · have h : L - U ≤ secondPartialFn n φ i j (x' - z') - secondPartialFn n φ i j x' :=
        sub_le_sub h3 h2
      have heq2 : -(U - L) = L - U := by ring
      rw [heq2]
      exact h
    · exact sub_le_sub h1 h4
  have hnonneg : ∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r := by
    intro r
    unfold secondPartialModulus
    apply Real.sSup_nonneg
    intro v hv
    obtain ⟨x', z', _, rfl⟩ := hv
    exact abs_nonneg _
  have hdom : ∀ (x z : EuclideanSpace ℝ (Fin n)),
      |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
        ≤ secondPartialModulus n φ i j ‖z‖ := by
    intro x z
    unfold secondPartialModulus
    apply le_csSup (hBdd_all ‖z‖)
    exact ⟨x, z, le_rfl, rfl⟩
  have htend : Filter.Tendsto (secondPartialModulus n φ i j)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : (0:ℝ) < ε / 2 := half_pos hε
    obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuous_iff.mp hunif) (ε/2) hε2
    rw [eventually_nhdsWithin_iff]
    rw [Metric.eventually_nhds_iff_ball]
    use δ, hδpos
    intro r hr
    simp only [Metric.mem_ball] at hr
    intro hrIoi
    simp only [Set.mem_Ioi] at hrIoi
    have hr_abs : |r| < δ := by
      have h : dist r (0:ℝ) = |r - 0| := Real.dist_eq r 0
      rw [h] at hr
      simpa using hr
    have hr_lt : r < δ := by
      have h : |r| = r := abs_of_pos hrIoi
      rw [h] at hr_abs
      exact hr_abs
    have hM_nonneg : 0 ≤ secondPartialModulus n φ i j r := hnonneg r
    have hdist : dist (secondPartialModulus n φ i j r) (0:ℝ)
        = secondPartialModulus n φ i j r := by
      rw [Real.dist_eq]
      simp [abs_of_nonneg hM_nonneg]
    rw [hdist]
    have hle : secondPartialModulus n φ i j r ≤ ε / 2 := by
      unfold secondPartialModulus
      apply csSup_le
      · use 0
        use 0, 0
        constructor
        · simp [hrIoi.le]
        · simp
      · intro b hb
        obtain ⟨x', z', hz', rfl⟩ := hb
        have hnorm : ‖z'‖ < δ := lt_of_le_of_lt hz' hr_lt
        have hdist_eq : dist (x' - z') x' = ‖z'‖ := by
          rw [dist_eq_norm]
          have h : (x' - z') - x' = -z' := by module
          rw [h, norm_neg]
        have hDlt : dist (secondPartialFn n φ i j (x' - z')) (secondPartialFn n φ i j x')
            < ε / 2 := hδ (by rw [hdist_eq]; exact hnorm)
        rw [Real.dist_eq] at hDlt
        exact le_of_lt hDlt
    calc secondPartialModulus n φ i j r ≤ ε / 2 := hle
      _ < ε := half_lt_self hε
  exact ⟨hcont, hsupp, hunif, hnonneg, hdom, htend⟩

end DijProps

section GaussMom2

open MeasureTheory

private lemma euclid_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  have hnonneg : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc ‖x‖ ^ 2 = (√(∑ i, ‖x i‖ ^ 2)) ^ 2 := by rw [EuclideanSpace.norm_eq]
    _ = ∑ i, ‖x i‖ ^ 2 := Real.sq_sqrt hnonneg
    _ = ∑ i, (x i) ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]

private lemma int_gauss (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, Real.exp (-x ^ 2 / (4 * t)) = √(4 * Real.pi * t) := by
  have _ := ht
  have h1 : (fun x : ℝ => Real.exp (-x ^ 2 / (4 * t)))
      = (fun x : ℝ => Real.exp (-(4 * t)⁻¹ * x ^ 2)) := by
    congr with x
    congr 1
    rw [div_eq_mul_inv]
    ring
  rw [h1, integral_gaussian]
  congr 1
  rw [div_inv_eq_mul]
  ring

private lemma int_gauss_sq (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) = 2 * t * √(4 * Real.pi * t) := by
  have hsqrt_pos : (0:ℝ) < √(4 * Real.pi * t) := by positivity
  obtain ⟨v, hvc, hv0⟩ : ∃ v : NNReal, (v : ℝ) = 2 * t ∧ v ≠ 0 :=
    ⟨⟨2 * t, by positivity⟩, rfl, by
      intro h
      have h2 := congrArg (fun a : NNReal => (a : ℝ)) h
      have h2t : (2:ℝ) * t = 0 := h2
      linarith⟩
  have hvar := ProbabilityTheory.variance_fun_id_gaussianReal (μ := (0:ℝ)) (v := v)
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at hvar
  simp only [ProbabilityTheory.integral_id_gaussianReal, sub_zero] at hvar
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv0] at hvar
  have e1 : (2:ℝ) * Real.pi * (2 * t) = 4 * Real.pi * t := by ring
  have e2 : ∀ x : ℝ, (-(x - 0) ^ 2 / (2 * (2 * t))) = (-x ^ 2 / (4 * t)) := by
    intro x
    rw [sub_zero]
    congr 1
    ring
  have hfun : ∀ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x • x ^ 2
      = (√(4 * Real.pi * t))⁻¹ * (x ^ 2 * Real.exp (-x ^ 2 / (4 * t))) := by
    intro x
    rw [ProbabilityTheory.gaussianPDFReal_def]
    change ((√(2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ)))) • x ^ 2 = _
    rw [hvc, smul_eq_mul, e1, e2 x]
    ring
  simp_rw [hfun] at hvar
  rw [integral_const_mul, hvc] at hvar
  have hsqrt_ne : √(4 * Real.pi * t) ≠ 0 := ne_of_gt hsqrt_pos
  have h := congrArg (fun z => √(4 * Real.pi * t) * z) hvar
  simp only [← mul_assoc, mul_inv_cancel₀ hsqrt_ne, one_mul] at h
  calc (∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / (4 * t)))
      = √(4 * Real.pi * t) * 2 * t := h
    _ = 2 * t * √(4 * Real.pi * t) := by ring

private lemma intble_gauss (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (4 * t))) := by
  have h1 : (fun x : ℝ => Real.exp (-x ^ 2 / (4 * t)))
      = (fun x : ℝ => Real.exp (-(4 * t)⁻¹ * x ^ 2)) := by
    congr with x
    congr 1
    rw [div_eq_mul_inv]
    ring
  rw [h1]
  apply integrable_exp_neg_mul_sq
  positivity

private lemma intble_gauss_sq (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / (4 * t))) := by
  have hb : (0:ℝ) < (4 * t)⁻¹ := by positivity
  have h1 : (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / (4 * t)))
      = (fun x : ℝ => x ^ (2:ℝ) * Real.exp (-(4 * t)⁻¹ * x ^ 2)) := by
    congr with x
    rw [Real.rpow_two]
    congr 1
    congr 1
    rw [div_eq_mul_inv]
    ring
  rw [h1]
  exact integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)

private lemma prod_ite_eq_mul_pow (n : ℕ) (k : Fin n) (A B : ℝ) :
    (∏ l : Fin n, (if l = k then A else B)) = A * B ^ (n - 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [ite_eq_left rfl]
  have hz : ∀ x ∈ Finset.univ.erase k, (if x = k then A else B) = B := by
    intro x hx
    rw [ite_eq_right (Finset.mem_erase.mp hx).1]
  have hcongr : (∏ x ∈ Finset.univ.erase k, (if x = k then A else B))
      = ∏ x ∈ Finset.univ.erase k, B :=
    Finset.prod_congr rfl hz
  rw [hcongr, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k),
    Finset.card_univ, Fintype.card_fin]

private lemma gauss_factored (n : ℕ) (t : ℝ) (k : Fin n) (x : Fin n → ℝ) :
    Real.exp (-(∑ l, (x l)^2)/(4*t)) * (x k)^2
      = ∏ l, ((if l = k then (x l)^2 else 1) * Real.exp (-(x l)^2/(4*t))) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq_of_mem', Finset.mem_univ]
  rw [← Real.exp_sum]
  rw [mul_comm ((x k)^2) _]
  congr 1
  congr 1
  rw [← Finset.sum_neg_distrib, ← Finset.sum_div]

private lemma coord_second_moment (n : ℕ) (t : ℝ) (ht : 0 < t) (k : Fin n) :
    ∫ (x : Fin n → ℝ), ((4 * Real.pi * t) ^ (-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * (x k)^2
      = 2 * t := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  have hc : (0:ℝ) < 4 * Real.pi * t := by positivity
  have hfun : (fun x : Fin n → ℝ => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) *
    (x k)^2)
      = (fun x => (4*Real.pi*t)^(-(n:ℝ)/2) * ∏ l, ((if l = k then (x l)^2 else 1) * Real.exp (-(x
        l)^2/(4*t)))) := by
    funext x
    rw [mul_assoc, gauss_factored n t k x]
  rw [hfun, integral_const_mul,
    integral_fintype_prod_volume_eq_prod (f := fun l (u : ℝ) => (if l = k then u^2 else 1) *
      Real.exp (-u^2/(4*t)))]
  have hfactor : ∀ l : Fin n, (∫ u : ℝ, ((if l = k then u^2 else 1) * Real.exp (-u^2/(4*t))))
      = (if l = k then 2*t*√(4*Real.pi*t) else √(4*Real.pi*t)) := by
    intro l
    by_cases hl : l = k
    · simp only [ite_eq_left hl]
      exact int_gauss_sq t ht
    · simp only [ite_eq_right hl, one_mul]
      exact int_gauss t ht
  simp_rw [hfactor]
  rw [prod_ite_eq_mul_pow]
  have hBn : ∀ m : ℕ, (√(4*Real.pi*t))^m = (4*Real.pi*t)^((m:ℝ)/2) := by
    intro m
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    congr 1
    ring
  have hsqrt : √(4*Real.pi*t) = (4*Real.pi*t)^((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have hcast : ((n - 1 : ℕ):ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have hfinal : (4*Real.pi*t)^(-(n:ℝ)/2) * ((2*t*√(4*Real.pi*t)) * (√(4*Real.pi*t))^(n-1))
      = 2*t * ((4*Real.pi*t)^(-(n:ℝ)/2) * ((4*Real.pi*t)^((1:ℝ)/2) * (4*Real.pi*t)^(((n:ℝ)-1)/2)))
        := by
    rw [hBn (n-1), hsqrt, hcast]
    ring
  rw [hfinal, ← Real.rpow_add hc, ← Real.rpow_add hc]
  have hexp : (-(n:ℝ)/2 + ((1:ℝ)/2 + ((n:ℝ)-1)/2)) = 0 := by ring
  rw [hexp, Real.rpow_zero, mul_one]

private lemma transfer_heat (n : ℕ) (t : ℝ) (i j : Fin n) :
    (∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * t))) * |y i * y j|)
    = ∫ (x : Fin n → ℝ), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-(∑ l, (x l)^2) / (4 * t))) * |x i * x j| := by
  rw [← (PiLp.volume_preserving_toLp _).integral_comp (MeasurableEquiv.toLp 2
    _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  rw [euclid_norm_sq]

private lemma abs_mul_le_sq_add (a b : ℝ) : |a * b| ≤ (a^2 + b^2)/2 := by
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs, mul_assoc, ← abs_mul] at h
  linarith

private lemma intble_factored (n : ℕ) (t : ℝ) (ht : 0 < t) (k : Fin n) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-(∑ l, (x l)^2)/(4*t)) * (x k)^2) := by
  have hfun : (fun x : Fin n → ℝ => Real.exp (-(∑ l, (x l)^2)/(4*t)) * (x k)^2)
      = (fun x => ∏ l, ((if l = k then (x l)^2 else 1) * Real.exp (-(x l)^2/(4*t)))) := by
    funext x
    exact gauss_factored n t k x
  rw [hfun]
  apply Integrable.fintype_prod (f := fun l (u : ℝ) => (if l = k then u^2 else 1) * Real.exp
    (-u^2/(4*t)))
  intro l
  by_cases hl : l = k
  · simp only [ite_eq_left hl]
    exact intble_gauss_sq t ht
  · simp only [ite_eq_right hl, one_mul]
    exact intble_gauss t ht

/-- Heat-kernel cross-moment bound and tail second moment `o(t)`. -/
private theorem heatKernel_crossMoment_le (n : ℕ) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * t))) * |y i * y j| ≤ 2 * t := by
  rw [transfer_heat n t i j]
  have hCE : ∀ x : Fin n → ℝ, 0 ≤ (4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t)) := by
    intro x
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hle : (fun x : Fin n → ℝ => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) *
    |x i * x j|)
      ≤ (fun x => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * (((x i)^2+(x
        j)^2)/2)) := by
    intro x
    exact mul_le_mul_of_nonneg_left (abs_mul_le_sq_add _ _) (hCE x)
  have hfun2i : (fun x : Fin n → ℝ => (((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*t))) * (x i)^2))
      = (fun x => (4*Real.pi*t)^(-(n:ℝ)/2) * (Real.exp (-(∑ l, (x l)^2)/(4*t)) * (x i)^2)) := by
    funext x; ring
  have hfun2j : (fun x : Fin n → ℝ => (((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*t))) * (x j)^2))
      = (fun x => (4*Real.pi*t)^(-(n:ℝ)/2) * (Real.exp (-(∑ l, (x l)^2)/(4*t)) * (x j)^2)) := by
    funext x; ring
  have hHi : Integrable (fun x : Fin n → ℝ => (((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*t))) * (x i)^2)) := by
    rw [hfun2i]
    exact (intble_factored n t ht i).const_mul _
  have hHj : Integrable (fun x : Fin n → ℝ => (((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*t))) * (x j)^2)) := by
    rw [hfun2j]
    exact (intble_factored n t ht j).const_mul _
  have hfunG : (fun x : Fin n → ℝ => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t)))
    * (((x i)^2+(x j)^2)/2))
      = (fun x => (1/2) * ((((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * (x
        i)^2) + (((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * (x j)^2))) := by
    funext x; ring
  have hg : Integrable (fun x : Fin n → ℝ => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*t))) * (((x i)^2+(x j)^2)/2)) := by
    rw [hfunG]
    exact (hHi.add hHj).const_mul _
  have hFmeas : AEStronglyMeasurable (fun x : Fin n → ℝ => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
    (-(∑ l, (x l)^2)/(4*t))) * |x i * x j|) volume := by
    fun_prop
  have hf : Integrable (fun x : Fin n → ℝ => ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*t))) * |x i * x j|) :=
    Integrable.mono' hg hFmeas (ae_of_all _ (fun x => by
      have hFn : 0 ≤ ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * |x i * x j| :=
        mul_nonneg (hCE x) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hFn]
      exact hle x))
  have hval : (∫ x : Fin n → ℝ, ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) *
    (((x i)^2+(x j)^2)/2)) = 2*t := by
    rw [hfunG, integral_const_mul, integral_add hHi hHj, coord_second_moment n t ht i,
      coord_second_moment n t ht j]
    ring
  calc (∫ (x : Fin n → ℝ), ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * |x i * x
    j|)
      ≤ ∫ (x : Fin n → ℝ), ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*t))) * (((x
        i)^2+(x j)^2)/2) :=
        integral_mono hf hg hle
    _ = 2 * t := hval

private lemma intble_coord (n : ℕ) (s : ℝ) (hs : 0 < s) (k : Fin n) :
    Integrable (fun x : Fin n → ℝ => (((4*Real.pi*s)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*s)))
      * (x k)^2)) := by
  have hfun2 : (fun x : Fin n → ℝ => (((4*Real.pi*s)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*s)))
    * (x k)^2))
      = (fun x => (4*Real.pi*s)^(-(n:ℝ)/2) * (Real.exp (-(∑ l, (x l)^2)/(4*s)) * (x k)^2)) := by
    funext x; ring
  rw [hfun2]
  exact (intble_factored n s hs k).const_mul _

private lemma transfer_heat_sq (n : ℕ) (s : ℝ) :
    (∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * s) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * s))) * ‖y‖ ^ 2)
    = ∫ (x : Fin n → ℝ), ((4 * Real.pi * s) ^ (-(n : ℝ) / 2)
        * Real.exp (-(∑ l, (x l)^2) / (4 * s))) * (∑ k, (x k)^2) := by
  rw [← (PiLp.volume_preserving_toLp _).integral_comp (MeasurableEquiv.toLp 2
    _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  rw [euclid_norm_sq]

private lemma full_second_moment (n : ℕ) (s : ℝ) (hs : 0 < s) :
    (∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * s) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * s))) * ‖y‖ ^ 2) = 2 * (n:ℝ) * s := by
  rw [transfer_heat_sq n s]
  have hfun : (fun x : Fin n → ℝ => ((4*Real.pi*s)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*s))) *
    (∑ k, (x k)^2))
      = (fun x => ∑ k, (((4*Real.pi*s)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x l)^2)/(4*s))) * (x k)^2))
        := by
    funext x
    rw [Finset.mul_sum]
  rw [hfun, integral_finsetSum Finset.univ (fun k _ => intble_coord n s hs k)]
  simp_rw [coord_second_moment n s hs]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma intble_full_sq (n : ℕ) (s : ℝ) (hs : 0 < s) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => ((4*Real.pi*s)^(-(n:ℝ)/2) * Real.exp
      (-‖y‖^2/(4*s))) * ‖y‖^2) := by
  rw [← (PiLp.volume_preserving_toLp _).integrable_comp_emb (MeasurableEquiv.toLp 2
    _).measurableEmbedding]
  have h : Integrable (fun x : Fin n → ℝ => ∑ k, (((4*Real.pi*s)^(-(n:ℝ)/2) * Real.exp (-(∑ l, (x
    l)^2)/(4*s))) * (x k)^2)) :=
    integrable_finsetSum _ (fun k _ => intble_coord n s hs k)
  refine h.congr (ae_of_all _ (fun x => ?_))
  simp only [Function.comp_apply]
  rw [euclid_norm_sq, Finset.mul_sum]

private lemma heat_2t_eq_8t (n : ℕ) (t : ℝ) :
    (fun y : EuclideanSpace ℝ (Fin n) => ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) *
      ‖y‖^2)
    = (fun y => ((4*Real.pi*(2*t))^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(4*(2*t)))) * ‖y‖^2) := by
  have e1 : (8:ℝ)*Real.pi*t = 4*Real.pi*(2*t) := by ring
  have e2 : (8:ℝ)*t = 4*(2*t) := by ring
  funext y
  rw [e1, e2]

private lemma full_second_moment_8 (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (∫ (y : EuclideanSpace ℝ (Fin n)), ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2)
      = 2*(n:ℝ)*(2*t) := by
  rw [heat_2t_eq_8t n t]
  exact full_second_moment n (2*t) (by linarith)

private lemma intble_full_sq_8 (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
      (-‖y‖^2/(8*t))) * ‖y‖^2) := by
  rw [heat_2t_eq_8t n t]
  exact intble_full_sq n (2*t) (by linarith)

private lemma heat_norm_ratio (n : ℕ) (t : ℝ) (ht : 0 < t) :
    (4*Real.pi*t)^(-(n:ℝ)/2) = (2:ℝ)^((n:ℝ)/2) * (8*Real.pi*t)^(-(n:ℝ)/2) := by
  have h2 : (2:ℝ)^((n:ℝ)/2) * (2:ℝ)^(-(n:ℝ)/2) = 1 := by
    rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
    have hexp : (n:ℝ)/2 + (-(n:ℝ)/2) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have h8 : (8:ℝ)*Real.pi*t = 2*(4*Real.pi*t) := by ring
  rw [h8, Real.mul_rpow (show (0:ℝ) ≤ 2 by norm_num) (show (0:ℝ) ≤ 4*Real.pi*t by positivity),
    ← mul_assoc, h2, one_mul]

private lemma tail_pointwise (n : ℕ) (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : δ < ‖y‖) :
    ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(4*t))) * ‖y‖^2
      ≤ (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
        (-‖y‖^2/(8*t))) * ‖y‖^2) := by
  have hr2 : δ^2 < ‖y‖^2 := by
    have h1 : (0:ℝ) < ‖y‖ - δ := by linarith [hy]
    have h2 : (0:ℝ) < ‖y‖ + δ := by positivity
    nlinarith [mul_pos h1 h2]
  have h8t : (0:ℝ) < 8*t := by positivity
  have hexp_le : Real.exp (-‖y‖^2/(8*t)) ≤ Real.exp (-δ^2/(8*t)) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr h8t.le)
    linarith [hr2]
  have h4t : (4:ℝ)*t ≠ 0 := ne_of_gt (show (4:ℝ)*t > 0 by positivity)
  have h8t' : (8:ℝ)*t ≠ 0 := ne_of_gt (show (8:ℝ)*t > 0 by positivity)
  have hE : Real.exp (-‖y‖^2/(4*t)) = Real.exp (-‖y‖^2/(8*t)) * Real.exp (-‖y‖^2/(8*t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [← add_div, div_eq_div_iff h4t h8t']
    ring
  have hC := heat_norm_ratio n t ht
  have hK : (4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(4*t))
      ≤ (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
        (-‖y‖^2/(8*t))) := by
    have hK2t_nonneg : 0 ≤ (8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t)) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
    have hrpow_nonneg : 0 ≤ (2:ℝ)^((n:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
    calc (4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(4*t))
        = (2:ℝ)^((n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t)) * ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
          (-‖y‖^2/(8*t))) := by
          rw [hC, hE]; ring
      _ ≤ (2:ℝ)^((n:ℝ)/2) * Real.exp (-δ^2/(8*t)) * ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
        (-‖y‖^2/(8*t))) := by
          apply mul_le_mul_of_nonneg_right _ hK2t_nonneg
          exact mul_le_mul_of_nonneg_left hexp_le hrpow_nonneg
      _ = (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
        (-‖y‖^2/(8*t))) := by
          ring
  calc ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(4*t))) * ‖y‖^2
      ≤ ((Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
        (-‖y‖^2/(8*t)))) * ‖y‖^2 :=
        mul_le_mul_of_nonneg_right hK (sq_nonneg _)
    _ = (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
      (-‖y‖^2/(8*t))) * ‖y‖^2) := by
        ring

private lemma tail_bound (n : ℕ) (t δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) :
    (∫ (y : EuclideanSpace ℝ (Fin n)) in {y | δ < ‖y‖},
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * ‖y‖ ^ 2) / t
      ≤ Real.exp (-δ^2/(8*t)) * ((2:ℝ)^((n:ℝ)/2) * (4*(n:ℝ))) := by
  have hs_meas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hf_on : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => ((4*Real.pi*t)^(-(n:ℝ)/2) *
    Real.exp (-‖y‖^2/(4*t))) * ‖y‖^2) {y | δ < ‖y‖} :=
    (intble_full_sq n t ht).integrableOn
  have hg_on : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => (Real.exp (-δ^2/(8*t)) *
    (2:ℝ)^((n:ℝ)/2)) * (((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2)) {y | δ <
      ‖y‖} :=
    ((intble_full_sq_8 n t ht).const_mul _).integrableOn
  have hmono : (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, ((4*Real.pi*t)^(-(n:ℝ)/2) *
    Real.exp (-‖y‖^2/(4*t))) * ‖y‖^2)
      ≤ (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2))
        * (((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2)) :=
    setIntegral_mono_on hf_on hg_on hs_meas (fun y hy => tail_pointwise n t δ ht hδ y hy)
  have hg_eq : (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, (Real.exp (-δ^2/(8*t)) *
    (2:ℝ)^((n:ℝ)/2)) * (((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2))
      = (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ <
        ‖y‖}, ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2) :=
    integral_const_mul _ _
  have hext : (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, ((8*Real.pi*t)^(-(n:ℝ)/2) *
    Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2)
      ≤ (∫ y : EuclideanSpace ℝ (Fin n), ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) *
        ‖y‖^2) := by
    apply setIntegral_le_integral (intble_full_sq_8 n t ht)
    apply ae_of_all
    intro y
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
      (sq_nonneg _)
  have hfull := full_second_moment_8 n t ht
  have hD_nonneg : 0 ≤ Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _)
  have h1 : (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
    (-‖y‖^2/(4*t))) * ‖y‖^2)
      ≤ (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (2*(n:ℝ)*(2*t)) := by
    calc (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
      (-‖y‖^2/(4*t))) * ‖y‖^2)
        ≤ (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, (Real.exp (-δ^2/(8*t)) *
          (2:ℝ)^((n:ℝ)/2)) * (((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2)) :=
            hmono
      _ = (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ <
        ‖y‖}, ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2) := hg_eq
      _ ≤ (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (∫ y : EuclideanSpace ℝ (Fin n),
        ((8*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(8*t))) * ‖y‖^2) :=
          mul_le_mul_of_nonneg_left hext hD_nonneg
      _ = (Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (2*(n:ℝ)*(2*t)) := by rw [hfull]
  have h2 : (∫ y in {y : EuclideanSpace ℝ (Fin n) | δ < ‖y‖}, ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp
    (-‖y‖^2/(4*t))) * ‖y‖^2)/t
      ≤ ((Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (2*(n:ℝ)*(2*t)))/t := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr ht.le)
  have h3 : ((Real.exp (-δ^2/(8*t)) * (2:ℝ)^((n:ℝ)/2)) * (2*(n:ℝ)*(2*t)))/t
      = Real.exp (-δ^2/(8*t)) * ((2:ℝ)^((n:ℝ)/2) * (4*(n:ℝ))) := by
    rw [div_eq_iff (ne_of_gt ht)]
    ring
  rw [h3] at h2
  exact h2

private lemma tail_exp_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-δ^2/(8*t))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hneg : (-δ^2/8) < 0 := by
    have hpos : (0:ℝ) < δ^2/8 := by positivity
    linarith
  have h1 : Filter.Tendsto (fun t : ℝ => (-δ^2/8) * t⁻¹) (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg hneg tendsto_inv_nhdsGT_zero
  have h2 : ∀ t : ℝ, (-δ^2/(8*t)) = ((-δ^2/8) * t⁻¹) := by
    intro t
    rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
    ring
  have hfun : (fun t : ℝ => Real.exp (-δ^2/(8*t))) = (fun t => Real.exp (((-δ^2/8) * t⁻¹))) := by
    funext t
    rw [h2 t]
  rw [hfun]
  exact Real.tendsto_exp_atBot.comp h1

private theorem heatKernel_tail_secondMoment_div_tendsto (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun t : ℝ => (∫ (y : EuclideanSpace ℝ (Fin n)) in {y | δ < ‖y‖},
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
            * ‖y‖ ^ 2) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hG : Filter.Tendsto (fun t : ℝ => Real.exp (-δ^2/(8*t)) * ((2:ℝ)^((n:ℝ)/2) * (4*(n:ℝ))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (tail_exp_tendsto δ hδ).mul_const ((2:ℝ)^((n:ℝ)/2) * (4*(n:ℝ)))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Ioi] at ht
    have hInt : 0 ≤ (∫ (y : EuclideanSpace ℝ (Fin n)) in {y | δ < ‖y‖},
        ((4*Real.pi*t)^(-(n:ℝ)/2) * Real.exp (-‖y‖^2/(4*t))) * ‖y‖^2) := by
      apply integral_nonneg_of_ae
      apply ae_of_all
      intro y
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
        (sq_nonneg _)
    exact div_nonneg hInt ht.le
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Ioi] at ht
    exact tail_bound n t δ ht hδ

end GaussMom2


section LpEstNposHelpers

open MeasureTheory


private theorem coord_abs_le_norm (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |y i| ≤ ‖y‖ := by
  have h : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  rwa [Real.norm_eq_abs] at h

private theorem smul_norm_le_of_unit_interval (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ‖s • y‖ ≤ ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  calc s * ‖y‖ ≤ 1 * ‖y‖ :=
        mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
    _ = ‖y‖ := one_mul _

private theorem sum_abs_mul_le_norm_sq (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin n, ∑ j : Fin n, |y i * y j| ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2 := by
  have hcoord : ∀ i : Fin n, |y i| ≤ ‖y‖ := fun i => coord_abs_le_norm n y i
  calc ∑ i : Fin n, ∑ j : Fin n, |y i * y j|
      = ∑ i : Fin n, ∑ j : Fin n, (|y i| * |y j|) := by
        congr 1; ext i; congr 1; ext j; rw [abs_mul]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (‖y‖ * ‖y‖) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul (hcoord i) (hcoord j) (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) ^ 2 * ‖y‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

private theorem secondPartialModulus_mono_aux (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n)
    (hcont : Continuous (secondPartialFn n φ i j))
    (hsupp : HasCompactSupport (secondPartialFn n φ i j))
    {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hle : r₁ ≤ r₂) :
    secondPartialModulus n φ i j r₁ ≤ secondPartialModulus n φ i j r₂ := by
  have hBdd : ∃ M : ℝ, ∀ x : EuclideanSpace ℝ (Fin n),
      |secondPartialFn n φ i j x| ≤ M := by
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous hsupp hcont
    exact ⟨C, fun x => by have h := hC x; rwa [Real.norm_eq_abs] at h⟩
  unfold secondPartialModulus
  apply csSup_le_csSup
  · obtain ⟨M, hM⟩ := hBdd
    use 2 * |M|
    intro v hv
    obtain ⟨x, z, _, rfl⟩ := hv
    calc |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
        ≤ |secondPartialFn n φ i j (x - z)| + |secondPartialFn n φ i j x| :=
          abs_sub _ _
      _ ≤ M + M := add_le_add (hM _) (hM _)
      _ ≤ |M| + |M| := add_le_add (le_abs_self _) (le_abs_self _)
      _ = 2 * |M| := by ring
  · use 0, 0, 0
    constructor
    · simpa using hr₁
    · simp
  · intro v hv
    obtain ⟨x, z, hz, rfl⟩ := hv
    exact ⟨x, z, le_trans hz hle, rfl⟩

private theorem secondPartial_sub_le_modulus_aux (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n)
    (hcont : Continuous (secondPartialFn n φ i j))
    (hsupp : HasCompactSupport (secondPartialFn n φ i j))
    (hdom : ∀ (x z : EuclideanSpace ℝ (Fin n)),
      |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
        ≤ secondPartialModulus n φ i j ‖z‖)
    (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
      ≤ secondPartialModulus n φ i j ‖y‖ := by
  have hnorm : ‖s • y‖ ≤ ‖y‖ := smul_norm_le_of_unit_interval n y s hs0 hs1
  calc |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
      ≤ secondPartialModulus n φ i j ‖s • y‖ := hdom x (s • y)
    _ ≤ secondPartialModulus n φ i j ‖y‖ :=
        secondPartialModulus_mono_aux n φ i j hcont hsupp (norm_nonneg _) hnorm

end LpEstNposHelpers

section LpEstZero

open MeasureTheory


private theorem heatKernel_nonneg (n : ℕ) (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ Φ n t x :=
  (heatKernel_pos ht x).le


private theorem coord_mul_le_norm_sq (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    |y i * y j| ≤ ‖y‖ ^ 2 := by
  have hi : |y i| ≤ ‖y‖ := coord_abs_le_norm n y i
  have hj : |y j| ≤ ‖y‖ := coord_abs_le_norm n y j
  calc |y i * y j| = |y i| * |y j| := abs_mul _ _
    _ ≤ ‖y‖ * ‖y‖ := by gcongr
    _ = ‖y‖ ^ 2 := by ring

private theorem n_zero_case {p : ENNReal}
    (_hp1 : 1 ≤ p) (_hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    (hRemThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x
        = ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          * ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i))) :
    Filter.Tendsto
      (fun t : ℝ =>
        (eLpNorm (fun x => heatConvolution 0 φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hzero : ∀ t : ℝ, 0 < t →
      (fun x => heatConvolution 0 φ t x - φ x - t * Laplacian.laplacian φ x) = 0 := by
    intro t ht
    funext x
    have h := hRemThm 0 hφ hφ_supp ht x
    rw [h]
    simp
  have hfn : ∀ t : ℝ, 0 < t →
      (eLpNorm (fun x => heatConvolution 0 φ t x - φ x
        - t * Laplacian.laplacian φ x) p volume).toReal / t = 0 := by
    intro t ht
    rw [hzero t ht]
    simp
  have heq : (fun t : ℝ =>
      (eLpNorm (fun x => heatConvolution 0 φ t x - φ x
        - t * Laplacian.laplacian φ x) p volume).toReal / t)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_Ioi] at ht
    exact hfn t ht
  rw [Filter.tendsto_congr' heq]
  exact tendsto_const_nhds

end LpEstZero

section JensenLp

open MeasureTheory

/-- Jensen for `∫⁻`: for a probability measure `μ`, the `p`-th power of the
norm of an integral is at most the integral of the `p`-th powers. -/
private theorem lintegral_norm_integral_le {n : ℕ} {p : ℝ} (hp1 : 1 ≤ p)
    {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF_meas : AEStronglyMeasurable (Function.uncurry F) (μ.prod volume))
    (hF_int : Integrable (Function.uncurry F) (μ.prod volume)) :
    ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ p) ∂volume
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ p) ∂volume ∂μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp1
  have hpne : p ≠ 0 := by linarith
  have hslice : ∀ᵐ y ∂volume, Integrable (fun x => F x y) μ := hF_int.prod_left_ae
  have hpoint : ∀ᵐ y ∂volume, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ p)
      ≤ ∫⁻ x, ENNReal.ofReal (‖F x y‖ ^ p) ∂μ := by
    filter_upwards [hslice] with y hy
    have hnorm : ‖∫ x, F x y ∂μ‖ ≤ (∫⁻ x, ENNReal.ofReal ‖F x y‖ ∂μ).toReal :=
      norm_integral_le_lintegral_norm _
    have hofReal_le : ENNReal.ofReal ‖∫ x, F x y ∂μ‖
        ≤ ∫⁻ x, ENNReal.ofReal ‖F x y‖ ∂μ :=
      (ENNReal.ofReal_le_ofReal hnorm).trans ENNReal.ofReal_toReal_le
    have hmeas : AEMeasurable (fun x => ENNReal.ofReal ‖F x y‖) μ :=
      hy.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
    rcases eq_or_lt_of_le hp1 with rfl | hp1'
    · simp only [Real.rpow_one]
      exact hofReal_le
    · have hconj : p.HolderConjugate p.conjExponent :=
        Real.HolderConjugate.conjExponent hp1'
      have hone : AEMeasurable (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ENNReal)) μ :=
        aemeasurable_const
      have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hmeas hone
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one, measure_univ,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0] at hH
      have hle := hofReal_le.trans hH
      have hpow := ENNReal.rpow_le_rpow hle hp0
      rw [← ENNReal.rpow_mul, div_mul_cancel₀ 1 hpne, ENNReal.rpow_one] at hpow
      have hgoal : ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ p)
          = (ENNReal.ofReal ‖∫ x, F x y ∂μ‖) ^ p :=
        (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0).symm
      rw [hgoal]
      exact hpow
  have hcont : Continuous (fun r : ℝ => ‖r‖ ^ p) :=
    continuous_norm.rpow_const (fun _ => Or.inr hp0)
  have hmeas_outer : Measurable (fun r : ℝ => ENNReal.ofReal (‖r‖ ^ p)) :=
    hcont.measurable.ennreal_ofReal
  have hmeas_prod : AEMeasurable
      (Function.uncurry fun x y => ENNReal.ofReal (‖F x y‖ ^ p)) (μ.prod volume) :=
    hmeas_outer.comp_aemeasurable hF_meas.aemeasurable
  have hswap := lintegral_lintegral_swap (μ := μ) (ν := volume)
    (f := fun x y => ENNReal.ofReal (‖F x y‖ ^ p)) hmeas_prod
  calc ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ p) ∂volume
      ≤ ∫⁻ y, (∫⁻ x, ENNReal.ofReal (‖F x y‖ ^ p) ∂μ) ∂volume :=
        lintegral_mono_ae hpoint
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ p) ∂volume ∂μ := hswap.symm

end JensenLp

section LemmaA

open MeasureTheory


private theorem volume_ball_euclidean_le (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      ≤ ENNReal.ofReal ((2 * r) ^ n) := by
  let a' : Fin n → ℝ := fun _ => -r
  let b' : Fin n → ℝ := fun _ => r
  let a : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a'
  let b : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b'
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Set.Icc a b := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    constructor
    · show a ≤ x
      change WithLp.toLp 2 a' ≤ x
      change a' ≤ WithLp.ofLp x
      intro i
      change a' i ≤ (WithLp.ofLp x) i
      have h1 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h1
      have h2 : -‖x‖ ≤ x i := neg_le_of_abs_le h1
      have h3 : -r ≤ -‖x‖ := by linarith
      have ha'i : a' i = -r := rfl
      have heq : (WithLp.ofLp x) i = x i := rfl
      rw [ha'i, heq]
      linarith
    · show x ≤ b
      change x ≤ WithLp.toLp 2 b'
      change WithLp.ofLp x ≤ b'
      intro i
      change (WithLp.ofLp x) i ≤ b' i
      have h1 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
      rw [Real.norm_eq_abs] at h1
      have h2 : x i ≤ ‖x‖ := le_of_abs_le h1
      have hb'i : b' i = r := rfl
      have heq : (WithLp.ofLp x) i = x i := rfl
      rw [hb'i, heq]
      linarith
  have hvol_eq : volume (Set.Icc a b) = volume (Set.Icc a' b') := by
    have hpres := PiLp.volume_preserving_toLp (Fin n)
    have hemb := MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    have heq : ⇑(MeasurableEquiv.toLp 2 (Fin n → ℝ)) = WithLp.toLp 2 := rfl
    rw [heq] at hemb
    have h := hpres.measure_preimage_emb hemb (Set.Icc a b)
    have hpre : WithLp.toLp 2 ⁻¹' (Set.Icc a b) = Set.Icc a' b' := rfl
    rw [hpre] at h
    exact h.symm
  calc volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      ≤ volume (Set.Icc a b) := measure_mono hsub
    _ = volume (Set.Icc a' b') := hvol_eq
    _ = ∏ i, ENNReal.ofReal (b' i - a' i) := Real.volume_Icc_pi
    _ = ENNReal.ofReal ((2 * r) ^ n) := by
        trans ∏ _i : Fin n, ENNReal.ofReal (2 * r)
        · apply Finset.prod_congr rfl
          intro i _
          congr 1
          show b' i - a' i = 2 * r
          have hb : b' i = r := rfl
          have ha : a' i = -r := rfl
          rw [hb, ha]
          ring
        · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2 * r)]

private theorem per_fun_bound (n : ℕ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hcont : Continuous f)
    (M R0 : ℝ) (hM0 : 0 ≤ M) (hR0 : 0 ≤ R0)
    (hM : ∀ x, ‖f x‖ ≤ M)
    (hK : closure (Function.support f) ⊆ Metric.ball 0 R0)
    (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (modv : ℝ) (hmod0 : 0 ≤ modv)
    (hmod : ∀ x : EuclideanSpace ℝ (Fin n), |f (x - s • y) - f x| ≤ modv) :
    ∫⁻ x, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume
      ≤ ENNReal.ofReal (((2:ℝ) ^ n * (2 * M) ^ (p.toReal - 1)) * modv * (R0 + ‖y‖) ^ n) := by
  -- Setup q
  have hne : p ≠ ⊤ := ne_of_lt hp
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hne hp1
    rw [ENNReal.toReal_one] at h
    exact h
  have hq0 : 0 ≤ p.toReal := by linarith
  have hqpos : 0 < p.toReal := by linarith
  have hqm1 : 0 ≤ p.toReal - 1 := by linarith
  -- B = 2*M
  set B : ℝ := 2 * M with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hBpow0 : 0 ≤ B ^ (p.toReal - 1) := Real.rpow_nonneg hB0 _
  -- r and s_set
  set r : ℝ := R0 + ‖y‖ with hrdef
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hr0 : 0 ≤ r := by positivity
  set sset : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 r with hsset
  have hsmeas : MeasurableSet sset := measurableSet_ball
  -- Measurability of integrand
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal) := by
    have hsub : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x - s • y) :=
      continuous_id.sub continuous_const
    have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin n) => f (x - s • y)) :=
      hcont.comp hsub
    have h2 : Continuous (fun x : EuclideanSpace ℝ (Fin n) => f (x - s • y) - f x) :=
      h1.sub hcont
    have h3 : Continuous (fun x : EuclideanSpace ℝ (Fin n) => ‖f (x - s • y) - f x‖) :=
      h2.norm
    have h4 : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ‖f (x - s • y) - f x‖) :=
      ENNReal.continuous_ofReal.comp h3
    have h5 : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal) :=
      ENNReal.continuous_rpow_const.comp h4
    exact h5.measurable
  -- Vanishing outside
  have hvan : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ sset → f x = 0 ∧ f (x - s • y) = 0 := by
    intro x hx
    have hR0r : R0 ≤ r := by simp only [hrdef]; linarith
    have hball_sub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R0 ⊆ sset :=
      Metric.ball_subset_ball hR0r
    have hKsub : closure (Function.support f) ⊆ sset := hK.trans hball_sub
    have hsmy_le : ‖s • y‖ ≤ ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      calc s * ‖y‖ ≤ 1 * ‖y‖ := by apply mul_le_mul_of_nonneg_right hs1 hy0
        _ = ‖y‖ := one_mul _
    constructor
    · have hxK : x ∉ closure (Function.support f) := fun h => hx (hKsub h)
      have hxsupp : x ∉ Function.support f := fun h => hxK (subset_closure h)
      exact Function.notMem_support.mp hxsupp
    · have hmem : x - s • y ∉ closure (Function.support f) := by
        intro hcon
        have hball : x - s • y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R0 := hK hcon
        rw [Metric.mem_ball, dist_zero_right] at hball
        have htri : ‖x‖ ≤ ‖x - s • y‖ + ‖s • y‖ := by
          conv_lhs => rw [← sub_add_cancel x (s • y)]
          exact norm_add_le _ _
        have hlt : ‖x - s • y‖ + ‖s • y‖ < R0 + ‖y‖ :=
          add_lt_add_of_lt_of_le hball hsmy_le
        have hxball : ‖x‖ < r := by simp [hrdef]; linarith
        have hxmem : x ∈ sset := by
          rw [Metric.mem_ball, dist_zero_right]
          exact hxball
        exact hx hxmem
      have hsupp : x - s • y ∉ Function.support f := fun h => hmem (subset_closure h)
      exact Function.notMem_support.mp hsupp
  -- Integrand zero outside
  have hzero_out : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ ssetᶜ →
      ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal = 0 := by
    intro x hx
    rw [Set.mem_compl_iff] at hx
    obtain ⟨hfx, hfxs⟩ := hvan x hx
    rw [hfxs, hfx, sub_zero, norm_zero, ENNReal.ofReal_zero]
    exact ENNReal.zero_rpow_of_pos hqpos
  -- Complement integral is 0
  have hcompl_zero : ∫⁻ x in ssetᶜ, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume = 0 :=
    by
    rw [(setLIntegral_eq_zero_iff hsmeas.compl hmeas).mpr]
    filter_upwards with x hx
    exact hzero_out x hx
  -- Split
  have hsplit : ∫⁻ x, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume
      = ∫⁻ x in sset, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume := by
    have h : (∫⁻ x in sset, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume)
        + (∫⁻ x in ssetᶜ, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume)
        = ∫⁻ x, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume :=
      lintegral_add_compl _ hsmeas
    rw [hcompl_zero, add_zero] at h
    exact h.symm
  rw [hsplit]
  -- Pointwise bound: for all x, integrand ≤ ofReal (B^(q-1) * modv)
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal
        ≤ ENNReal.ofReal (B ^ (p.toReal - 1) * modv) := by
    intro x
    have hd0 : 0 ≤ ‖f (x - s • y) - f x‖ := norm_nonneg _
    rw [ENNReal.ofReal_rpow_of_nonneg hd0 hq0]
    apply ENNReal.ofReal_le_ofReal
    -- Need ‖diff‖^q ≤ B^(q-1)*modv
    -- |diff| = ‖diff‖?
    have hnorm_abs : ‖f (x - s • y) - f x‖ = |f (x - s • y) - f x| := Real.norm_eq_abs _
    have hdB : ‖f (x - s • y) - f x‖ ≤ B := by
      rw [hnorm_abs]
      have h1 : |f (x - s • y)| ≤ M := by
        have h := hM (x - s • y)
        rwa [Real.norm_eq_abs] at h
      have h2 : |f x| ≤ M := by
        have h := hM x
        rwa [Real.norm_eq_abs] at h
      calc |f (x - s • y) - f x| ≤ |f (x - s • y)| + |f x| := abs_sub _ _
        _ ≤ M + M := add_le_add h1 h2
        _ = B := by simp [hBdef]; ring
    have hdmod : ‖f (x - s • y) - f x‖ ≤ modv := by
      rw [hnorm_abs]
      exact hmod x
    -- rpow bound
    have hstep : ‖f (x - s • y) - f x‖ ^ p.toReal ≤ B ^ (p.toReal - 1) * ‖f (x - s • y) - f x‖ := by
      by_cases hd : ‖f (x - s • y) - f x‖ = 0
      · rw [hd, Real.zero_rpow (ne_of_gt hqpos), mul_zero]
      · have hdpos : 0 < ‖f (x - s • y) - f x‖ := lt_of_le_of_ne hd0 (Ne.symm hd)
        have hqeq : p.toReal = (p.toReal - 1) + 1 := by ring
        conv_lhs => rw [hqeq]
        rw [Real.rpow_add hdpos, Real.rpow_one]
        have hpow : ‖f (x - s • y) - f x‖ ^ (p.toReal - 1) ≤ B ^ (p.toReal - 1) :=
          Real.rpow_le_rpow hd0 hdB hqm1
        exact mul_le_mul_of_nonneg_right hpow hd0
    calc ‖f (x - s • y) - f x‖ ^ p.toReal
        ≤ B ^ (p.toReal - 1) * ‖f (x - s • y) - f x‖ := hstep
      _ ≤ B ^ (p.toReal - 1) * modv := by
          apply mul_le_mul_of_nonneg_left hdmod hBpow0
  -- Integral over sset ≤ const * volume
  have hle : ∫⁻ x in sset, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume
      ≤ ENNReal.ofReal (B ^ (p.toReal - 1) * modv) * volume sset := by
    have h : (∫⁻ x in sset, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume)
        ≤ (∫⁻ _ in sset, ENNReal.ofReal (B ^ (p.toReal - 1) * modv) ∂volume) :=
      setLIntegral_mono measurable_const (fun x _ => hpt x)
    rw [setLIntegral_const] at h
    exact h
  -- Volume bound
  have hvol : volume sset ≤ ENNReal.ofReal ((2 * r) ^ n) := volume_ball_euclidean_le n r hr0
  -- Combine
  calc ∫⁻ x in sset, ENNReal.ofReal ‖f (x - s • y) - f x‖ ^ p.toReal ∂volume
      ≤ ENNReal.ofReal (B ^ (p.toReal - 1) * modv) * volume sset := hle
    _ ≤ ENNReal.ofReal (B ^ (p.toReal - 1) * modv) * ENNReal.ofReal ((2 * r) ^ n) := by
        exact mul_le_mul_right hvol _
    _ = ENNReal.ofReal ((B ^ (p.toReal - 1) * modv) * ((2 * r) ^ n)) := by
        have hnn : 0 ≤ B ^ (p.toReal - 1) * modv := mul_nonneg hBpow0 hmod0
        rw [ENNReal.ofReal_mul hnn]
    _ = ENNReal.ofReal (((2:ℝ) ^ n * B ^ (p.toReal - 1)) * modv * r ^ n) := by
        congr 1
        have hpow : (2 * r) ^ n = (2:ℝ) ^ n * r ^ n := mul_pow 2 r n
        rw [hpow]
        ring
    _ = ENNReal.ofReal (((2:ℝ) ^ n * (2 * M) ^ (p.toReal - 1)) * modv * (R0 + ‖y‖) ^ n) := by
        simp only [hBdef, hrdef]

private theorem lintegral_diff_le (n : ℕ) (hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p)
    (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      (∀ (x z : EuclideanSpace ℝ (Fin n)),
        |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖z‖) →
      ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
      |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
        ≤ secondPartialModulus n φ i j ‖y‖) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ (i j : Fin n) (y : EuclideanSpace ℝ (Fin n))
      (s : ℝ), 0 ≤ s → s ≤ 1 →
      ∫⁻ x, ENNReal.ofReal
        ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
        ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n) := by
  have _ := hn
  have _ := hφ
  have _ := hφ_supp
  have hMR : ∀ i j : Fin n, ∃ M R0 : ℝ, 0 ≤ M ∧ 0 ≤ R0 ∧
      (∀ x, ‖secondPartialFn n φ i j x‖ ≤ M) ∧
      closure (Function.support (secondPartialFn n φ i j)) ⊆ Metric.ball 0 R0 := by
    intro i j
    obtain ⟨hcont, hsupp, _, _, _, _⟩ := hDijThm i j
    obtain ⟨M0, hM0⟩ := hsupp.exists_bound_of_continuous hcont
    obtain ⟨r0, hr0⟩ := (hasCompactSupport_def.mp hsupp).isBounded.subset_ball
      (0 : EuclideanSpace ℝ (Fin n))
    exact ⟨max M0 0, max r0 0, le_max_right _ _, le_max_right _ _,
      fun x => le_trans (hM0 x) (le_max_left _ _),
      hr0.trans (Metric.ball_subset_ball (le_max_left _ _))⟩
  choose Mfun Rfun hM0 hR0 hM hK using hMR
  refine ⟨∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)),
    ∑ i, ∑ j, Rfun i j, ?_, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (pow_nonneg (by norm_num) n)
    exact Real.rpow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hM0 i j)) _
  · apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact hR0 i j
  · intro i j y s hs0 hs1
    obtain ⟨hcont, hsupp, _, hmod0_all, hmod_all, _⟩ := hDijThm i j
    have hmod0 : 0 ≤ secondPartialModulus n φ i j ‖y‖ := hmod0_all ‖y‖
    have hmod : ∀ x : EuclideanSpace ℝ (Fin n),
        |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖y‖ :=
      fun x => hSubThm n i j hcont hsupp hmod_all x y s hs0 hs1
    have hper := per_fun_bound n hp1 hp (secondPartialFn n φ i j) hcont
      (Mfun i j) (Rfun i j) (hM0 i j) (hR0 i j) (hM i j) (hK i j)
      y s hs0 hs1 (secondPartialModulus n φ i j ‖y‖) hmod0 hmod
    have hCij0 : 0 ≤ (2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1) :=
      mul_nonneg (pow_nonneg (by norm_num) n)
        (Real.rpow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hM0 i j)) _)
    have hCijC : (2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)
        ≤ ∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)) := by
      have h1 : (2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)
          ≤ ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)) := by
        apply Finset.single_le_sum _ (Finset.mem_univ j)
        intro j' _
        exact mul_nonneg (pow_nonneg (by norm_num) n)
          (Real.rpow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hM0 i j')) _)
      have h2 : (∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)))
          ≤ ∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)) := by
        apply Finset.single_le_sum _ (Finset.mem_univ i)
        intro i' _
        apply Finset.sum_nonneg
        intro j' _
        exact mul_nonneg (pow_nonneg (by norm_num) n)
          (Real.rpow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hM0 i' j')) _)
      exact le_trans h1 h2
    have hRijR : Rfun i j ≤ ∑ i, ∑ j, Rfun i j := by
      have h1 : Rfun i j ≤ ∑ j, Rfun i j :=
        Finset.single_le_sum (fun j' _ => hR0 i j') (Finset.mem_univ j)
      have h2 : (∑ j, Rfun i j) ≤ ∑ i, ∑ j, Rfun i j := by
        apply Finset.single_le_sum _ (Finset.mem_univ i)
        intro i' _
        apply Finset.sum_nonneg
        intro j' _
        exact hR0 i' j'
      exact le_trans h1 h2
    have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
    have hr0le : Rfun i j + ‖y‖ ≤ (∑ i, ∑ j, Rfun i j) + ‖y‖ :=
      add_le_add_left hRijR _
    have hr00 : 0 ≤ Rfun i j + ‖y‖ := add_nonneg (hR0 i j) hy0
    have hpow : (Rfun i j + ‖y‖) ^ n ≤ ((∑ i, ∑ j, Rfun i j) + ‖y‖) ^ n :=
      pow_le_pow_left₀ hr00 hr0le n
    have hCmod : ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1))
        * secondPartialModulus n φ i j ‖y‖
        ≤ (∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)))
        * secondPartialModulus n φ i j ‖y‖ :=
      mul_le_mul_of_nonneg_right hCijC hmod0
    have hmono : ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1))
        * secondPartialModulus n φ i j ‖y‖ * (Rfun i j + ‖y‖) ^ n
        ≤ (∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)))
        * secondPartialModulus n φ i j ‖y‖
        * ((∑ i, ∑ j, Rfun i j) + ‖y‖) ^ n := by
      have hpow0 : 0 ≤ (Rfun i j + ‖y‖) ^ n := pow_nonneg hr00 n
      have hC0 : 0 ≤ ∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)) := by
        apply Finset.sum_nonneg
        intro i' _
        apply Finset.sum_nonneg
        intro j' _
        exact mul_nonneg (pow_nonneg (by norm_num) n)
          (Real.rpow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hM0 i' j')) _)
      have hCmod0 : 0 ≤ (∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)))
          * secondPartialModulus n φ i j ‖y‖ := mul_nonneg hC0 hmod0
      have h := mul_le_mul hCmod hpow hpow0 hCmod0
      simpa [mul_assoc] using h
    calc ∫⁻ x, ENNReal.ofReal
          ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
        ≤ ENNReal.ofReal (((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1))
          * secondPartialModulus n φ i j ‖y‖ * (Rfun i j + ‖y‖) ^ n) := hper
      _ ≤ ENNReal.ofReal ((∑ i, ∑ j, ((2:ℝ) ^ n * (2 * Mfun i j) ^ (p.toReal - 1)))
          * secondPartialModulus n φ i j ‖y‖
          * ((∑ i, ∑ j, Rfun i j) + ‖y‖) ^ n) :=
        ENNReal.ofReal_le_ofReal hmono

end LemmaA

section C1

open MeasureTheory Filter
open scoped Topology Pointwise


local instance : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_lt_top]⟩

/-- Integration against the Gaussian density measure is the weighted volume integral. -/
private theorem Dfn_integral_density (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M) :
    ∀ (t : ℝ), 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
        (Φ n t y)))
      = ∫ y, Φ n t y * Dfn n φ x y := by
  -- `integral_withDensity_eq_integral_smul` needs no integrability, so the
  -- regularity hypotheses are unneeded; reference them to silence the linter.
  have _ := hDijThm
  have _ := hBndThm
  intro t ht x
  have hKcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y) := by
    unfold heatKernel
    fun_prop
  have hKmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) => Real.toNNReal (Φ n t y)) :=
    hKcont.measurable.real_toNNReal
  have hKnonneg : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ Φ n t y := by
    intro y
    unfold heatKernel
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact (Real.exp_pos _).le
  simp only [← ENNReal.ofNNReal_toNNReal]
  rw [integral_withDensity_eq_integral_smul hKmeas]
  apply integral_congr_ae
  filter_upwards with y
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hKnonneg y)]

private theorem Dfn_integral_measurable (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M)
    (hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0)) :
    ∀ (t : ℝ), 0 < t → AEStronglyMeasurable
      (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Φ n t y))) volume := by
  intro t ht
  have hCont : ∀ i j, Continuous (secondPartialFn n φ i j) :=
    fun i j => (hDijThm i j).1
  have hSupp : ∀ i j, HasCompactSupport (secondPartialFn n φ i j) :=
    fun i j => (hDijThm i j).2.1
  have hEx : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M :=
    fun i j => hBndThm n i j (hCont i j) (hSupp i j)
  choose M hM0 hM using hEx
  set Mtot : ℝ := ∑ i, ∑ j, M i j with hMtotDef
  have hMtot0 : 0 ≤ Mtot :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hM0 i j
  have hMle : ∀ i j, M i j ≤ Mtot := by
    intro i j
    calc M i j ≤ ∑ j', M i j' :=
          Finset.single_le_sum (fun j' _ => hM0 i j') (Finset.mem_univ j)
      _ ≤ Mtot :=
          Finset.single_le_sum
            (fun i' _ => Finset.sum_nonneg fun j' _ => hM0 i' j')
            (Finset.mem_univ i)
  have hDijBnd : ∀ i j x, |secondPartialFn n φ i j x| ≤ Mtot :=
    fun i j x => (hM i j x).trans (hMle i j)
  set C : ℝ := 2 * (n : ℝ) ^ 2 * Mtot with hCDef
  have hC0 : 0 ≤ C := by
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := mul_nonneg (by norm_num) hn2
    rw [hCDef]
    exact mul_nonneg h2 hMtot0
  have hxCont : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
    ps.1.1) :=
    continuous_fst.comp continuous_fst
  have hyCont : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
    ps.1.2) :=
    continuous_snd.comp continuous_fst
  have hsCont : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
    ps.2) :=
    continuous_snd
  have hSubCont : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
    ps.1.1 - ps.2 • ps.1.2) :=
    hxCont.sub (hsCont.smul hyCont)
  have hfUncurry : Continuous (Function.uncurry
      (fun (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) (s : ℝ) =>
        (1 - s) * ∑ i, ∑ j, p.2 i * p.2 j *
          (secondPartialFn n φ i j (p.1 - s • p.2) - secondPartialFn n φ i j p.1))) := by
    unfold Function.uncurry
    apply Continuous.mul
    · exact continuous_const.sub continuous_snd
    · apply continuous_finsetSum _ fun i _ => ?_
      apply continuous_finsetSum _ fun j _ => ?_
      have hyi : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
        ps.1.2 i) := by
        fun_prop
      have hyj : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
        ps.1.2 j) := by
        fun_prop
      have hD1 : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
          secondPartialFn n φ i j (ps.1.1 - ps.2 • ps.1.2)) :=
        (hCont i j).comp hSubCont
      have hD2 : Continuous (fun ps : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ =>
          secondPartialFn n φ i j ps.1.1) :=
        (hCont i j).comp hxCont
      exact (hyi.mul hyj).mul (hD1.sub hD2)
  have hDfnCont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => Dfn n
    φ p.1 p.2) := by
    have hEq : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => Dfn n φ p.1 p.2)
        = (fun p => ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, p.2 i * p.2 j *
          (secondPartialFn n φ i j (p.1 - s • p.2) - secondPartialFn n φ i j p.1)) := by
      funext p
      simp only [Dfn]
    rw [hEq]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfUncurry 0 1
  have hContX : ∀ (y : EuclideanSpace ℝ (Fin n)), Continuous (fun x => Dfn n φ x y) := by
    intro y
    have hInner : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (x, y)) :=
      continuous_id.prodMk continuous_const
    have h2 := hDfnCont.comp hInner
    simpa [Function.comp_def] using h2
  have hContY : ∀ (x : EuclideanSpace ℝ (Fin n)), Continuous (fun y => Dfn n φ x y) := by
    intro x
    have hInner : Continuous (fun y : EuclideanSpace ℝ (Fin n) => (x, y)) :=
      continuous_const.prodMk continuous_id
    have h2 := hDfnCont.comp hInner
    simpa [Function.comp_def] using h2
  have hFmeas : ∀ x, AEStronglyMeasurable (fun y => Dfn n φ x y)
      (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
    fun x => (hContY x).aestronglyMeasurable
  have hContAE : ∀ᵐ y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
    (Φ n t y)),
      Continuous fun x => Dfn n φ x y :=
    Filter.Eventually.of_forall fun y => hContX y
  have hyi_le : ∀ (y : EuclideanSpace ℝ (Fin n)) (i : Fin n), |y i| ≤ ‖y‖ := by
    intro y i
    have h := PiLp.norm_apply_le y i
    rwa [Real.norm_eq_abs] at h
  have hBoundPt : ∀ (x y : EuclideanSpace ℝ (Fin n)), ‖Dfn n φ x y‖ ≤ C * ‖y‖ ^ 2 := by
    intro x y
    have hNorm : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
        ‖(1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤ C * ‖y‖ ^ 2 := by
      intro s hs
      have hs01 : s ∈ Set.Ioc (0 : ℝ) 1 := by
        have h01 : (0 : ℝ) ≤ 1 := by norm_num
        rwa [Set.uIoc_of_le h01] at hs
      obtain ⟨hs0, hs1⟩ := hs01
      have h1s : ‖(1 - s : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs]
        have hnn : (0 : ℝ) ≤ 1 - s := by linarith
        rw [abs_of_nonneg hnn]
        linarith
      have hTerm : ∀ i j, ‖y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
          ≤ ‖y‖ ^ 2 * (2 * Mtot) := by
        intro i j
        have hAbsSub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
          intro a b
          calc |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
            _ ≤ |a| + |-b| := abs_add_le _ _
            _ = |a| + |b| := by rw [abs_neg]
        have hdiff : |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x| ≤ 2 * Mtot
          := by
          calc |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
              ≤ |secondPartialFn n φ i j (x - s • y)| + |secondPartialFn n φ i j x| := hAbsSub _ _
            _ ≤ Mtot + Mtot := add_le_add (hDijBnd i j _) (hDijBnd i j _)
            _ = 2 * Mtot := by ring
        calc ‖y i * y j * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
            = |y i| * |y j| * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x| :=
              by
              simp [Real.norm_eq_abs]
          _ ≤ ‖y‖ * ‖y‖ * (2 * Mtot) := by
              apply mul_le_mul (mul_le_mul (hyi_le y i) (hyi_le y j) (abs_nonneg _) (norm_nonneg _))
                hdiff (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = ‖y‖ ^ 2 * (2 * Mtot) := by ring
      have hSum : ‖∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤ C * ‖y‖ ^ 2 := by
        calc ‖∑ i, ∑ j, y i * y j * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j
          x)‖
            ≤ ∑ i, ‖∑ j, y i * y j * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j
              x)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ i, ∑ j, (‖y‖ ^ 2 * (2 * Mtot)) := by
              apply Finset.sum_le_sum
              intro i _
              calc ‖∑ j, y i * y j * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j
                x)‖
                  ≤ ∑ j, ‖y i * y j * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i
                    j x)‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ j, (‖y‖ ^ 2 * (2 * Mtot)) :=
                    Finset.sum_le_sum fun j _ => hTerm i j
          _ = C * ‖y‖ ^ 2 := by
              simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hCDef]
              ring
      calc ‖(1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
          = ‖(1 - s : ℝ)‖ * ‖∑ i, ∑ j, y i * y j *
            (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ := norm_mul _ _
        _ ≤ 1 * (C * ‖y‖ ^ 2) := mul_le_mul h1s hSum (norm_nonneg _) (by norm_num)
        _ = C * ‖y‖ ^ 2 := one_mul _
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const hNorm
    simp only [Dfn] at hInt ⊢
    calc ‖∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
        ≤ (C * ‖y‖ ^ 2) * |1 - 0| := hInt
      _ = C * ‖y‖ ^ 2 := by simp
  have hBoundEv : ∀ x, ∀ᵐ y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
    (Φ n t y)),
      ‖Dfn n φ x y‖ ≤ C * ‖y‖ ^ 2 :=
    fun x => Filter.Eventually.of_forall fun y => hBoundPt x y
  have hBasePos : (0 : ℝ) < 4 * Real.pi * t := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  have hHeatNonneg : ∀ y, 0 ≤ Φ n t y := by
    intro y
    unfold heatKernel
    apply mul_nonneg
    · exact Real.rpow_nonneg (le_of_lt hBasePos) _
    · exact le_of_lt (Real.exp_pos _)
  have hHeatCont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y) := by
    unfold heatKernel
    apply Continuous.mul continuous_const
    apply Real.continuous_exp.comp
    apply Continuous.div
    · continuity
    · exact continuous_const
    · intro y
      have h4t : (0 : ℝ) < 4 * t := by positivity
      exact ne_of_gt h4t
  have hDiagInt : ∀ i, Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y * (y i * y i)) volume := by
    intro i
    have h3 : (∫ y : EuclideanSpace ℝ (Fin n),
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i))
        = 2 * t := by
      have h := (hMomThm n ht).2.2 i i
      simpa using h
    have ht2 : (2 : ℝ) * t ≠ 0 := ne_of_gt (by positivity)
    have hRHSInt : Integrable
        (fun y : EuclideanSpace ℝ (Fin n) =>
          ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i))
        volume := by
      by_contra hni
      have h0 := integral_undef hni
      rw [h3] at h0
      exact ht2 h0
    have hEq : (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y * (y i * y i))
        = (fun y => ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y i)) := by
      funext y
      simp [heatKernel]
    rwa [hEq]
  have hNormSqHeatInt : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2 * Φ n t y) volume := by
    have hEq : (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2 * Φ n t y)
        = (fun y => ∑ i, ((y i) ^ 2 * Φ n t y)) := by
      funext y
      rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
    rw [hEq]
    exact integrable_finsetSum _ fun i _ => by
      have hEq2 : (fun y : EuclideanSpace ℝ (Fin n) => (y i) ^ 2 * Φ n t y)
          = (fun y => Φ n t y * (y i * y i)) := by
        funext y
        ring
      rw [hEq2]
      exact hDiagInt i
  have hDensMeas : Measurable
      (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
    hHeatCont.measurable.ennreal_ofReal
  have hDensLt : ∀ᵐ (y : EuclideanSpace ℝ (Fin n)) ∂volume,
      (ENNReal.ofReal (Φ n t y)) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top
  have hBoundIntVolume : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => (C * ‖y‖ ^ 2) * Φ n t y) volume := by
    have hEq : (fun y : EuclideanSpace ℝ (Fin n) => (C * ‖y‖ ^ 2) * Φ n t y)
        = (fun y => C * (‖y‖ ^ 2 * Φ n t y)) := by
      funext y
      ring
    rw [hEq]
    exact hNormSqHeatInt.const_mul C
  have hBoundInt : Integrable (fun y : EuclideanSpace ℝ (Fin n) => C * ‖y‖ ^ 2)
      (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
        by
    rw [integrable_withDensity_iff hDensMeas hDensLt]
    have hEq : (fun y : EuclideanSpace ℝ (Fin n) =>
          (C * ‖y‖ ^ 2) * (ENNReal.ofReal (Φ n t y)).toReal)
        = (fun y => (C * ‖y‖ ^ 2) * Φ n t y) := by
      funext y
      rw [ENNReal.toReal_ofReal (hHeatNonneg y)]
    rw [hEq]
    exact hBoundIntVolume
  have hContIntegral : Continuous (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity
      fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y))) :=
    continuous_of_dominated hFmeas hBoundEv hBoundInt hContAE
  exact hContIntegral.aestronglyMeasurable

private theorem heatKernel_continuous (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => Φ n t x := by
  unfold heatKernel
  apply Continuous.mul continuous_const
  apply Real.continuous_exp.comp
  apply Continuous.div
  · exact (continuous_norm.pow 2).neg
  · exact continuous_const
  · exact fun _ => ne_of_gt (mul_pos (by norm_num) ht)

/-- A coordinate of a Euclidean vector is bounded by its norm. -/
private theorem euclidean_coord_abs_le_norm (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : |x i| ≤ ‖x‖ := by
  have h1 : (‖x i‖) ^ 2 ≤ ∑ j, (‖x j‖) ^ 2 :=
    Finset.single_le_sum (f := fun j => (‖x j‖) ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ j, (‖x j‖) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : (‖x i‖) ^ 2 ≤ (‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt hsum0]
    exact h1
  rw [Real.norm_eq_abs, sq_abs] at h2
  exact abs_le_of_sq_le_sq h2 (norm_nonneg _)

/-- Uniform domination of the Taylor integrand by `C * ‖y‖ ^ 2`. -/
private theorem Dfn_bound (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
      s ∈ Set.Icc 0 1 →
      ‖(1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
        C * ‖y‖ ^ 2 := by
  choose M hM0 hM using hBnd
  refine ⟨∑ i, ∑ j, 2 * M i j,
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num) (hM0 i j),
    fun s x y hs => ?_⟩
  have hs01 := Set.mem_Icc.mp hs
  have h1s : |1 - s| ≤ 1 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hterm : ∀ i j, ‖y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
      (2 * M i j) * ‖y‖ ^ 2 := by
    intro i j
    have hyi : |y i| ≤ ‖y‖ := euclidean_coord_abs_le_norm n y i
    have hyj : |y j| ≤ ‖y‖ := euclidean_coord_abs_le_norm n y j
    have hdiff : ‖secondPartialFn n φ i j (x - s • y) -
        secondPartialFn n φ i j x‖ ≤ 2 * M i j := by
      have e1 : ‖secondPartialFn n φ i j (x - s • y)‖ ≤ M i j := by
        rw [Real.norm_eq_abs]
        exact hM i j _
      have e2 : ‖secondPartialFn n φ i j x‖ ≤ M i j := by
        rw [Real.norm_eq_abs]
        exact hM i j _
      linarith [norm_sub_le (secondPartialFn n φ i j (x - s • y))
        (secondPartialFn n φ i j x)]
    have e1 : |y i| * |y j| ≤ ‖y‖ * ‖y‖ :=
      mul_le_mul hyi hyj (abs_nonneg _) (norm_nonneg _)
    have hnn : (0 : ℝ) ≤ 2 * M i j := mul_nonneg (by norm_num) (hM0 i j)
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |y i| * |y j| * ‖secondPartialFn n φ i j (x - s • y) -
            secondPartialFn n φ i j x‖
        ≤ (‖y‖ * ‖y‖) * (2 * M i j) :=
          mul_le_mul e1 hdiff (norm_nonneg _) (by positivity)
      _ = (2 * M i j) * ‖y‖ ^ 2 := by ring
  have hsum : ‖∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
      (∑ i, ∑ j, 2 * M i j) * ‖y‖ ^ 2 := by
    simp only [Finset.sum_mul]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun j _ => hterm i j
  rw [norm_mul, Real.norm_eq_abs]
  calc |1 - s| * ‖∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
      ≤ 1 * ((∑ i, ∑ j, 2 * M i j) * ‖y‖ ^ 2) :=
        mul_le_mul h1s hsum (norm_nonneg _) zero_le_one
    _ = (∑ i, ∑ j, 2 * M i j) * ‖y‖ ^ 2 := one_mul _

/-- Joint continuity of the Taylor remainder in `(x, y)`. -/
private theorem Dfn_continuous (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hDij : ∀ i j, Continuous (secondPartialFn n φ i j))
    (hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M) :
    Continuous (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
      Dfn n φ x y) := by
  obtain ⟨C, hC0, hper⟩ := Dfn_bound n φ hBnd
  have hcoord : ∀ i : Fin n, Continuous fun x : EuclideanSpace ℝ (Fin n) => x i := by
    intro i
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
    rw [EuclideanSpace.coe_proj] at h
    exact h
  have hH : Continuous fun q : ℝ ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
      (1 - q.1) * ∑ i, ∑ j, q.2.2 i * q.2.2 j *
        (secondPartialFn n φ i j (q.2.1 - q.1 • q.2.2) -
          secondPartialFn n φ i j q.2.1) := by
    apply Continuous.mul
    · exact continuous_const.sub continuous_fst
    · apply continuous_finsetSum _
      intro i _
      apply continuous_finsetSum _
      intro j _
      apply Continuous.mul
      · apply Continuous.mul
        · exact (hcoord i).comp (continuous_snd.comp continuous_snd)
        · exact (hcoord j).comp (continuous_snd.comp continuous_snd)
      · apply Continuous.sub
        · exact (hDij i j).comp ((continuous_fst.comp continuous_snd).sub
            (continuous_fst.smul (continuous_snd.comp continuous_snd)))
        · exact (hDij i j).comp (continuous_fst.comp continuous_snd)
  rw [continuous_iff_continuousAt]
  intro p₀
  have hrewrite : (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
      Dfn n φ x y) = fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => ∫ s, (1 - s) * ∑ i, ∑ j, p.2 i * p.2 j *
        (secondPartialFn n φ i j (p.1 - s • p.2) -
          secondPartialFn n φ i j p.1) ∂(volume.restrict (Set.Ioc 0 1)) := by
    funext p
    change Dfn n φ p.1 p.2 = _
    unfold Dfn
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [hrewrite]
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => C * (‖p₀.2‖ + 1) ^ 2) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun p => ?_
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact continuous_const.sub continuous_id
    · apply continuous_finsetSum _
      intro i _
      apply continuous_finsetSum _
      intro j _
      apply Continuous.mul
      · apply Continuous.mul
        · exact continuous_const
        · exact continuous_const
      · apply Continuous.sub
        · exact (hDij i j).comp
            (continuous_const.sub (continuous_id.smul continuous_const))
        · exact continuous_const
  · refine eventually_of_mem (Metric.ball_mem_nhds p₀ zero_lt_one) fun p hp => ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun s hs => ?_
    have hsIcc : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hs
    have hle := hper s p.1 p.2 hsIcc
    have hdist : dist p p₀ < 1 := Metric.mem_ball.mp hp
    have hlip : LipschitzWith 1 (Prod.snd : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :=
      LipschitzWith.prod_snd
    have hle1 : dist p.2 p₀.2 ≤ 1 * dist p p₀ := by
      have h := LipschitzWith.dist_le_mul hlip p p₀
      simpa using h
    have hnorm1 : ‖p.2 - p₀.2‖ < 1 := by
      rw [← dist_eq_norm]
      linarith [hle1, hdist]
    have hnorm2 : ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
      linarith [norm_sub_norm_le p.2 p₀.2, hnorm1]
    have hpow2 : ‖p.2‖ ^ 2 ≤ (‖p₀.2‖ + 1) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm2 2
    exact hle.trans (mul_le_mul_of_nonneg_left hpow2 hC0)
  · refine ae_of_all _ fun s => ?_
    have h1 : ContinuousAt (fun q : ℝ ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        (1 - q.1) * ∑ i, ∑ j, q.2.2 i * q.2.2 j *
          (secondPartialFn n φ i j (q.2.1 - q.1 • q.2.2) -
            secondPartialFn n φ i j q.2.1)) (s, p₀) := hH.continuousAt
    have h2 : ContinuousAt (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => (s, p)) p₀ :=
      continuousAt_const.prodMk continuousAt_id
    have hcomp := h1.comp h2
    exact hcomp

private theorem integrable_heatKernel_mul_norm_pow (n : ℕ) (t : ℝ) (ht : 0 < t)
    (m : ℕ) :
    Integrable (fun a : EuclideanSpace ℝ (Fin n) =>
      Φ n t a * ‖a‖ ^ m) volume := by
  refine ((integrable_poly_gauss_aux n m (1 / (4 * t)) (by positivity)).const_mul
    ((4 * Real.pi * t) ^ (-(n : ℝ) / 2))).mono'
    ((heatKernel_continuous n t ht).mul (continuous_norm.pow m)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  change ‖Φ n t a * ‖a‖ ^ m‖ ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
    * ((1 + ‖a‖) ^ m * Real.exp (-(1 / (4 * t)) * ‖a‖ ^ 2))
  have hexp : Real.exp (-‖a‖ ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * ‖a‖ ^ 2) := by
    congr 1
    ring
  have hpow : ‖a‖ ^ m ≤ (1 + ‖a‖) ^ m := pow_le_pow_left₀ (norm_nonneg a) (by linarith) m
  rw [heatKernel_euclideanSpace, hexp, Real.norm_of_nonneg (by positivity)]
  calc (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖a‖ ^ 2) * ‖a‖ ^ m
      ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖a‖ ^ 2)
        * (1 + ‖a‖) ^ m := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * ((1 + ‖a‖) ^ m * Real.exp (-(1 / (4 * t)) * ‖a‖ ^ 2)) := by ring

private theorem Dfn_lintegral_x_le (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hDfnBound : ∀ (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (_hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
      s ∈ Set.Icc 0 1 →
      ‖(1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
        C * ‖y‖ ^ 2)
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ y : EuclideanSpace ℝ (Fin n),
      ∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume
        ≤ ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2) := by
  obtain ⟨C₀, hC₀, hDB⟩ := hDfnBound n φ
    (fun i j => hBndThm n i j (hDijThm i j).1 (hDijThm i j).2.1)
  have hcont : ∀ x y : EuclideanSpace ℝ (Fin n),
      Continuous (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)) := by
    intro x y
    have hxy : Continuous (fun s : ℝ => x - s • y) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    refine Continuous.mul (continuous_const.sub continuous_id) ?_
    refine continuous_finsetSum _ fun i _ => ?_
    refine continuous_finsetSum _ fun j _ => ?_
    refine Continuous.mul continuous_const ?_
    exact ((hDijThm i j).1.comp hxy).sub continuous_const
  have hpt : ∀ x y : EuclideanSpace ℝ (Fin n), ‖Dfn n φ x y‖ ≤ C₀ * ‖y‖ ^ 2 := by
    intro x y
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have h1 : ‖∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
        ≤ ∫ s in (0 : ℝ)..1, ‖(1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ := by
      rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h01]
      exact norm_integral_le_integral_norm _
    have h2 : (∫ s in (0 : ℝ)..1, ‖(1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖)
        ≤ ∫ s in (0 : ℝ)..1, C₀ * ‖y‖ ^ 2 :=
      intervalIntegral.integral_mono_on h01 ((hcont x y).norm.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1) (fun s hs => hDB s x y hs)
    have h3 : (∫ s in (0 : ℝ)..1, C₀ * ‖y‖ ^ 2) = C₀ * ‖y‖ ^ 2 := by
      rw [intervalIntegral.integral_const, sub_zero, one_smul]
    have hD : Dfn n φ x y = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) := rfl
    rw [hD]
    exact le_trans h1 (le_trans h2 (le_of_eq h3))
  have hts0 : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)),
      z ∉ tsupport g → g z = 0 := by
    intro g z hz
    have hsub := subset_tsupport g
    have hnsup : z ∉ Function.support g := fun h => hz (hsub h)
    by_contra hne
    exact hnsup (Function.mem_support.mpr hne)
  have hzero : ∀ y x : EuclideanSpace ℝ (Fin n),
      x ∉ (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) ∪
        ((⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) +
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ‖y‖) →
      Dfn n φ x y = 0 := by
    intro y x hx
    have hxA : x ∉ ⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j) := fun h => hx (Or.inl h)
    have hxB : x ∉ (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) +
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ‖y‖ :=
      fun h => hx (Or.inr h)
    have hAx : ∀ i j, x ∉ tsupport (secondPartialFn n φ i j) := by
      intro i j hmem
      exact hxA (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hmem⟩⟩)
    have hsy : ∀ s : ℝ, s ∈ Set.Icc 0 1 →
        s • y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ‖y‖ := by
      intro s hs
      obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs]
      have habs : |s| ≤ 1 := by rw [abs_of_nonneg hs0]; exact hs1
      calc |s| * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    have hAs : ∀ (s : ℝ) (i j : Fin n), s ∈ Set.Icc 0 1 →
        x - s • y ∉ tsupport (secondPartialFn n φ i j) := by
      intro s i j hs hcon
      have hmemK : x - s • y ∈ ⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j) :=
        Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hcon⟩⟩
      apply hxB
      have heq : x = (x - s • y) + s • y := (sub_add_cancel x (s • y)).symm
      rw [heq]
      exact Set.add_mem_add hmemK (hsy s hs)
    have hg0 : ∀ s : ℝ, s ∈ Set.Icc 0 1 →
        (1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) = 0 := by
      intro s hs
      have hterm : ∀ i j : Fin n, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) = 0 := by
        intro i j
        rw [hts0 _ _ (hAs s i j hs), hts0 _ _ (hAx i j), sub_self, mul_zero]
      simp [hterm]
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have hD : Dfn n φ x y = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) := rfl
    rw [hD, intervalIntegral.integral_of_le h01]
    apply setIntegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall (fun s hs => hg0 s (Set.Ioc_subset_Icc_self hs))
  have hKc : IsCompact (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) := by
    have e1 : (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j))
        = ⋃ i ∈ (Set.univ : Set (Fin n)), ⋃ j ∈ (Set.univ : Set (Fin n)),
          tsupport (secondPartialFn n φ i j) := by
      ext x
      simp
    rw [e1]
    refine Set.Finite.isCompact_biUnion (Set.finite_univ (α := Fin n)) fun i _ => ?_
    refine Set.Finite.isCompact_biUnion (Set.finite_univ (α := Fin n)) fun j _ => ?_
    exact (hDijThm i j).2.1
  obtain ⟨C₁, hC₁⟩ := isBounded_iff_forall_norm_le.mp hKc.isBounded
  have hR0 : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
  have hKR : ∀ x ∈ (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)), ‖x‖ ≤ max C₁ 0 :=
    fun x hx => le_trans (hC₁ x hx) (le_max_left _ _)
  have hsub : ∀ y : EuclideanSpace ℝ (Fin n),
      (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) ∪
        ((⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) +
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ‖y‖)
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖) := by
    intro y x hx
    rcases hx with hxK | hxadd
    · rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖x‖ ≤ max C₁ 0 := hKR x hxK
        _ ≤ max C₁ 0 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
    · obtain ⟨a, haK, b, hb, rfl⟩ := Set.mem_add.mp hxadd
      rw [Metric.mem_closedBall, dist_zero_right]
      have haR : ‖a‖ ≤ max C₁ 0 := hKR a haK
      have hbR : ‖b‖ ≤ ‖y‖ := by
        have h := Metric.mem_closedBall.mp hb
        rwa [dist_zero_right] at h
      calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
        _ ≤ max C₁ 0 + ‖y‖ := add_le_add haR hbR
  have hD0ball : ∀ y x : EuclideanSpace ℝ (Fin n),
      x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖) →
      Dfn n φ x y = 0 := by
    intro y x hx
    exact hzero y x (fun hcon => hx (hsub y hcon))
  have hGnonneg : (0 : ℝ) ≤ √Real.pi ^ n / Real.Gamma (↑n / 2 + 1) :=
    div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (le_of_lt (Real.Gamma_pos_of_pos (by positivity)))
  refine ⟨(√Real.pi ^ n / Real.Gamma (↑n / 2 + 1)) * C₀, max C₁ 0,
    mul_nonneg hGnonneg hC₀, hR0, fun y => ?_⟩
  by_cases hn : n = 0
  · subst hn
    have hDf0 : ∀ x : EuclideanSpace ℝ (Fin 0), Dfn 0 φ x y = 0 := by
      intro x
      unfold Dfn
      have hint : ∀ s : ℝ, (1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn 0 φ i j (x - s • y) - secondPartialFn 0 φ i j x) = 0 := by
        intro s
        simp
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply setIntegral_eq_zero_of_ae_eq_zero
      exact Filter.Eventually.of_forall (fun s _ => hint s)
    have hz : (∫⁻ x, ENNReal.ofReal ‖Dfn 0 φ x y‖ ∂volume) = 0 := by
      have hfun : (fun x => ENNReal.ofReal ‖Dfn 0 φ x y‖) = fun _ => 0 :=
        funext (fun x => by rw [hDf0 x]; simp)
      calc (∫⁻ x, ENNReal.ofReal ‖Dfn 0 φ x y‖ ∂volume)
          = ∫⁻ _ : EuclideanSpace ℝ (Fin 0), (0 : ENNReal) ∂volume := by rw [hfun]
        _ = 0 := by rw [lintegral_const, zero_mul]
    rw [hz]
    exact zero_le
  · have hne : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    have hSmeas : MeasurableSet
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖)) :=
      Metric.isClosed_closedBall.measurableSet
    have hbound : (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume)
        ≤ ENNReal.ofReal (C₀ * ‖y‖ ^ 2) *
          volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖)) := by
      have hmono : (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume)
          ≤ ∫⁻ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖)).indicator
            (fun _ => ENNReal.ofReal (C₀ * ‖y‖ ^ 2)) x ∂volume := by
        apply lintegral_mono_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        by_cases hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖)
        · have hmem : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
              (max C₁ 0 + ‖y‖)).indicator (fun _ => ENNReal.ofReal (C₀ * ‖y‖ ^ 2)) x
              = ENNReal.ofReal (C₀ * ‖y‖ ^ 2) :=
            Set.indicator_of_mem hx _
          rw [hmem]
          exact ENNReal.ofReal_le_ofReal (hpt x y)
        · have hmem : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
              (max C₁ 0 + ‖y‖)).indicator (fun _ => ENNReal.ofReal (C₀ * ‖y‖ ^ 2)) x = 0 :=
            Set.indicator_of_notMem hx _
          rw [hmem]
          have hDx : Dfn n φ x y = 0 := hD0ball y x hx
          rw [hDx]
          simp
      have hind : (∫⁻ x, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
          (max C₁ 0 + ‖y‖)).indicator (fun _ => ENNReal.ofReal (C₀ * ‖y‖ ^ 2)) x ∂volume)
          = ENNReal.ofReal (C₀ * ‖y‖ ^ 2) *
            volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖)) := by
        rw [lintegral_indicator hSmeas]
        exact setLIntegral_const _ _
      exact le_trans hmono (le_of_eq hind)
    have hvol : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖))
        = ENNReal.ofReal (max C₁ 0 + ‖y‖) ^ n *
          ENNReal.ofReal (√Real.pi ^ n / Real.Gamma (↑n / 2 + 1)) := by
      have h := @EuclideanSpace.volume_closedBall (Fin n) hne inferInstance
        (0 : EuclideanSpace ℝ (Fin n)) (max C₁ 0 + ‖y‖)
      rw [Fintype.card_fin] at h
      exact h
    have hr : (0 : ℝ) ≤ max C₁ 0 + ‖y‖ := add_nonneg hR0 (norm_nonneg _)
    have hc : (0 : ℝ) ≤ C₀ * ‖y‖ ^ 2 := mul_nonneg hC₀ (sq_nonneg _)
    have hring : (C₀ * ‖y‖ ^ 2) * ((max C₁ 0 + ‖y‖) ^ n *
          (√Real.pi ^ n / Real.Gamma (↑n / 2 + 1)))
        = ((√Real.pi ^ n / Real.Gamma (↑n / 2 + 1)) * C₀) *
          (max C₁ 0 + ‖y‖) ^ n * ‖y‖ ^ 2 := by ring
    rw [hvol] at hbound
    refine le_trans hbound ?_
    rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (pow_nonneg hr n),
      ← ENNReal.ofReal_mul hc]
    apply ENNReal.ofReal_le_ofReal
    exact le_of_eq hring

private theorem isCompact_supportUnion (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    IsCompact (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) := by
  apply isCompact_iUnion
  intro i
  apply isCompact_iUnion
  intro j
  exact ((hDijThm i j).2.1).isCompact

private theorem exists_closedBall_superset_supportUnion (n : ℕ)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ R : ℝ, 0 ≤ R ∧
      (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) ⊆
        Metric.closedBall 0 R := by
  have hComp := isCompact_supportUnion n φ hDijThm
  have hBdd := hComp.isBounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hBdd
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  have hxC := hC x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact le_trans hxC (le_max_left _ _)

private theorem Dfn_norm_le_of_bound (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hDij : ∀ i j, Continuous (secondPartialFn n φ i j))
    (C : ℝ) (hC : ∀ (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
      s ∈ Set.Icc 0 1 →
      ‖(1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
        C * ‖y‖ ^ 2) :
    ∀ (x y : EuclideanSpace ℝ (Fin n)), ‖Dfn n φ x y‖ ≤ C * ‖y‖ ^ 2 := by
  intro x y
  have hCont : Continuous (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)) := by
    have hSub : Continuous (fun s : ℝ => x - s • y) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    apply Continuous.mul
    · exact continuous_const.sub continuous_id
    · apply continuous_finsetSum _
      intro i _
      apply continuous_finsetSum _
      intro j _
      have hD : Continuous (fun s : ℝ => secondPartialFn n φ i j (x - s • y)) :=
        (hDij i j).comp hSub
      have hDiff : Continuous (fun s : ℝ =>
          secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) :=
        hD.sub continuous_const
      exact (continuous_const.mul continuous_const).mul hDiff
  have hNorm : ‖∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
      ∫ s in (0 : ℝ)..1, ‖(1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num)
  have hInt1 : IntervalIntegrable (fun s : ℝ => ‖(1 - s) * ∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖)
      volume 0 1 :=
    hCont.norm.intervalIntegrable 0 1
  have hInt2 : IntervalIntegrable (fun _ : ℝ => C * ‖y‖ ^ 2) volume 0 1 :=
    intervalIntegrable_const
  have hMono : (∫ s in (0 : ℝ)..1, ‖(1 - s) * ∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖) ≤
      ∫ _ in (0 : ℝ)..1, C * ‖y‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hInt1 hInt2
      (fun s hs => hC s x y hs)
  have hConst : (∫ _ in (0 : ℝ)..1, C * ‖y‖ ^ 2) = C * ‖y‖ ^ 2 := by
    simp [intervalIntegral.integral_const]
  have hEq : Dfn n φ x y = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) := rfl
  rw [hEq]
  exact le_trans hNorm (le_trans hMono (le_of_eq hConst))

private theorem Dfn_eq_zero_of_outside_closedBall (n : ℕ)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ)
    (hR : (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) ⊆
      Metric.closedBall 0 R)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∉ Metric.closedBall 0 (R + ‖y‖)) :
    Dfn n φ x y = 0 := by
  have hLe : R ≤ R + ‖y‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hSub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆
      Metric.closedBall 0 (R + ‖y‖) :=
    Metric.closedBall_subset_closedBall hLe
  have hxK : x ∉ ⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j) :=
    fun hK => hx (hSub (hR hK))
  have hOut : ∀ (s : ℝ), s ∈ Set.Icc 0 1 →
      x - s • y ∉ ⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j) := by
    intro s hs hMem
    have hBall := hR hMem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hBall
    have hs1 : s ≤ 1 := hs.2
    have hs0 : 0 ≤ s := hs.1
    have hAbs : |s| ≤ 1 := abs_le.mpr ⟨by linarith, hs1⟩
    have hSmul : ‖s • y‖ ≤ ‖y‖ := by
      calc ‖s • y‖ = ‖s‖ * ‖y‖ := norm_smul s y
        _ = |s| * ‖y‖ := by rw [Real.norm_eq_abs]
        _ ≤ 1 * ‖y‖ := by
            apply mul_le_mul_of_nonneg_right hAbs (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    have hX : ‖x‖ ≤ R + ‖y‖ := by
      have hEq : x = (x - s • y) + s • y := by abel
      calc ‖x‖ = ‖(x - s • y) + s • y‖ := by rw [← hEq]
        _ ≤ ‖x - s • y‖ + ‖s • y‖ := norm_add_le _ _
        _ ≤ R + ‖y‖ := add_le_add hBall hSmul
    have hxBall : x ∈ Metric.closedBall 0 (R + ‖y‖) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hX
    exact hx hxBall
  have hZero : ∀ (s : ℝ), s ∈ Set.Ioc 0 1 →
      (1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) = 0 := by
    intro s hs
    have hsIcc : s ∈ Set.Icc 0 1 := Set.Ioc_subset_Icc_self hs
    have h1 : ∀ i j, secondPartialFn n φ i j x = 0 := by
      intro i j
      apply image_eq_zero_of_notMem_tsupport
      intro hIn
      have hSub2 : tsupport (secondPartialFn n φ i j) ⊆
          ⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j) :=
        le_trans (Set.subset_iUnion (fun j => tsupport (secondPartialFn n φ i j)) j)
          (Set.subset_iUnion (fun i => ⋃ j, tsupport (secondPartialFn n φ i j)) i)
      exact hxK (hSub2 hIn)
    have h2 : ∀ i j, secondPartialFn n φ i j (x - s • y) = 0 := by
      intro i j
      apply image_eq_zero_of_notMem_tsupport
      intro hIn
      have hSub2 : tsupport (secondPartialFn n φ i j) ⊆
          ⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j) :=
        le_trans (Set.subset_iUnion (fun j => tsupport (secondPartialFn n φ i j)) j)
          (Set.subset_iUnion (fun i => ⋃ j, tsupport (secondPartialFn n φ i j)) i)
      exact hOut s hsIcc (hSub2 hIn)
    have hSum : (∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)) = 0 := by
      apply Fintype.sum_eq_zero
      intro i
      apply Fintype.sum_eq_zero
      intro j
      rw [h2 i j, h1 i j, sub_self, mul_zero]
    rw [hSum, mul_zero]
  have hEq : Dfn n φ x y = ∫ s in Set.Ioc 0 1, (1 - s) * ∑ i, ∑ j, y i * y j *
      (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x) := by
    unfold Dfn
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hEq]
  exact setIntegral_eq_zero_of_forall_eq_zero (fun s hs => hZero s hs)

private theorem lintegral_Dfn_le_volume_mul (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (R C : ℝ)
    (hR : (⋃ i, ⋃ j, tsupport (secondPartialFn n φ i j)) ⊆
      Metric.closedBall 0 R)
    (hBound : ∀ (x y : EuclideanSpace ℝ (Fin n)),
      ‖Dfn n φ x y‖ ≤ C * ‖y‖ ^ 2)
    (y : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume ≤
      ENNReal.ofReal (C * ‖y‖ ^ 2) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖)) := by
  have hMeas : MeasurableSet (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖)) :=
    measurableSet_closedBall
  have hSplit : ∫⁻ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖),
      ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume +
      ∫⁻ x in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖))ᶜ,
        ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume =
      ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume :=
    MeasureTheory.lintegral_add_compl _ hMeas
  have hZero : ∫⁻ x in (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖))ᶜ,
      ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume = 0 := by
    apply MeasureTheory.setLIntegral_eq_zero hMeas.compl
    intro x hx
    simp only [Set.mem_compl_iff] at hx
    have hD := Dfn_eq_zero_of_outside_closedBall n φ R hR x y hx
    simp [hD]
  have hLe : ∫⁻ x in Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖),
      ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume ≤
      ∫⁻ _ in Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖),
        ENNReal.ofReal (C * ‖y‖ ^ 2) ∂volume := by
    apply MeasureTheory.setLIntegral_mono measurable_const
    intro x _
    exact ENNReal.ofReal_le_ofReal (hBound x y)
  have hConst : ∫⁻ _ in Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖),
      ENNReal.ofReal (C * ‖y‖ ^ 2) ∂volume =
      ENNReal.ofReal (C * ‖y‖ ^ 2) *
        volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖)) :=
    MeasureTheory.setLIntegral_const _ _
  calc ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume
      = ∫⁻ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖),
          ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume +
          ∫⁻ x in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖))ᶜ,
            ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume := hSplit.symm
    _ = ∫⁻ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖),
          ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume := by rw [hZero, add_zero]
    _ ≤ ENNReal.ofReal (C * ‖y‖ ^ 2) *
          volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R + ‖y‖)) := by
          rw [← hConst]
          exact hLe

/-- The heat kernel is nonnegative for positive time. -/
private theorem Dfn_uncurry_integrable (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (_hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M)
    (hDfnBound : ∀ (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (_hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
      s ∈ Set.Icc 0 1 →
      ‖(1 - s) * ∑ i, ∑ j, y i * y j *
        (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
        C * ‖y‖ ^ 2)
    (hDfnCont : ∀ (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
      (_hDij : ∀ i j, Continuous (secondPartialFn n φ i j))
      (_hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M),
    Continuous (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
      Dfn n φ x y))
    (hIntMom : ∀ (n : ℕ) (t : ℝ) (_ht : 0 < t) (m : ℕ),
    Integrable (fun a : EuclideanSpace ℝ (Fin n) =>
      Φ n t a * ‖a‖ ^ m) volume)
    (hXBound : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
      (_hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
      (_hDfnBound : ∀ (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
        (_hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (x y : EuclideanSpace ℝ (Fin n)),
        s ∈ Set.Icc 0 1 →
        ‖(1 - s) * ∑ i, ∑ j, y i * y j *
          (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖ ≤
          C * ‖y‖ ^ 2)
      (_hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M),
      ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ y : EuclideanSpace ℝ (Fin n),
        ∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume
          ≤ ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)) :
    ∀ (t : ℝ), 0 < t →
      Integrable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) => Dfn n φ x y)
        (volume.prod (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
          (Φ n t y))) := by
  intro t ht
  have hDij : ∀ i j, Continuous (secondPartialFn n φ i j) :=
    fun i j => (hDijThm i j).1
  have hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M :=
    fun i j => hBndThm n i j (hDij i j) (hDijThm i j).2.1
  have hCont := hDfnCont n φ hDij hBnd
  refine ⟨hCont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  obtain ⟨C, R, hC, hR, hXB⟩ := hXBound n hDijThm hDfnBound hBndThm
  have hF : Continuous (fun a : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ‖Function.uncurry (fun x y : EuclideanSpace ℝ (Fin n) => Dfn n φ x y) a‖) :=
    ENNReal.continuous_ofReal.comp (continuous_norm.comp hCont)
  have hProd : (∫⁻ a, ENNReal.ofReal
        ‖Function.uncurry (fun x y : EuclideanSpace ℝ (Fin n) => Dfn n φ x y) a‖
        ∂(volume.prod (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y))))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal ‖Dfn n φ x y‖
        ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)) ∂volume :=
    lintegral_prod _ hF.aemeasurable
  have hUnc : AEMeasurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ‖Dfn n φ x y‖)
      (volume.prod (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Φ n t y))) :=
    hF.aemeasurable
  have hSwap : (∫⁻ x, ∫⁻ y, ENNReal.ofReal ‖Dfn n φ x y‖
        ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)) ∂volume)
      = ∫⁻ y, ∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume
        ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)) :=
    lintegral_lintegral_swap hUnc
  rw [hProd, hSwap]
  have hMono : (∫⁻ y, ∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ∂volume
        ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)))
      ≤ ∫⁻ y, ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)
        ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)) :=
    lintegral_mono hXB
  refine lt_of_le_of_lt hMono ?_
  have hHKMeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Φ n t y)) :=
    (ENNReal.continuous_ofReal.comp (heatKernel_continuous n t ht)).measurable
  have hpolycont : Continuous (fun y : EuclideanSpace ℝ (Fin n) =>
      C * (R + ‖y‖) ^ n * ‖y‖ ^ 2) :=
    (continuous_const.mul ((continuous_const.add continuous_norm).pow n)).mul
      (continuous_norm.pow 2)
  have hDensMeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)) :=
    (ENNReal.continuous_ofReal.comp hpolycont).measurable
  have hDens : (∫⁻ y, ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)
        ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)))
      = ∫⁻ y, ENNReal.ofReal (Φ n t y)
        * ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2) ∂volume :=
    lintegral_withDensity_eq_lintegral_mul volume hHKMeas hDensMeas
  rw [hDens]
  have hmul : ∀ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (Φ n t y) * ENNReal.ofReal (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)
        = ENNReal.ofReal (Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)) :=
    fun y => (ENNReal.ofReal_mul (heatKernel_nonneg n t ht y)).symm
  simp only [hmul]
  have hpowbound : ∀ r : ℝ, 0 ≤ r → (R + r) ^ n ≤ 2 ^ n * (R ^ n + r ^ n) := by
    intro r hr
    have hmax : R + r ≤ 2 * max R r := by
      rcases le_total R r with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hmaxn : (max R r) ^ n ≤ R ^ n + r ^ n := by
      rcases le_total R r with h | h
      · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg hR n)
      · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hr n)
    calc (R + r) ^ n ≤ (2 * max R r) ^ n := pow_le_pow_left₀ (add_nonneg hR hr) hmax n
      _ = 2 ^ n * (max R r) ^ n := mul_pow 2 _ n
      _ ≤ 2 ^ n * (R ^ n + r ^ n) :=
          mul_le_mul_of_nonneg_left hmaxn (pow_nonneg (by norm_num) n)
  have hpoly : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ C * (R + ‖y‖) ^ n * ‖y‖ ^ 2 := by
    intro y
    exact mul_nonneg (mul_nonneg hC (pow_nonneg (add_nonneg hR (norm_nonneg _)) n))
      (pow_nonneg (norm_nonneg _) 2)
  have hpolyQ : ∀ y : EuclideanSpace ℝ (Fin n),
      C * (R + ‖y‖) ^ n * ‖y‖ ^ 2 ≤ 2 ^ n * C * (R ^ n * ‖y‖ ^ 2 + ‖y‖ ^ (n + 2)) := by
    intro y
    have h1 : (R + ‖y‖) ^ n ≤ 2 ^ n * (R ^ n + ‖y‖ ^ n) := hpowbound _ (norm_nonneg _)
    have h2 : (R + ‖y‖) ^ n * ‖y‖ ^ 2 ≤ (2 ^ n * (R ^ n + ‖y‖ ^ n)) * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) 2)
    have h3 : C * ((R + ‖y‖) ^ n * ‖y‖ ^ 2)
        ≤ C * ((2 ^ n * (R ^ n + ‖y‖ ^ n)) * ‖y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hC
    have hpow : ‖y‖ ^ n * ‖y‖ ^ 2 = ‖y‖ ^ (n + 2) := by rw [← pow_add]
    calc C * (R + ‖y‖) ^ n * ‖y‖ ^ 2 = C * ((R + ‖y‖) ^ n * ‖y‖ ^ 2) := by ring
      _ ≤ C * ((2 ^ n * (R ^ n + ‖y‖ ^ n)) * ‖y‖ ^ 2) := h3
      _ = 2 ^ n * C * (R ^ n * ‖y‖ ^ 2 + ‖y‖ ^ (n + 2)) := by rw [← hpow]; ring
  have hfmeas : AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
      Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)) volume :=
    ((heatKernel_continuous n t ht).mul hpolycont).aestronglyMeasurable
  have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((2 : ℝ) ^ n * C * R ^ n) * (Φ n t y * ‖y‖ ^ 2)) volume :=
    (hIntMom n t ht 2).const_mul ((2 : ℝ) ^ n * C * R ^ n)
  have hn2 : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      ((2 : ℝ) ^ n * C) * (Φ n t y * ‖y‖ ^ (n + 2))) volume :=
    (hIntMom n t ht (n + 2)).const_mul ((2 : ℝ) ^ n * C)
  have hR := h2.add hn2
  have hbound : ∀ᵐ y : EuclideanSpace ℝ (Fin n) ∂volume,
      ‖Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)‖
        ≤ ((fun y : EuclideanSpace ℝ (Fin n) =>
          ((2 : ℝ) ^ n * C * R ^ n) * (Φ n t y * ‖y‖ ^ 2))
          + (fun y : EuclideanSpace ℝ (Fin n) =>
          ((2 : ℝ) ^ n * C) * (Φ n t y * ‖y‖ ^ (n + 2)))) y := by
    refine ae_of_all _ (fun y => ?_)
    change ‖Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)‖
      ≤ ((2 : ℝ) ^ n * C * R ^ n) * (Φ n t y * ‖y‖ ^ 2)
        + ((2 : ℝ) ^ n * C) * (Φ n t y * ‖y‖ ^ (n + 2))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg n t ht y) (hpoly y))]
    calc Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)
        ≤ Φ n t y * (2 ^ n * C * (R ^ n * ‖y‖ ^ 2 + ‖y‖ ^ (n + 2))) :=
          mul_le_mul_of_nonneg_left (hpolyQ y) (heatKernel_nonneg n t ht y)
      _ = ((2 : ℝ) ^ n * C * R ^ n) * (Φ n t y * ‖y‖ ^ 2)
          + ((2 : ℝ) ^ n * C) * (Φ n t y * ‖y‖ ^ (n + 2)) := by ring
  have hInt : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)) volume :=
    hR.mono' hfmeas hbound
  have hfin := (hasFiniteIntegral_iff_norm _).mp hInt.hasFiniteIntegral
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2)‖
        = Φ n t y * (C * (R + ‖y‖) ^ n * ‖y‖ ^ 2) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heatKernel_nonneg n t ht y) (hpoly y))]
  simp only [hnorm] at hfin
  exact hfin

private theorem integrable_uncurry_prod_swap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {F : α → β → ℝ} :
    Integrable (Function.uncurry F) (μ.prod ν) →
    Integrable (Function.uncurry (Function.swap F)) (ν.prod μ) := by
  intro h
  exact h.swap

private theorem Dfn_Jensen_chain (n : ℕ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hJensenThm : ∀ {n : ℕ} {q : ℝ} (_hq1 : 1 ≤ q)
      {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
      {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) →
      Integrable (Function.uncurry F) (μ.prod volume) →
      ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ q) ∂volume
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ q) ∂volume ∂μ)
    (hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hProbThm : ∀ (n : ℕ) {t : ℝ} (_ht : 0 < t),
      (∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y = 1) →
      IsProbabilityMeasure
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)))
    (hMeas : ∀ (t : ℝ), 0 < t →
      AEStronglyMeasurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) => Dfn n φ x y)
        ((volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t
          y)).prod volume))
    (hInt : ∀ (t : ℝ), 0 < t →
      Integrable (Function.uncurry fun y x : EuclideanSpace ℝ (Fin n) => Dfn n φ x y)
        ((volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t
          y)).prod volume)) :
    ∀ (t : ℝ), 0 < t →
      (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
        n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume)
      ≤ ∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
        ∂volume) ∂volume := by
  intro t ht
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono (ne_of_lt hp) hp1
    rwa [ENNReal.toReal_one] at h
  have hmass : (∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y) = 1 := by
    simpa only [heatKernel_euclideanSpace] using (hMomThm n ht).1
  have := hProbThm n ht hmass
  have hpos : ∀ y : EuclideanSpace ℝ (Fin n), 0 < Φ n t y := by
    intro y
    unfold heatKernel
    apply mul_pos
    · exact Real.rpow_pos_of_pos (by positivity) _
    · exact Real.exp_pos _
  have hhk : Measurable (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y) := by
    unfold heatKernel
    measurability
  have hf_meas : AEMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) volume :=
    (ENNReal.measurable_ofReal.comp hhk).aemeasurable
  have hf_ne : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (Φ n t y) ≠ 0 :=
    Filter.Eventually.of_forall fun y => ne_of_gt (ENNReal.ofReal_pos.mpr (hpos y))
  have hvol_ac : volume ≪ (volume.withDensity
      fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
    withDensity_absolutelyContinuous' hf_meas hf_ne
  have hμt_ac : (volume.withDensity
      fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) ≪ volume :=
    withDensity_absolutelyContinuous volume _
  have hprod_ac : (volume.prod (volume.withDensity
      fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)))
      ≪ ((volume.withDensity
        fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)).prod volume) :=
    Measure.AbsolutelyContinuous.prod hvol_ac hμt_ac
  have hM : AEStronglyMeasurable
      (Function.uncurry fun y x : EuclideanSpace ℝ (Fin n) => Dfn n φ x y)
      ((volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t
        y)).prod volume) :=
    AEStronglyMeasurable.prod_swap
      (f := Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) => Dfn n φ x y)
      (AEStronglyMeasurable.mono_ac hprod_ac (hMeas t ht))
  have hI : Integrable
      (Function.uncurry fun y x : EuclideanSpace ℝ (Fin n) => Dfn n φ x y)
      ((volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t
        y)).prod volume) := by
    exact hInt t ht
  have hJ := hJensenThm hq1 hM hI
  have hψ : Measurable (fun r : ℝ => ENNReal.ofReal (‖r‖ ^ p.toReal)) := by
    measurability
  have hunc : AEMeasurable
      (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (‖Dfn n φ y x‖ ^ p.toReal))
      ((volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t
        y)).prod volume) :=
    hψ.comp_aemeasurable hM.aemeasurable
  have hg_meas : AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫⁻ y, ENNReal.ofReal (‖Dfn n φ y x‖ ^ p.toReal) ∂volume)
      (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
    AEMeasurable.lintegral_prod_right hunc
  calc (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
    n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume)
      = ∫⁻ y, ENNReal.ofReal (‖∫ x, Dfn n φ y x ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
        n) => ENNReal.ofReal (Φ n t y))‖ ^ p.toReal) ∂volume := by
        apply lintegral_congr
        intro a
        exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (zero_le_one.trans hq1)
    _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖Dfn n φ y x‖ ^ p.toReal) ∂volume ∂(volume.withDensity fun y :
      EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
      hJ
    _ = ∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
      ∂volume) ∂volume := by
        rw [lintegral_withDensity_eq_lintegral_mul₀' hf_meas hg_meas]
        apply lintegral_congr
        intro a
        simp only [Pi.mul_apply]
        congr 1
        apply lintegral_congr
        intro b
        exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (zero_le_one.trans hq1)).symm

private theorem Dfn_Jensen_lintegral (n : ℕ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hJensenThm : ∀ {n : ℕ} {q : ℝ} (_hq1 : 1 ≤ q)
      {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
      {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) →
      Integrable (Function.uncurry F) (μ.prod volume) →
      ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ q) ∂volume
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ q) ∂volume ∂μ)
    (hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hProbThm : ∀ (n : ℕ) {t : ℝ} (_ht : 0 < t),
      (∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y = 1) →
      IsProbabilityMeasure
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)))
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M) :
    ∀ (t : ℝ), 0 < t →
      (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
        n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume)
      ≤ ∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
        ∂volume) ∂volume := by
  intro t ht
  have hDij : ∀ i j, Continuous (secondPartialFn n φ i j) :=
    fun i j => (hDijThm i j).1
  have hBnd : ∀ i j, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M :=
    fun i j => hBndThm n i j (hDij i j) (hDijThm i j).2.1
  exact Dfn_Jensen_chain n hp1 hp hJensenThm hMomThm hProbThm
    (fun t ht => (Dfn_continuous n φ hDij hBnd).aestronglyMeasurable)
    (fun t ht => integrable_uncurry_prod_swap (Dfn_uncurry_integrable n hDijThm hMomThm hBndThm
      Dfn_bound Dfn_continuous
      integrable_heatKernel_mul_norm_pow Dfn_lintegral_x_le t ht))
    t ht

private theorem jensen_density_bundle (n : ℕ) (_hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p)
    (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (_hφ : ContDiff ℝ 2 φ) (_hφ_supp : HasCompactSupport φ)
    (hJensenThm : ∀ {n : ℕ} {q : ℝ} (_hq1 : 1 ≤ q)
      {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
      {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) →
      Integrable (Function.uncurry F) (μ.prod volume) →
      ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ q) ∂volume
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ q) ∂volume ∂μ)
    (hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hProbThm : ∀ (n : ℕ) {t : ℝ} (_ht : 0 < t),
      (∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y = 1) →
      IsProbabilityMeasure
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)))
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (_hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      (∀ (x z : EuclideanSpace ℝ (Fin n)),
        |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖z‖) →
      ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
      |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
        ≤ secondPartialModulus n φ i j ‖y‖)
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M) :
    ∀ (t : ℝ), 0 < t →
      (∀ x : EuclideanSpace ℝ (Fin n),
        (∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
          (Φ n t y)))
        = ∫ y, Φ n t y * Dfn n φ x y)
      ∧ AEStronglyMeasurable
        (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)))
        volume
      ∧ (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
        n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume)
        ≤ ∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
          ∂volume) ∂volume := by
  intro t ht
  exact ⟨Dfn_integral_density n hDijThm hBndThm t ht,
    Dfn_integral_measurable n hDijThm hBndThm hMomThm t ht,
    Dfn_Jensen_lintegral n hp1 hp hJensenThm hMomThm hProbThm hDijThm hBndThm t ht⟩

end C1

section C2bypass

open MeasureTheory
open scoped Topology


private theorem aux_integral_one_sub_rpow_le (H : ℝ → ℝ) (hH : Continuous H)
    (hHnn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ H s) (q : ℝ) (hq : 1 ≤ q) :
    (∫ s in (0 : ℝ)..1, (1 - s) * H s) ^ q
      ≤ ((1 : ℝ) / 2) ^ (q - 1)
        * ∫ s in (0 : ℝ)..1, (1 - s) * (H s) ^ q := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have h1nn : (0 : ℝ) ≤ 1 := by norm_num
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hHq : Continuous (fun s : ℝ => (H s) ^ q) :=
    (Real.continuous_rpow_const hq0).comp hH
  have hA : 0 ≤ ∫ s in (0 : ℝ)..1, (1 - s) * H s := by
    apply intervalIntegral.integral_nonneg h01
    intro s hs
    have hs1 : s ≤ 1 := (Set.mem_Icc.mp hs).2
    have hw : (0 : ℝ) ≤ 1 - s := by linarith
    exact mul_nonneg hw (hHnn s hs)
  have hint : ∫ s in (0 : ℝ)..1, (1 - s) = 1 / 2 := by
    have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => s) volume 0 1 :=
      continuous_id.intervalIntegrable _ _
    have hsub : ∫ s in (0 : ℝ)..1, (1 - s)
        = (∫ s in (0 : ℝ)..1, (1 : ℝ)) - ∫ s in (0 : ℝ)..1, s :=
      intervalIntegral.integral_sub h1 h2
    rw [hsub, intervalIntegral.integral_const, integral_id, smul_eq_mul]
    norm_num
  have hdens_cont : Continuous (fun s : ℝ => (2 : ℝ) * (1 - s)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have hdens_meas : Measurable (fun s : ℝ => ENNReal.ofReal (2 * (1 - s))) :=
    (ENNReal.continuous_ofReal.comp hdens_cont).measurable
  have hdens_top : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ENNReal.ofReal (2 * (1 - s)) < ⊤ :=
    Filter.Eventually.of_forall fun s => ENNReal.ofReal_lt_top
  have hdens_eq : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      (ENNReal.ofReal (2 * (1 - s))).toReal = 2 * (1 - s) := by
    intro s hs
    have hs1 : s ≤ 1 := (Set.mem_Ioc.mp hs).2
    have hnn : (0 : ℝ) ≤ 2 * (1 - s) := by linarith
    exact ENNReal.toReal_ofReal hnn
  have hIoc1 : ∫ s, (1 : ℝ) - s ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      = ∫ s in (0 : ℝ)..1, (1 - s) :=
    (intervalIntegral.integral_of_le h01).symm
  have hμ1 : ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s)))) Set.univ = 1 := by
    have hBoch : Integrable (fun s : ℝ => 2 * (1 - s))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      Continuous.integrableOn_Ioc hdens_cont
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun s : ℝ => 2 * (1 - s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs1 : s ≤ 1 := (Set.mem_Ioc.mp hs).2
      change (0 : ℝ) ≤ 2 * (1 - s)
      linarith
    have hbase1 : ∫ s, (2 : ℝ) * (1 - s)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) = 1 := by
      rw [integral_const_mul, hIoc1, hint]
      norm_num
    calc ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
          (fun s => ENNReal.ofReal (2 * (1 - s)))) Set.univ
        = ∫⁻ s, ENNReal.ofReal (2 * (1 - s))
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      _ = ENNReal.ofReal (∫ s, (2 : ℝ) * (1 - s)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
          (ofReal_integral_eq_lintegral_ofReal hBoch hnn).symm
      _ = 1 := by rw [hbase1, ENNReal.ofReal_one]
  have hprob : IsProbabilityMeasure ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s)))) := ⟨hμ1⟩
  have hH_int : Integrable H ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s)))) := by
    rw [integrable_withDensity_iff hdens_meas hdens_top]
    have hcont : Continuous (fun x : ℝ => H x * (2 * (1 - x))) :=
      Continuous.mul hH hdens_cont
    have hknown : Integrable (fun x : ℝ => H x * (2 * (1 - x)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      Continuous.integrableOn_Ioc hcont
    refine Integrable.congr hknown ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    show H x * (2 * (1 - x))
      = H x * (ENNReal.ofReal (2 * (1 - x))).toReal
    rw [hdens_eq x hx]
  have hHq_int : Integrable ((fun x : ℝ => x ^ q) ∘ H)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun s => ENNReal.ofReal (2 * (1 - s)))) := by
    rw [integrable_withDensity_iff hdens_meas hdens_top]
    simp only [Function.comp_apply]
    have hcont : Continuous (fun x : ℝ => (H x) ^ q * (2 * (1 - x))) :=
      Continuous.mul hHq hdens_cont
    have hknown : Integrable (fun x : ℝ => (H x) ^ q * (2 * (1 - x)))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      Continuous.integrableOn_Ioc hcont
    refine Integrable.congr hknown ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    show (H x) ^ q * (2 * (1 - x))
      = (H x) ^ q * (ENNReal.ofReal (2 * (1 - x))).toReal
    rw [hdens_eq x hx]
  have hae : ∀ᵐ x ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s)))), H x ∈ Set.Ici (0 : ℝ) := by
    rw [ae_withDensity_iff hdens_meas]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx _
    exact Set.mem_Ici.mpr (hHnn x (Set.Ioc_subset_Icc_self hx))
  have hJ : (∫ x, H x ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s))))) ^ q
      ≤ ∫ x, (H x) ^ q ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
        (fun s => ENNReal.ofReal (2 * (1 - s)))) :=
    (convexOn_rpow hq).map_integral_le
      (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici hae hH_int hHq_int
  have hInt_H : ∫ x, H x ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s))))
      = 2 * ∫ s in (0 : ℝ)..1, (1 - s) * H s := by
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    simp only [smul_eq_mul]
    have hcongr : ∫ x, (ENNReal.ofReal (2 * (1 - x))).toReal * H x
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        = ∫ x, 2 * ((1 - x) * H x)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      show (ENNReal.ofReal (2 * (1 - x))).toReal * H x
        = 2 * ((1 - x) * H x)
      rw [hdens_eq x hx]
      ring
    rw [hcongr, integral_const_mul]
    congr 1
    exact (intervalIntegral.integral_of_le h01).symm
  have hInt_Hq : ∫ x, (H x) ^ q ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).withDensity
      (fun s => ENNReal.ofReal (2 * (1 - s))))
      = 2 * ∫ s in (0 : ℝ)..1, (1 - s) * (H s) ^ q := by
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_top]
    simp only [smul_eq_mul]
    have hcongr : ∫ x, (ENNReal.ofReal (2 * (1 - x))).toReal * (H x) ^ q
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        = ∫ x, 2 * ((1 - x) * (H x) ^ q)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      show (ENNReal.ofReal (2 * (1 - x))).toReal * (H x) ^ q
        = 2 * ((1 - x) * (H x) ^ q)
      rw [hdens_eq x hx]
      ring
    rw [hcongr, integral_const_mul]
    congr 1
    exact (intervalIntegral.integral_of_le h01).symm
  rw [hInt_H, hInt_Hq] at hJ
  rw [Real.mul_rpow h2nn hA] at hJ
  have h2q_eq : (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1) * 2 := by
    have hqq : q = (q - 1) + 1 := by ring
    conv_lhs => rw [hqq]
    rw [Real.rpow_add h2pos, Real.rpow_one]
  have hgoal_eq : ((1 : ℝ) / 2) ^ (q - 1)
      * ∫ s in (0 : ℝ)..1, (1 - s) * (H s) ^ q
      = (∫ s in (0 : ℝ)..1, (1 - s) * (H s) ^ q) / (2 : ℝ) ^ (q - 1) := by
    rw [Real.div_rpow h1nn h2nn, Real.one_rpow]
    ring
  rw [hgoal_eq, le_div_iff₀ (Real.rpow_pos_of_pos h2pos (q - 1))]
  rw [h2q_eq] at hJ
  linear_combination hJ / 2

private theorem Dfn_pointwise_rpow_le (n : ℕ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ (x y : EuclideanSpace ℝ (Fin n)),
      ‖Dfn n φ x y‖ ^ p.toReal
      ≤ ((1 : ℝ) / 2) ^ (p.toReal - 1)
        * ∫ s in (0 : ℝ)..1, (1 - s)
          * (∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal := by
  intro x y
  have hpTop : p ≠ ⊤ := ne_of_lt hp
  have hq1 : 1 ≤ p.toReal := by
    have h := ENNReal.toReal_mono hpTop hp1
    rwa [ENNReal.toReal_one] at h
  have hDij_cont : ∀ i j : Fin n, Continuous (secondPartialFn n φ i j) :=
    fun i j => (hDijThm i j).1
  have hlin : Continuous (fun s : ℝ => x - s • y) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have htermH : ∀ i j : Fin n, Continuous (fun s : ℝ => |y i * y j|
      * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) := by
    intro i j
    exact Continuous.mul continuous_const
      (Continuous.abs (Continuous.sub ((hDij_cont i j).comp hlin) continuous_const))
  have hHcont : Continuous (fun s : ℝ => ∑ i, ∑ j, |y i * y j|
      * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) :=
    continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => htermH i j
  have hHnn : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ∑ i, ∑ j, |y i * y j|
      * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x| := by
    intro s _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have htermS : ∀ i j : Fin n, Continuous (fun s : ℝ => y i * y j
      * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)) := by
    intro i j
    exact Continuous.mul continuous_const
      (Continuous.sub ((hDij_cont i j).comp hlin) continuous_const)
  have hScont : Continuous (fun s : ℝ => (1 - s) * ∑ i, ∑ j, y i * y j
      * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)) :=
    Continuous.mul (continuous_const.sub continuous_id)
      (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => htermS i j)
  have hcont2 : Continuous (fun s : ℝ => (1 - s) * (∑ i, ∑ j, |y i * y j|
      * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|)) :=
    Continuous.mul (continuous_const.sub continuous_id) hHcont
  have hstep1 : ‖Dfn n φ x y‖ ≤ ∫ s in (0 : ℝ)..1, (1 - s) * (∑ i, ∑ j,
      |y i * y j| * |secondPartialFn n φ i j (x - s • y)
        - secondPartialFn n φ i j x|) := by
    have hnorm : ‖∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j
          * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
        ≤ ∫ s in (0 : ℝ)..1, ‖(1 - s) * ∑ i, ∑ j, y i * y j
          * (secondPartialFn n φ i j (x - s • y)
            - secondPartialFn n φ i j x)‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    have hDfn : Dfn n φ x y = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j,
        y i * y j * (secondPartialFn n φ i j (x - s • y)
          - secondPartialFn n φ i j x) := rfl
    rw [hDfn]
    refine le_trans hnorm
      (intervalIntegral.integral_mono_on zero_le_one ?hint1 ?hint2 ?hpt)
    · exact hScont.norm.intervalIntegrable _ _
    · exact hcont2.intervalIntegrable _ _
    · intro s hs
      have hs1 : s ≤ 1 := (Set.mem_Icc.mp hs).2
      have hw : (0 : ℝ) ≤ 1 - s := by linarith
      have hnorm_eq : ‖(1 - s) * ∑ i, ∑ j, y i * y j
            * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
          = (1 - s) * ‖∑ i, ∑ j, y i * y j
            * (secondPartialFn n φ i j (x - s • y)
              - secondPartialFn n φ i j x)‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hw]
      have hterm_eq : ∀ i j : Fin n, ‖y i * y j
            * (secondPartialFn n φ i j (x - s • y)
              - secondPartialFn n φ i j x)‖
          = |y i * y j| * |secondPartialFn n φ i j (x - s • y)
            - secondPartialFn n φ i j x| := by
        intro i j
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hle : ‖∑ i, ∑ j, y i * y j
            * (secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x)‖
          ≤ ∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y)
              - secondPartialFn n φ i j x| := by
        calc ‖∑ i, ∑ j, y i * y j
                * (secondPartialFn n φ i j (x - s • y)
                  - secondPartialFn n φ i j x)‖
            ≤ ∑ i, ‖∑ j, y i * y j
                * (secondPartialFn n φ i j (x - s • y)
                  - secondPartialFn n φ i j x)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ i, ∑ j, ‖y i * y j
              * (secondPartialFn n φ i j (x - s • y)
                - secondPartialFn n φ i j x)‖ := by
              apply Finset.sum_le_sum; intro i _
              exact norm_sum_le _ _
          _ = ∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y)
                - secondPartialFn n φ i j x| := by
              apply Finset.sum_congr rfl; intro i _
              apply Finset.sum_congr rfl; intro j _
              exact hterm_eq i j
      rw [hnorm_eq]
      exact mul_le_mul_of_nonneg_left hle hw
  have hstep2 : ‖Dfn n φ x y‖ ^ p.toReal ≤ (∫ s in (0 : ℝ)..1, (1 - s)
      * (∑ i, ∑ j, |y i * y j|
        * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|))
        ^ p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) hstep1 (le_trans zero_le_one hq1)
  have hstep3 := aux_integral_one_sub_rpow_le
    (fun s : ℝ => ∑ i, ∑ j, |y i * y j|
      * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|)
    hHcont hHnn p.toReal hq1
  exact le_trans hstep2 hstep3

private theorem aux_integral_one_sub : ∫ s in (0 : ℝ)..1, (1 - s) = 1 / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s - s ^ 2 / 2) (1 - x) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
    have hp : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℕ) * x ^ (2 - 1)) x :=
      hasDerivAt_pow 2 x
    simp at hp
    have hdiv : HasDerivAt (fun s : ℝ => s ^ 2 / 2) x x := by
      have h := hp.div_const (2 : ℝ)
      simpa using h
    have hsub := h1.sub hdiv
    have heq : (fun s : ℝ => s - s ^ 2 / 2)
        = (fun s : ℝ => s) - (fun s : ℝ => s ^ 2 / 2) := by
      funext s
      rfl
    rw [heq]
    simpa using hsub
  have hint : IntervalIntegrable (fun s : ℝ => 1 - s) volume 0 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp at hftc
  linarith

private theorem aux_rpow_sum_le (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 ≤ q)
    (a b : Fin n → Fin n → ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hb : ∀ i j, 0 ≤ b i j) :
    (∑ i, ∑ j, a i j * b i j) ^ q
      ≤ (∑ i, ∑ j, a i j) ^ q * ∑ i, ∑ j, (b i j) ^ q := by
  classical
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty := by
    obtain ⟨k⟩ := Fin.pos_iff_nonempty.mp hn
    exact ⟨(k, k), Finset.mem_univ _⟩
  obtain ⟨w, _, hwmax⟩ := Finset.exists_max_image Finset.univ
    (fun z : Fin n × Fin n => b z.1 z.2) hne
  obtain ⟨i0, j0⟩ := w
  have hmax : ∀ i j, b i j ≤ b i0 j0 := fun i j => hwmax (i, j) (Finset.mem_univ _)
  have hsumle : ∑ i, ∑ j, a i j * b i j ≤ (∑ i, ∑ j, a i j) * b i0 j0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hmax i j) (ha i j)
  have hsum_nn : 0 ≤ ∑ i, ∑ j, a i j * b i j := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (ha i j) (hb i j)
  have hA_nn : 0 ≤ ∑ i, ∑ j, a i j := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact ha i j
  have hb0_nn : 0 ≤ b i0 j0 := hb i0 j0
  have hrpow_le : (∑ i, ∑ j, a i j * b i j) ^ q ≤ ((∑ i, ∑ j, a i j) * b i0 j0) ^ q :=
    Real.rpow_le_rpow hsum_nn hsumle hq
  rw [Real.mul_rpow hA_nn hb0_nn] at hrpow_le
  have hsingle : (b i0 j0) ^ q ≤ ∑ i, ∑ j, (b i j) ^ q := by
    have h1 : (b i0 j0) ^ q ≤ ∑ j, (b i0 j) ^ q := by
      apply Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hb i0 j) q) (Finset.mem_univ j0)
    have h2 : (∑ j, (b i0 j) ^ q) ≤ ∑ i, ∑ j, (b i j) ^ q := by
      apply Finset.single_le_sum _ (Finset.mem_univ i0)
      intro i _
      apply Finset.sum_nonneg
      intro j _
      exact Real.rpow_nonneg (hb i j) q
    exact h1.trans h2
  calc (∑ i, ∑ j, a i j * b i j) ^ q
      ≤ (∑ i, ∑ j, a i j) ^ q * (b i0 j0) ^ q := hrpow_le
    _ ≤ (∑ i, ∑ j, a i j) ^ q * ∑ i, ∑ j, (b i j) ^ q := by
        apply mul_le_mul_of_nonneg_left hsingle (Real.rpow_nonneg hA_nn q)

private theorem Dfn_lintegral_of_pointwise (n : ℕ) (hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p)
    (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hSumThm : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin n)),
      ∑ i : Fin n, ∑ j : Fin n, |y i * y j| ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2) :
    ∀ (C R : ℝ), 0 ≤ C → 0 ≤ R →
      (∀ (i j : Fin n) (y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
        ∫⁻ x, ENNReal.ofReal
          ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
          ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n)) →
      (∀ (x y : EuclideanSpace ℝ (Fin n)),
        ‖Dfn n φ x y‖ ^ p.toReal
        ≤ ((1 : ℝ) / 2) ^ (p.toReal - 1)
          * ∫ s in (0 : ℝ)..1, (1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) →
      ∀ y : EuclideanSpace ℝ (Fin n),
        (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
        ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
          p.toReal) * C)
          * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal)))
            := by
  intro C R hC hR hPer hPt y
  have _ := hφ
  have _ := hφ_supp
  have hp_ne : p ≠ ⊤ := ne_top_of_lt hp
  have hq1 : 1 ≤ p.toReal := by
    have h1 := ENNReal.toReal_mono hp_ne hp1
    simpa using h1
  have hq0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hCont : ∀ i j, Continuous (secondPartialFn n φ i j) :=
    fun i j => (hDijThm i j).1
  have hJoint : Continuous (fun z : EuclideanSpace ℝ (Fin n) × ℝ => z.1 - z.2 • y) :=
    continuous_fst.sub (continuous_snd.smul continuous_const)
  have hDiffJoint : ∀ i j, Continuous (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      secondPartialFn n φ i j (z.1 - z.2 • y) - secondPartialFn n φ i j z.1) := by
    intro i j
    exact ((hCont i j).comp hJoint).sub ((hCont i j).comp continuous_fst)
  have hSJoint : Continuous (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      ∑ i, ∑ j, |y i * y j|
        * |secondPartialFn n φ i j (z.1 - z.2 • y) - secondPartialFn n φ i j z.1|) := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul ((hDiffJoint i j).abs)
  have hGJoint : Continuous (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      (1 - z.2) * (∑ i, ∑ j, |y i * y j|
        * |secondPartialFn n φ i j (z.1 - z.2 • y) - secondPartialFn n φ i j z.1|) ^ p.toReal) := by
    apply Continuous.mul
    · exact continuous_const.sub continuous_snd
    · exact hSJoint.rpow_const (fun _ => Or.inr hq0)
  have hGx : ∀ x : EuclideanSpace ℝ (Fin n), Continuous (fun s : ℝ =>
      (1 - s) * (∑ i, ∑ j, |y i * y j|
        * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) := by
    intro x
    exact hGJoint.comp (continuous_const.prodMk continuous_id)
  have hDiffX : ∀ (s : ℝ) (i j : Fin n), Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) := by
    intro s i j
    exact ((hDiffJoint i j).comp (continuous_id.prodMk continuous_const)).abs
  have hK1_nn : 0 ≤ ((1 : ℝ) / 2) ^ (p.toReal - 1) :=
    Real.rpow_nonneg (by norm_num) _
  have stepA : (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
      ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ∫⁻ x,
        ENNReal.ofReal (∫ s in (0 : ℝ)..1, (1 - s)
          * (∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
              ∂volume := by
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
          ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ENNReal.ofReal (∫ s in (0 : ℝ)..1, (1
            - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) := by
      intro x
      have hrw : ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
          = ENNReal.ofReal (‖Dfn n φ x y‖ ^ p.toReal) :=
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0
      rw [hrw]
      have hle := hPt x y
      have hof : ENNReal.ofReal (‖Dfn n φ x y‖ ^ p.toReal)
          ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)
            * ∫ s in (0 : ℝ)..1, (1 - s)
              * (∑ i, ∑ j, |y i * y j|
                * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) :=
        ENNReal.ofReal_le_ofReal hle
      rwa [ENNReal.ofReal_mul hK1_nn] at hof
    calc (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
        ≤ ∫⁻ x, ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ENNReal.ofReal (∫ s in (0 :
          ℝ)..1, (1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
                ∂volume :=
          lintegral_mono hpoint
      _ = ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ∫⁻ x,
          ENNReal.ofReal (∫ s in (0 : ℝ)..1, (1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
                ∂volume :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hS_nn : ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ),
      0 ≤ ∑ i, ∑ j, |y i * y j|
        * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x| := by
    intro x s
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hconv : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (∫ s in (0 : ℝ)..1, (1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
      = ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume
            := by
    intro x
    have hInt : Integrable (fun s : ℝ => (1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
        (volume.restrict (Set.Ioc 0 1)) := by
      have h1 : IntervalIntegrable (fun s : ℝ => (1 - s)
          * (∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
          volume 0 1 := (hGx x).intervalIntegrable 0 1
      have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h1
      exact h2
    have hNn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => (1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) := by
      apply (ae_restrict_mem measurableSet_Ioc).mono
      intro s hs
      simp only [Set.mem_Ioc] at hs
      apply mul_nonneg
      · linarith [hs.2]
      · exact Real.rpow_nonneg (hS_nn x s) _
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact ofReal_integral_eq_lintegral_ofReal hInt hNn
  have hmeas : AEMeasurable (Function.uncurry (fun x : EuclideanSpace ℝ (Fin n) => fun s : ℝ =>
      ENNReal.ofReal ((1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    apply Measurable.aemeasurable
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
        ENNReal.ofReal ((1 - z.2)
          * (∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (z.1 - z.2 • y) - secondPartialFn n φ i j z.1|) ^ p.toReal))
              :=
      ENNReal.continuous_ofReal.comp hGJoint
    exact hcont.measurable
  have hswap : (∫⁻ x, ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume
            ∂volume)
      = ∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ x, ENNReal.ofReal ((1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume
            ∂volume :=
    lintegral_lintegral_swap hmeas
  have hMod_nn : ∀ i j (r : ℝ), 0 ≤ secondPartialModulus n φ i j r :=
    fun i j r => ((hDijThm i j).2.2.2.1) r
  have hInner : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (∫⁻ x, ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|
        * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume)
      ≤ ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
        * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n)) := by
    intro s hs0 hs1
    have hmeas_ij : ∀ i j, Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^
          p.toReal)) := by
      intro i j
      exact (ENNReal.continuous_ofReal.comp ((hDiffX s i j).rpow_const (fun _ => Or.inr
        hq0))).measurable
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
        ≤ ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (∑ i, ∑ j, ENNReal.ofReal (((|secondPartialFn n φ i j (x - s • y)
            - secondPartialFn n φ i j x|)) ^ p.toReal)) := by
      intro x
      have hrb := aux_rpow_sum_le n hn p.toReal hq0
        (fun i j => |y i * y j|)
        (fun i j => |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|)
        (fun i j => abs_nonneg _) (fun i j => abs_nonneg _)
      have hof := ENNReal.ofReal_le_ofReal hrb
      have hAq_nn : 0 ≤ (∑ i, ∑ j, |y i * y j|) ^ p.toReal :=
        Real.rpow_nonneg (by positivity) _
      rw [ENNReal.ofReal_mul hAq_nn] at hof
      have hsum_rw : ENNReal.ofReal (∑ i, ∑ j,
          (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
          = (∑ i, ∑ j, ENNReal.ofReal (
            (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · apply Finset.sum_congr rfl
          intro i _
          exact ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
        · intro i _
          exact Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
      rwa [hsum_rw] at hof
    have hle_ij : ∀ i j, (∫⁻ x, ENNReal.ofReal (
          (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume)
        ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n) := by
      intro i j
      have heq : ∀ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal ((|secondPartialFn n φ i j (x - s • y)
            - secondPartialFn n φ i j x|) ^ p.toReal)
          = ENNReal.ofReal ‖secondPartialFn n φ i j (x - s • y)
            - secondPartialFn n φ i j x‖ ^ p.toReal := by
        intro x
        rw [← Real.norm_eq_abs]
        exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0).symm
      simp_rw [heq]
      exact hPer i j y s hs0 hs1
    calc (∫⁻ x, ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume)
        ≤ ∫⁻ x, ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
            * (∑ i, ∑ j, ENNReal.ofReal (
              (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal))
                ∂volume :=
          lintegral_mono hpoint
      _ = ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * ∫⁻ x, (∑ i, ∑ j, ENNReal.ofReal (
            (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal))
              ∂volume :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (∑ i, ∑ j, ∫⁻ x, ENNReal.ofReal (
            (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
              ∂volume) := by
          congr 1
          rw [lintegral_finsetSum Finset.univ]
          · apply Finset.sum_congr rfl
            intro i _
            exact lintegral_finsetSum Finset.univ (fun j _ => hmeas_ij i j)
          · intro i _
            have hci : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
                ∑ j, ENNReal.ofReal (
                  (|secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal))
                    := by
              apply continuous_finsetSum
              intro j _
              exact ENNReal.continuous_ofReal.comp ((hDiffX s i j).rpow_const (fun _ => Or.inr hq0))
            exact hci.measurable
      _ ≤ ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n)) := by
          gcongr
          exact hle_ij _ _
  have hHs : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      (∫⁻ x, ENNReal.ofReal ((1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume)
      ≤ ENNReal.ofReal (1 - s) * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
        * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))) := by
    intro s hs
    simp only [Set.mem_Ioc] at hs
    have hs1 : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
    have hpull : (∫⁻ x, ENNReal.ofReal ((1 - s)
          * (∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
              ∂volume)
        = ENNReal.ofReal (1 - s) * ∫⁻ x, ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume
            := by
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal ((1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
          = ENNReal.ofReal (1 - s) * ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) := by
        intro x
        exact ENNReal.ofReal_mul hs1
      simp_rw [hpt]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hpull]
    gcongr
    exact hInner s (le_of_lt hs.1) hs.2
  have hB_ne : (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
        * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.mpr (fun i _ =>
        ENNReal.sum_ne_top.mpr (fun j _ => ENNReal.ofReal_ne_top)))
  have hOuter : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ x, ENNReal.ofReal ((1 - s)
        * (∑ i, ∑ j, |y i * y j|
          * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal) ∂volume
            ∂volume)
      ≤ (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - s) ∂volume)
        * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))) := by
    have hmono : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ x, ENNReal.ofReal ((1 - s)
          * (∑ i, ∑ j, |y i * y j|
            * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
              ∂volume ∂volume)
        ≤ ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - s) * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y
          j|) ^ p.toReal)
          * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n)))
            ∂volume := by
      apply lintegral_mono_ae
      apply (ae_restrict_mem measurableSet_Ioc).mono
      intro s hs
      exact hHs s hs
    rw [lintegral_mul_const' _ _ hB_ne] at hmono
    exact hmono
  have hInt1 : Integrable (fun s : ℝ => 1 - s) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h1 : IntervalIntegrable (fun s : ℝ => 1 - s) volume 0 1 :=
      (continuous_const.sub continuous_id).intervalIntegrable 0 1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h1
  have hNn1 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => 1 - s) := by
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro s hs
    simp only [Set.mem_Ioc] at hs
    change (0 : ℝ) ≤ 1 - s
    linarith [hs.2]
  have hHalf : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - s) ∂volume)
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hInt1 hNn1
    have h2 : (∫ s in Set.Ioc (0 : ℝ) 1, (1 - s) ∂volume) = ∫ s in (0 : ℝ)..1, (1 - s) :=
      (intervalIntegral.integral_of_le zero_le_one).symm
    rw [h2, aux_integral_one_sub] at h1
    exact h1.symm
  have hchain : (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
      ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * (ENNReal.ofReal ((1 : ℝ) / 2)
        * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n)))) :=
            by
    calc (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
        ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ∫⁻ x,
          ENNReal.ofReal (∫ s in (0 : ℝ)..1, (1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
                ∂volume :=
          stepA
      _ = ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ∫⁻ x,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
                ∂volume) ∂volume := by
          simp only [hconv]
      _ = ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          (∫⁻ x, ENNReal.ofReal ((1 - s)
            * (∑ i, ∑ j, |y i * y j|
              * |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|) ^ p.toReal)
                ∂volume) ∂volume := by
          rw [hswap]
      _ ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1))
          * ((∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (1 - s) ∂volume)
            * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
              * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))))
                := by
          gcongr
      _ = ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * (ENNReal.ofReal ((1 : ℝ) / 2)
          * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
            * (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))))
              := by
          rw [hHalf]
  have hP_nn : 0 ≤ (R + ‖y‖) ^ n := by
    apply pow_nonneg
    linarith [norm_nonneg y, hR]
  have hSumMod : (∑ i, ∑ j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))
      = (ENNReal.ofReal C * ENNReal.ofReal (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖))
        * ENNReal.ofReal ((R + ‖y‖) ^ n) := by
    have hpt : ∀ i j, ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n)
        = (ENNReal.ofReal C * ENNReal.ofReal (secondPartialModulus n φ i j ‖y‖))
          * ENNReal.ofReal ((R + ‖y‖) ^ n) := by
      intro i j
      rw [ENNReal.ofReal_mul (mul_nonneg hC (hMod_nn i j _)), ENNReal.ofReal_mul hC]
    simp_rw [hpt]
    simp_rw [← Finset.sum_mul]
    congr 1
    simp_rw [← Finset.mul_sum]
    congr 1
    have h : ENNReal.ofReal (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
        = ∑ i, ∑ j, ENNReal.ofReal (secondPartialModulus n φ i j ‖y‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => hMod_nn i j _))]
      apply Finset.sum_congr rfl
      intro i _
      exact ENNReal.ofReal_sum_of_nonneg (fun j _ => hMod_nn i j _)
    exact h.symm
  have hA_nn : 0 ≤ ∑ i, ∑ j, |y i * y j| := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact abs_nonneg _
  have hAq_nn : 0 ≤ (∑ i, ∑ j, |y i * y j|) ^ p.toReal :=
    Real.rpow_nonneg hA_nn _
  have hN_nn : 0 ≤ (n : ℝ) ^ 2 := pow_nonneg (Nat.cast_nonneg _) _
  have hNq_nn : 0 ≤ (((n : ℝ) ^ 2) ^ p.toReal) := Real.rpow_nonneg hN_nn _
  have hY_nn : 0 ≤ ‖y‖ ^ (2 * p.toReal) := Real.rpow_nonneg (norm_nonneg _) _
  have hM_nn : 0 ≤ ∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖ := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact hMod_nn i j _
  have hAq_le : (∑ i, ∑ j, |y i * y j|) ^ p.toReal
      ≤ (((n : ℝ) ^ 2) ^ p.toReal) * ‖y‖ ^ (2 * p.toReal) := by
    have hsum := hSumThm n y
    have hNY_nn : 0 ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2 :=
      mul_nonneg hN_nn (pow_nonneg (norm_nonneg _) _)
    have hrw : (∑ i, ∑ j, |y i * y j|) ^ p.toReal ≤ ((n : ℝ) ^ 2 * ‖y‖ ^ 2) ^ p.toReal :=
      Real.rpow_le_rpow hA_nn hsum hq0
    rw [Real.mul_rpow hN_nn (pow_nonneg (norm_nonneg _) _)] at hrw
    have hY2 : ((‖y‖ ^ 2 : ℝ)) ^ p.toReal = ‖y‖ ^ (2 * p.toReal) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (norm_nonneg _)]
      simp
    rw [hY2] at hrw
    exact hrw
  have hH_nn : (0 : ℝ) ≤ (1 : ℝ) / 2 := by norm_num
  have hK_nn : 0 ≤ ((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2)
      * C * (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK1_nn hH_nn) hC) hM_nn) hP_nn
  rw [hSumMod] at hchain
  have hOfEq : ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * (ENNReal.ofReal ((1 : ℝ) / 2)
        * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * ((ENNReal.ofReal C * ENNReal.ofReal (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖))
            * ENNReal.ofReal ((R + ‖y‖) ^ n))))
      = ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1))
        * (((1 : ℝ) / 2) * (((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (((C * (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)) * (R + ‖y‖) ^ n))))) := by
    rw [← ENNReal.ofReal_mul hC]
    rw [← ENNReal.ofReal_mul (mul_nonneg hC hM_nn)]
    rw [← ENNReal.ofReal_mul hAq_nn]
    rw [← ENNReal.ofReal_mul hH_nn]
    rw [← ENNReal.ofReal_mul hK1_nn]
  have hReal_le : ((((1 : ℝ) / 2) ^ (p.toReal - 1))
        * (((1 : ℝ) / 2) * (((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (((C * (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)) * (R + ‖y‖) ^ n)))))
      ≤ ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
        * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal))) :=
          by
    have h := mul_le_mul_of_nonneg_left hAq_le hK_nn
    linear_combination h
  calc (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
      ≤ ENNReal.ofReal (((1 : ℝ) / 2) ^ (p.toReal - 1)) * (ENNReal.ofReal ((1 : ℝ) / 2)
        * (ENNReal.ofReal ((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * ((ENNReal.ofReal C * ENNReal.ofReal (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖))
            * ENNReal.ofReal ((R + ‖y‖) ^ n)))) := hchain
    _ = ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1))
        * (((1 : ℝ) / 2) * (((∑ i, ∑ j, |y i * y j|) ^ p.toReal)
          * (((C * (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)) * (R + ‖y‖) ^ n))))) := hOfEq
    _ ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
      p.toReal) * C)
        * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal))) :=
        ENNReal.ofReal_le_ofReal hReal_le

private theorem Dfn_lintegral_le_v2 (n : ℕ) (hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p)
    (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    (hAthm : ∀ (n : ℕ) (_hn : 0 < n) {p : ENNReal} (_hp1 : 1 ≤ p) (_hp : p < ⊤)
      {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
      (_hφ_supp : HasCompactSupport φ)
      (_hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
      (_hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        (∀ (x z : EuclideanSpace ℝ (Fin n)),
          |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
            ≤ secondPartialModulus n φ i j ‖z‖) →
        ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
        |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖y‖),
      ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ (i j : Fin n) (y : EuclideanSpace ℝ (Fin n))
        (s : ℝ), 0 ≤ s → s ≤ 1 →
        ∫⁻ x, ENNReal.ofReal
          ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
          ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))
    (hSumThm : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin n)),
      ∑ i : Fin n, ∑ j : Fin n, |y i * y j| ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2)
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ y : EuclideanSpace ℝ (Fin n),
      (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
      ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
        * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal))) :=
          by
  -- `hSub` glue (coordinator): domination + modulus monotonicity.
  have hSub : ∀ (n' : ℕ) {φ' : EuclideanSpace ℝ (Fin n') → ℝ} (i j : Fin n'),
      Continuous (secondPartialFn n' φ' i j) → HasCompactSupport (secondPartialFn n' φ' i j) →
      (∀ (x z : EuclideanSpace ℝ (Fin n')), |secondPartialFn n' φ' i j (x - z) - secondPartialFn n'
        φ' i j x| ≤ secondPartialModulus n' φ' i j ‖z‖) →
      ∀ (x y : EuclideanSpace ℝ (Fin n')) (s : ℝ), 0 ≤ s → s ≤ 1 →
      |secondPartialFn n' φ' i j (x - s • y) - secondPartialFn n' φ' i j x| ≤ secondPartialModulus
        n' φ' i j ‖y‖ := by
    intro n' φ' i j hcont hsupp hdom x y s hs0 hs1
    refine (hdom x (s • y)).trans ?_
    refine secondPartialModulus_mono_aux n' φ' i j hcont hsupp (norm_nonneg _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_of_le_one_left (norm_nonneg _) hs1
  obtain ⟨C, R, hC, hR, hA⟩ := hAthm n hn hp1 hp hφ hφ_supp hDijThm hSub
  exact ⟨C, R, hC, hR, fun y => Dfn_lintegral_of_pointwise n hn hp1 hp hφ hφ_supp hDijThm hSumThm C
    R hC hR hA (fun x y => Dfn_pointwise_rpow_le n hp1 hp hDijThm x y) y⟩

end C2bypass

section C3

-- Heat-kernel integral estimate by a small-ball / large-tail split (`δ`).
-- Gaussian helper lemmas are proved from the Gaussian integral over Euclidean space.
-- The final absorption step is proved as `habsorb` inside the main estimate below.

open MeasureTheory
open scoped Topology


/-- Global bound on the modulus from a uniform bound on `D_{ij}`. -/
private theorem modulus_le_two_mul_bound (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (i j : Fin n) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ x, |secondPartialFn n φ i j x| ≤ M)
    (r : ℝ) (hr : 0 ≤ r) :
    secondPartialModulus n φ i j r ≤ 2 * M := by
  have _ : 0 ≤ M := hM0
  unfold secondPartialModulus
  apply csSup_le _ _
  · exact ⟨_, 0, 0, by simpa using hr, rfl⟩
  · intro v hv
    obtain ⟨x, z, -, rfl⟩ := hv
    calc |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
        ≤ |secondPartialFn n φ i j (x - z)| + |secondPartialFn n φ i j x| := by
          have h := abs_add_le (secondPartialFn n φ i j (x - z))
            (-secondPartialFn n φ i j x)
          simpa [sub_eq_add_neg] using h
      _ ≤ M + M := add_le_add (hM _) (hM _)
      _ = 2 * M := by ring

private theorem add_pow_le_two_pow_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ (2 : ℝ) ^ n * (a ^ n + b ^ n) := by
  have hmax : a + b ≤ 2 * max a b := by
    have h1 : a ≤ max a b := by simp
    have h2 : b ≤ max a b := by simp
    linarith
  have hpow : (a + b) ^ n ≤ (2 * max a b) ^ n :=
    pow_le_pow_left₀ (by positivity) hmax n
  rw [mul_pow] at hpow
  have hmaxpow : (max a b) ^ n ≤ a ^ n + b ^ n := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
  calc (a + b) ^ n ≤ (2 : ℝ) ^ n * (max a b) ^ n := hpow
    _ ≤ (2 : ℝ) ^ n * (a ^ n + b ^ n) :=
        mul_le_mul_of_nonneg_left hmaxpow (by positivity)

/-- Pointwise polynomial-exponential bound: `u^s ≤ s^s * exp u`. -/
private theorem rpow_le_rpow_mul_exp (u s : ℝ) (hu : 0 ≤ u) (hs : 0 < s) :
    u ^ s ≤ s ^ s * Real.exp u := by
  rcases eq_or_lt_of_le hu with rfl | hu_pos
  · rw [Real.zero_rpow hs.ne']
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hs) s) (Real.exp_pos _).le
  · have h1 : Real.log (u / s) ≤ u / s := by
      have h := Real.log_le_sub_one_of_pos (div_pos hu_pos hs)
      linarith
    have h2 : Real.log u - Real.log s = Real.log (u / s) :=
      (Real.log_div hu_pos.ne' hs.ne').symm
    have h3 : s * (Real.log u - Real.log s) ≤ u := by
      have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt hs)
      rw [← h2] at hmul
      have h4 : s * (u / s) = u := by
        rw [mul_comm s, div_mul_cancel₀ _ hs.ne']
      rw [h4] at hmul
      exact hmul
    have hlog : s * Real.log u ≤ s * Real.log s + u := by
      have := h3
      rw [mul_sub] at this
      linarith
    have e1 : u ^ s = Real.exp (s * Real.log u) := by
      rw [← Real.log_rpow hu_pos s, Real.exp_log (Real.rpow_pos_of_pos hu_pos s)]
    have e2 : Real.exp (s * Real.log s + u) = s ^ s * Real.exp u := by
      rw [Real.exp_add]
      congr 1
      rw [← Real.log_rpow hs s, Real.exp_log (Real.rpow_pos_of_pos hs s)]
    rw [e1]
    rw [← e2]
    exact Real.exp_le_exp.mpr hlog

/-- Gaussian lintegral over Euclidean space. -/
private theorem gauss_lintegral (n : ℕ) (b : ℝ) (hb : 0 < b) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (Real.exp (-b * ‖y‖ ^ 2))
      = ENNReal.ofReal ((Real.pi / b) ^ ((n : ℝ) / 2)) := by
  have hInt : Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-b * ‖y‖ ^ 2)) volume := by
    by_contra hcon
    have hval := GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := EuclideanSpace ℝ (Fin n)) (b := b) hb
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    rw [hfr] at hval
    rw [integral_undef hcon] at hval
    have hpos : 0 < (Real.pi / b) ^ ((n : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact hpos.ne' hval.symm
  have hae : 0 ≤ᵐ[volume]
      (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-b * ‖y‖ ^ 2)) :=
    Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le)
  have hval2 := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin n)) (b := b) hb
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  rw [hfr] at hval2
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hae, hval2]

/-- Gaussian moment core estimate (pointwise in the radius). -/
private theorem moment_core (r t s : ℝ) (hr : 0 ≤ r) (ht : 0 < t) (hs : 0 < s) :
    r ^ (2 * s) * Real.exp (-r ^ 2 / (4 * t))
      ≤ (8 * t) ^ s * s ^ s * Real.exp (-r ^ 2 / (8 * t)) := by
  have ht0 : t ≠ 0 := ht.ne'
  have h8t0 : (0:ℝ) ≤ 8 * t := by positivity
  have hu0 : 0 ≤ r ^ 2 / (8 * t) := by positivity
  have h8t : (8:ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht0
  have hr2 : r ^ 2 = 8 * t * (r ^ 2 / (8 * t)) := by field
  have hkey := rpow_le_rpow_mul_exp (r ^ 2 / (8 * t)) s hu0 hs
  have hr2s : r ^ (2 * s) = (8 * t) ^ s * (r ^ 2 / (8 * t)) ^ s := by
    have e : r ^ (2 * s) = (r ^ 2) ^ s := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hr]
      congr 1
    conv_lhs => rw [e]
    conv_lhs => rw [hr2]
    rw [Real.mul_rpow h8t0 hu0]
  rw [hr2s]
  have hmul : ((8 * t) ^ s * Real.exp (-r ^ 2 / (4 * t))) * (r ^ 2 / (8 * t)) ^ s
      ≤ ((8 * t) ^ s * Real.exp (-r ^ 2 / (4 * t)))
        * (s ^ s * Real.exp (r ^ 2 / (8 * t))) :=
    mul_le_mul_of_nonneg_left hkey
      (mul_nonneg (Real.rpow_nonneg h8t0 _) (Real.exp_pos _).le)
  have hexp : Real.exp (r ^ 2 / (8 * t)) * Real.exp (-r ^ 2 / (4 * t))
      = Real.exp (-r ^ 2 / (8 * t)) := by
    have h4t : (4:ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht0
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc (8 * t) ^ s * (r ^ 2 / (8 * t)) ^ s * Real.exp (-r ^ 2 / (4 * t))
      = ((8 * t) ^ s * Real.exp (-r ^ 2 / (4 * t))) * (r ^ 2 / (8 * t)) ^ s := by ring
    _ ≤ ((8 * t) ^ s * Real.exp (-r ^ 2 / (4 * t)))
        * (s ^ s * Real.exp (r ^ 2 / (8 * t))) := hmul
    _ = (8 * t) ^ s * s ^ s * Real.exp (-r ^ 2 / (8 * t)) := by
        have hring : ((8 * t) ^ s * Real.exp (-r ^ 2 / (4 * t)))
            * (s ^ s * Real.exp (r ^ 2 / (8 * t)))
            = (8 * t) ^ s * s ^ s
              * (Real.exp (r ^ 2 / (8 * t)) * Real.exp (-r ^ 2 / (4 * t))) := by ring
        rw [hring, hexp]

/-- Gaussian `2q`-moment bound over a ball (small part of the `δ`-split).
Proved via a pointwise polynomial-Gaussian bound plus the Gaussian integral. -/
private theorem smallBall_integral_bound (n : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cmom : ℝ, 0 ≤ Cmom ∧ ∀ (δ t : ℝ), 0 < δ → 0 < t → ∀ (C0 : ℝ), 0 ≤ C0 →
      ∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ,
        ENNReal.ofReal (Φ n t y) * ENNReal.ofReal (C0 * ‖y‖ ^ (2 * q)) ∂volume
        ≤ ENNReal.ofReal (C0 * (Cmom * t ^ q)) := by
  refine ⟨(8:ℝ)^q * q^q * 2^((n:ℝ)/2), ?_, fun δ t hδ ht C0 hC0 => ?_⟩
  · have hq0 : 0 ≤ q := by linarith
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hq0 _)) (Real.rpow_nonneg (by norm_num) _)
  · have hq0 : 0 ≤ q := by linarith
    have hqpos : 0 < q := by linarith
    have ht0 : t ≠ 0 := ht.ne'
    have h8t0 : (0:ℝ) ≤ 8 * t := by positivity
    have h4pt0 : (0:ℝ) ≤ 4 * Real.pi * t := by positivity
    have hK0 : 0 ≤ C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ((8 * t) ^ q * q ^ q) :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg h4pt0 _))
        (mul_nonneg (Real.rpow_nonneg h8t0 _) (Real.rpow_nonneg hq0 _))
    have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (Φ n t y) * ENNReal.ofReal (C0 * ‖y‖ ^ (2 * q))
          ≤ ENNReal.ofReal ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ((8 * t) ^ q * q ^ q))
            * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by
      intro y
      rw [← ENNReal.ofReal_mul (heatKernel_nonneg n t ht y)]
      apply ENNReal.ofReal_le_ofReal
      have hcore := moment_core ‖y‖ t q (norm_nonneg y) ht hqpos
      have hmul2 : C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          ≤ C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * ((8 * t) ^ q * q ^ q * Real.exp (-‖y‖ ^ 2 / (8 * t))) :=
        mul_le_mul_of_nonneg_left hcore
          (mul_nonneg hC0 (Real.rpow_nonneg h4pt0 _))
      rw [heatKernel_euclideanSpace]
      have eL : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t)) * (C0 * ‖y‖ ^ (2
        * q))
          = C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (4 * t))) := by ring
      have eR : (C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ((8 * t) ^ q * q ^ q))
            * Real.exp (-‖y‖ ^ 2 / (8 * t))
          = C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * ((8 * t) ^ q * q ^ q * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by ring
      rw [eL, eR]
      exact hmul2
    have hstep1 : (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ,
          ENNReal.ofReal (Φ n t y) * ENNReal.ofReal (C0 * ‖y‖ ^ (2 * q)) ∂volume)
        ≤ ∫⁻ y, ENNReal.ofReal (Φ n t y)
          * ENNReal.ofReal (C0 * ‖y‖ ^ (2 * q)) ∂volume :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    have hstep2 : (∫⁻ y, ENNReal.ofReal (Φ n t y)
          * ENNReal.ofReal (C0 * ‖y‖ ^ (2 * q)) ∂volume)
        ≤ ∫⁻ y, ENNReal.ofReal ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ((8 * t) ^ q * q ^ q))
            * Real.exp (-‖y‖ ^ 2 / (8 * t))) ∂volume :=
      lintegral_mono (fun y => hpt y)
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => -‖y‖ ^ 2 / (8 * t)) := by
      simp only [div_eq_mul_inv]
      continuity
    have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / (8 * t)))) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hcont)).measurable
    have hstep3 : (∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
          ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ((8 * t) ^ q * q ^ q))
            * Real.exp (-‖y‖ ^ 2 / (8 * t))) ∂volume)
        = ENNReal.ofReal (C0 * (((8:ℝ)^q * q^q * 2^((n:ℝ)/2)) * t ^ q)) := by
      have hpt2 : ∀ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / (8 * t)))
            = ENNReal.ofReal (Real.exp (-(1 / (8 * t)) * ‖y‖ ^ 2)) := by
        intro y
        congr 1
        congr 1
        ring
      have hI : (∫⁻ y : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / (8 * t))) ∂volume)
          = ENNReal.ofReal ((8 * Real.pi * t) ^ ((n : ℝ) / 2)) := by
        have hG := gauss_lintegral n (1 / (8 * t)) (by positivity)
        have hpi : Real.pi / (1 / (8 * t)) = 8 * Real.pi * t := by
          rw [div_div_eq_mul_div, div_one]
          ring
        rw [hpi] at hG
        simp only [hpt2]
        exact hG
      simp only [ENNReal.ofReal_mul hK0, lintegral_const_mul _ hmeas, hI]
      rw [← ENNReal.ofReal_mul hK0]
      congr 1
      have e1 : ((8:ℝ) * t) ^ q = 8 ^ q * t ^ q := Real.mul_rpow (by norm_num) ht.le
      have h4pt : 4 * Real.pi * t ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht0
      have h8pt0 : (0:ℝ) ≤ 8 * Real.pi * t := by positivity
      have hdiv : (8 * Real.pi * t) / (4 * Real.pi * t) = 2 := by
        rw [div_eq_iff h4pt]; ring
      have e2 : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (8 * Real.pi * t) ^ ((n : ℝ) / 2)
          = 2 ^ ((n : ℝ) / 2) := by
        rw [neg_div, Real.rpow_neg h4pt0,
          ← div_eq_inv_mul, ← Real.div_rpow h8pt0 h4pt0, hdiv]
      calc C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ((8 * t) ^ q * q ^ q)
            * (8 * Real.pi * t) ^ ((n : ℝ) / 2)
          = C0 * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (8 * Real.pi * t) ^ ((n : ℝ) / 2))
            * ((8 * t) ^ q * q ^ q) := by ring
        _ = C0 * 2 ^ ((n : ℝ) / 2) * (8 ^ q * t ^ q * q ^ q) := by rw [e1, e2]
        _ = C0 * ((8 ^ q * q ^ q * 2 ^ ((n : ℝ) / 2)) * t ^ q) := by ring
    exact (le_trans (le_trans hstep1 hstep2) hstep3.le)

private theorem largeCompl_integral_bound (n : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ (R δ t : ℝ), 0 ≤ R → 0 < δ → 0 < t →
      ∀ (C0 : ℝ), 0 ≤ C0 →
      ∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ,
        ENNReal.ofReal (Φ n t y)
          * ENNReal.ofReal (C0 * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q))) ∂volume
        ≤ ENNReal.ofReal (C0 * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t)))) := by
  refine ⟨(16:ℝ)^q * q^q * 2^n, (16:ℝ)^(q + (n:ℝ)/2) * (q + (n:ℝ)/2)^(q + (n:ℝ)/2) * 2^n,
    ?_, ?_, fun R δ t hR hδ ht C0 hC0 => ?_⟩
  · have hq0 : 0 ≤ q := by linarith
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hq0 _)) (pow_nonneg (by norm_num) _)
  · have hq0 : 0 ≤ q := by linarith
    have hqn0 : (0:ℝ) ≤ q + (n:ℝ)/2 := by
      have hn0 : (0:ℝ) ≤ (n:ℝ)/2 := by positivity
      linarith
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hqn0 _)) (pow_nonneg (by norm_num) _)
  · have hq0 : 0 ≤ q := by linarith
    have hqpos : 0 < q := by linarith
    have hqnpos : 0 < q + (n:ℝ)/2 := by
      have hn0 : (0:ℝ) ≤ (n:ℝ)/2 := by positivity
      linarith
    have ht0 : t ≠ 0 := ht.ne'
    have h4pt0 : (0:ℝ) ≤ 4 * Real.pi * t := by positivity
    have h16t0 : (0:ℝ) ≤ 16 * t := by positivity
    have h16 : (8:ℝ) * (2 * t) = 16 * t := by ring
    have h8 : (4:ℝ) * (2 * t) = 8 * t := by ring
    have h2tpos : 0 < 2 * t := by positivity
    have hK0 : 0 ≤ C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
        * (R ^ n * ((16 * t) ^ q * q ^ q) + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q +
          (n:ℝ)/2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg h4pt0 _)) (Real.exp_pos _).le)
        (add_nonneg (mul_nonneg (pow_nonneg hR _)
          (mul_nonneg (Real.rpow_nonneg h16t0 _) (Real.rpow_nonneg hq0 _)))
          (mul_nonneg (Real.rpow_nonneg h16t0 _) (Real.rpow_nonneg hqnpos.le _)))
    have hpt : ∀ y : EuclideanSpace ℝ (Fin n), δ ≤ ‖y‖ →
        ENNReal.ofReal (Φ n t y)
          * ENNReal.ofReal (C0 * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q)))
          ≤ ENNReal.ofReal ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
            * (R ^ n * ((16 * t) ^ q * q ^ q) + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q +
              (n:ℝ)/2)))
            * Real.exp (-‖y‖ ^ 2 / (16 * t))) := by
      intro y hrδ
      have hr0 : 0 ≤ ‖y‖ := norm_nonneg y
      have hrpos : 0 < ‖y‖ := lt_of_lt_of_le hδ hrδ
      have hδr : δ ^ 2 ≤ 2 * ‖y‖ ^ 2 := by
        have h1 : δ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (le_of_lt hδ) hrδ 2
        have h2 := sq_nonneg ‖y‖
        linarith
      have hfrac : δ ^ 2 / (16 * t) ≤ ‖y‖ ^ 2 / (8 * t) := by
        have h16tpos : (0:ℝ) < 16 * t := by positivity
        have h8tpos : (0:ℝ) < 8 * t := by positivity
        rw [div_le_div_iff₀ h16tpos h8tpos]
        calc δ ^ 2 * (8 * t) ≤ (2 * ‖y‖ ^ 2) * (8 * t) :=
              mul_le_mul_of_nonneg_right hδr (by positivity)
          _ = ‖y‖ ^ 2 * (16 * t) := by ring
      have hexp_tail : Real.exp (-‖y‖ ^ 2 / (4 * t))
          ≤ Real.exp (-δ ^ 2 / (16 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t)) := by
        have hsplit : Real.exp (-‖y‖ ^ 2 / (4 * t))
            = Real.exp (-δ ^ 2 / (16 * t))
              * Real.exp (-(‖y‖ ^ 2 / (4 * t) - δ ^ 2 / (16 * t))) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hrel : ‖y‖ ^ 2 / (4 * t) = 2 * (‖y‖ ^ 2 / (8 * t)) := by
          have h8t : (8:ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht0
          have h4t : (4:ℝ) * t ≠ 0 := mul_ne_zero (by norm_num) ht0
          field_simp
          ring
        rw [hsplit]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        rw [hrel]
        linear_combination hfrac
      have hrw : ‖y‖ ^ n * ‖y‖ ^ (2 * q) = ‖y‖ ^ (2 * (q + (n:ℝ)/2)) := by
        rw [← Real.rpow_natCast _ n, ← Real.rpow_add hrpos]
        congr 1
        ring
      have hmom1 := moment_core ‖y‖ (2 * t) q hr0 h2tpos hqpos
      rw [h16, h8] at hmom1
      have hterm1 : ‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (4 * t))
          ≤ Real.exp (-δ ^ 2 / (16 * t))
            * ((16 * t) ^ q * q ^ q * Real.exp (-‖y‖ ^ 2 / (16 * t))) := by
        have hstep_a := mul_le_mul_of_nonneg_left hexp_tail (Real.rpow_nonneg hr0 (2 * q))
        have hstep_b := mul_le_mul_of_nonneg_left hmom1
          (Real.exp_pos (-δ ^ 2 / (16 * t))).le
        have heq : ‖y‖ ^ (2 * q) * (Real.exp (-δ ^ 2 / (16 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t)))
            = Real.exp (-δ ^ 2 / (16 * t)) * (‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by
              ring
        rw [heq] at hstep_a
        exact le_trans hstep_a hstep_b
      have hmom2 := moment_core ‖y‖ (2 * t) (q + (n:ℝ)/2) hr0 h2tpos hqnpos
      rw [h16, h8] at hmom2
      have hterm2 : (‖y‖ ^ n * ‖y‖ ^ (2 * q)) * Real.exp (-‖y‖ ^ 2 / (4 * t))
          ≤ Real.exp (-δ ^ 2 / (16 * t))
            * ((16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)
              * Real.exp (-‖y‖ ^ 2 / (16 * t))) := by
        rw [hrw]
        have hstep_a := mul_le_mul_of_nonneg_left hexp_tail
          (Real.rpow_nonneg hr0 (2 * (q + (n:ℝ)/2)))
        have hstep_b := mul_le_mul_of_nonneg_left hmom2
          (Real.exp_pos (-δ ^ 2 / (16 * t))).le
        have heq : ‖y‖ ^ (2 * (q + (n:ℝ)/2))
              * (Real.exp (-δ ^ 2 / (16 * t)) * Real.exp (-‖y‖ ^ 2 / (8 * t)))
            = Real.exp (-δ ^ 2 / (16 * t))
              * (‖y‖ ^ (2 * (q + (n:ℝ)/2)) * Real.exp (-‖y‖ ^ 2 / (8 * t))) := by ring
        rw [heq] at hstep_a
        exact le_trans hstep_a hstep_b
      have hadd : R ^ n * (‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
            + (‖y‖ ^ n * ‖y‖ ^ (2 * q)) * Real.exp (-‖y‖ ^ 2 / (4 * t))
          ≤ R ^ n * (Real.exp (-δ ^ 2 / (16 * t))
              * ((16 * t) ^ q * q ^ q * Real.exp (-‖y‖ ^ 2 / (16 * t))))
            + Real.exp (-δ ^ 2 / (16 * t))
              * ((16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)
                * Real.exp (-‖y‖ ^ 2 / (16 * t))) :=
        add_le_add (mul_le_mul_of_nonneg_left hterm1 (pow_nonneg hR _)) hterm2
      have hmulS : C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (R ^ n * (‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
              + (‖y‖ ^ n * ‖y‖ ^ (2 * q)) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          ≤ C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (R ^ n * (Real.exp (-δ ^ 2 / (16 * t))
                * ((16 * t) ^ q * q ^ q * Real.exp (-‖y‖ ^ 2 / (16 * t))))
              + Real.exp (-δ ^ 2 / (16 * t))
                * ((16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)
                  * Real.exp (-‖y‖ ^ 2 / (16 * t)))) :=
        mul_le_mul_of_nonneg_left hadd (mul_nonneg hC0 (Real.rpow_nonneg h4pt0 _))
      rw [← ENNReal.ofReal_mul (heatKernel_nonneg n t ht y)]
      apply ENNReal.ofReal_le_ofReal
      rw [heatKernel_euclideanSpace]
      have eL : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / (4 * t))
            * (C0 * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q)))
          = C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (R ^ n * (‖y‖ ^ (2 * q) * Real.exp (-‖y‖ ^ 2 / (4 * t)))
              + (‖y‖ ^ n * ‖y‖ ^ (2 * q)) * Real.exp (-‖y‖ ^ 2 / (4 * t))) := by ring
      have eR : (C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
            * (R ^ n * ((16 * t) ^ q * q ^ q)
              + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)))
            * Real.exp (-‖y‖ ^ 2 / (16 * t))
          = C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * (R ^ n * (Real.exp (-δ ^ 2 / (16 * t))
                * ((16 * t) ^ q * q ^ q * Real.exp (-‖y‖ ^ 2 / (16 * t))))
              + Real.exp (-δ ^ 2 / (16 * t))
                * ((16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)
                  * Real.exp (-‖y‖ ^ 2 / (16 * t)))) := by ring
      rw [eL, eR]
      exact hmulS
    have hBmeas : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ) :=
      measurableSet_closedBall
    have hstep2 : (∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ,
          ENNReal.ofReal (Φ n t y)
            * ENNReal.ofReal (C0 * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q))) ∂volume)
        ≤ ∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ,
          ENNReal.ofReal ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
            * (R ^ n * ((16 * t) ^ q * q ^ q)
              + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)))
            * Real.exp (-‖y‖ ^ 2 / (16 * t))) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hBmeas.compl] with y hy
      have hrδ : δ ≤ ‖y‖ := by
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hy
        exact le_of_lt (lt_of_not_ge hy)
      exact hpt y hrδ
    have hstep1 : (∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ,
          ENNReal.ofReal ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
            * (R ^ n * ((16 * t) ^ q * q ^ q)
              + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)))
            * Real.exp (-‖y‖ ^ 2 / (16 * t))) ∂volume)
        ≤ ∫⁻ y, ENNReal.ofReal ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 *
          t))
            * (R ^ n * ((16 * t) ^ q * q ^ q)
              + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)))
            * Real.exp (-‖y‖ ^ 2 / (16 * t))) ∂volume :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => -‖y‖ ^ 2 / (16 * t)) := by
      simp only [div_eq_mul_inv]
      continuity
    have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / (16 * t)))) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hcont)).measurable
    have hstep3 : (∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
          ((C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
            * (R ^ n * ((16 * t) ^ q * q ^ q)
              + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)))
            * Real.exp (-‖y‖ ^ 2 / (16 * t))) ∂volume)
        = ENNReal.ofReal (C0 * ((R ^ n * ((16:ℝ)^q * q^q * 2^n) * t ^ q
          + (16:ℝ)^(q + (n:ℝ)/2) * (q + (n:ℝ)/2)^(q + (n:ℝ)/2) * 2^n * t ^ (q + (n:ℝ)/2))
          * Real.exp (-δ ^ 2 / (16 * t)))) := by
      have hpt2 : ∀ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / (16 * t)))
            = ENNReal.ofReal (Real.exp (-(1 / (16 * t)) * ‖y‖ ^ 2)) := by
        intro y
        congr 1
        congr 1
        ring
      have hI : (∫⁻ y : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / (16 * t))) ∂volume)
          = ENNReal.ofReal ((16 * Real.pi * t) ^ ((n : ℝ) / 2)) := by
        have hG := gauss_lintegral n (1 / (16 * t)) (by positivity)
        have hpi : Real.pi / (1 / (16 * t)) = 16 * Real.pi * t := by
          rw [div_div_eq_mul_div, div_one]
          ring
        rw [hpi] at hG
        simp only [hpt2]
        exact hG
      simp only [ENNReal.ofReal_mul hK0, lintegral_const_mul _ hmeas, hI]
      rw [← ENNReal.ofReal_mul hK0]
      congr 1
      have e1 : ((16:ℝ) * t) ^ q = 16 ^ q * t ^ q := Real.mul_rpow (by norm_num) ht.le
      have e1b : ((16:ℝ) * t) ^ (q + (n:ℝ)/2) = 16 ^ (q + (n:ℝ)/2) * t ^ (q + (n:ℝ)/2) :=
        Real.mul_rpow (by norm_num) ht.le
      have h4pt : 4 * Real.pi * t ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht0
      have h16pt0 : (0:ℝ) ≤ 16 * Real.pi * t := by positivity
      have hdiv : (16 * Real.pi * t) / (4 * Real.pi * t) = 4 := by
        rw [div_eq_iff h4pt]; ring
      have e2 : (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (16 * Real.pi * t) ^ ((n : ℝ) / 2)
          = 2 ^ n := by
        rw [neg_div, Real.rpow_neg h4pt0, mul_comm,
          ← div_eq_mul_inv, ← Real.div_rpow h16pt0 h4pt0, hdiv,
          show (4:ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast _ 2,
          ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num), ← Real.rpow_natCast _ n]
        congr 1
        ring
      calc C0 * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-δ ^ 2 / (16 * t))
              * (R ^ n * ((16 * t) ^ q * q ^ q)
                + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2))
              * (16 * Real.pi * t) ^ ((n : ℝ) / 2)
          = C0 * Real.exp (-δ ^ 2 / (16 * t)) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
              * (16 * Real.pi * t) ^ ((n : ℝ) / 2))
            * (R ^ n * ((16 * t) ^ q * q ^ q)
              + (16 * t) ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)) := by ring
        _ = C0 * Real.exp (-δ ^ 2 / (16 * t)) * 2 ^ n
            * (R ^ n * (16 ^ q * t ^ q * q ^ q)
              + 16 ^ (q + (n:ℝ)/2) * t ^ (q + (n:ℝ)/2) * (q + (n:ℝ)/2) ^ (q + (n:ℝ)/2)) := by
          rw [e2, e1, e1b]
        _ = C0 * ((R ^ n * ((16:ℝ)^q * q^q * 2^n) * t ^ q
            + (16:ℝ)^(q + (n:ℝ)/2) * (q + (n:ℝ)/2)^(q + (n:ℝ)/2) * 2^n * t ^ (q + (n:ℝ)/2))
            * Real.exp (-δ ^ 2 / (16 * t))) := by ring
    exact (le_trans hstep2 (le_trans hstep1 hstep3.le))

private theorem y_integral_estimate (n : ℕ) (hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p)
    (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (_hφ : ContDiff ℝ 2 φ) (_hφ_supp : HasCompactSupport φ)
    (_hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M)
    (hModMonoThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∀ {r₁ r₂ : ℝ}, 0 ≤ r₁ → r₁ ≤ r₂ →
      secondPartialModulus n φ i j r₁ ≤ secondPartialModulus n φ i j r₂)
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ (C R : ℝ), 0 ≤ C → 0 ≤ R →
      (∀ y : EuclideanSpace ℝ (Fin n),
        (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
        ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
          p.toReal) * C)
          * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal))))
            →
      ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ δ t : ℝ, 0 < δ → 0 < t → t ≤ 1 →
        (∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
          ∂volume) ∂volume).toReal
        ≤ t ^ p.toReal * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 *
          Real.exp (-δ ^ 2 / (16 * t))) := by
  have hSmallBall := smallBall_integral_bound
  have hLargeCompl := largeCompl_integral_bound
  set q : ℝ := p.toReal with hqdef
  have hp_ne : p ≠ ⊤ := ne_of_lt hp
  have hq1 : 1 ≤ q := by
    have h10 : (1 : ENNReal).toReal = 1 := by
      rw [← ENNReal.ofReal_one,
        ENNReal.toReal_ofReal ((by norm_num : (0 : ℝ) ≤ 1))]
    have h := ENNReal.toReal_mono hp_ne hp1
    rw [h10] at h
    exact h
  choose M hM0 hMle using
    fun i j => hBndThm n i j (hDijThm i j).1 (hDijThm i j).2.1
  obtain ⟨Cmom, hCmom0, hSmall⟩ := hSmallBall n q hq1
  obtain ⟨C1, C2, hC10, hC20, hLarge⟩ := hLargeCompl n q hq1
  intro C R hC hR hAnt
  have hPREF0 : 0 ≤ ((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
      * (((n : ℝ) ^ 2) ^ q) * C := by
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) hC
    · exact Real.rpow_nonneg (by norm_num) _
    · norm_num
    · exact Real.rpow_nonneg (by positivity) _
  have hMtot0 : 0 ≤ ∑ i, ∑ j, 2 * M i j := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by norm_num) (hM0 i j)
  refine ⟨(((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C) * Cmom,
    (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
      * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n * (R ^ n * C1 + C2),
    mul_nonneg hPREF0 hCmom0, ?_, fun δ t hδ ht ht1 => ?_⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg hPREF0 hMtot0) (by positivity))
      (add_nonneg (mul_nonneg (by positivity) hC10) hC20)
  · -- Main estimate for fixed `δ`, `t`: split the `y`-integral at `δ`.
    set B : Set (EuclideanSpace ℝ (Fin n)) :=
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ with hBdef
    have hBmeas : MeasurableSet B := measurableSet_closedBall
    have mem_le : ∀ y : EuclideanSpace ℝ (Fin n), y ∈ B → ‖y‖ ≤ δ := by
      intro y hy
      have h := Metric.mem_closedBall.mp hy
      rwa [dist_zero_right] at h
    have hSδ0 : 0 ≤ ∑ i, ∑ j, secondPartialModulus n φ i j δ :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => (hDijThm i j).2.2.2.1 δ
    have hC0s0 : 0 ≤ (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n :=
      mul_nonneg (mul_nonneg hPREF0 hSδ0) (by positivity)
    have hC0l0 : 0 ≤ (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n :=
      mul_nonneg (mul_nonneg hPREF0 hMtot0) (by positivity)
    -- SMALL part: pointwise bound on `‖y‖ ≤ δ` via modulus monotonicity.
    have hGy_small : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ δ →
        ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume)
          ≤ ENNReal.ofReal (Φ n t y) * ENNReal.ofReal
            (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
              * ‖y‖ ^ (2 * q)) := by
      intro y hyδ
      gcongr
      have hmono : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
          ≤ ∑ i, ∑ j, secondPartialModulus n φ i j δ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hModMonoThm n i j (hDijThm i j).1 (hDijThm i j).2.1 (norm_nonneg _) hyδ
      have hpow : (R + ‖y‖) ^ n ≤ (R + δ) ^ n :=
        pow_le_pow_left₀ (by positivity) (add_le_add_right hyδ R) n
      have hN0 : 0 ≤ ‖y‖ ^ (2 * q) := Real.rpow_nonneg (norm_nonneg _) _
      have hSP : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n
          ≤ (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n :=
        mul_le_mul hmono hpow (by positivity) hSδ0
      have hfull : (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
              * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * q))
          ≤ (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
            * ‖y‖ ^ (2 * q)) := by
        have hstep : (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
                * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * q))
            ≤ (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * ((∑ i, ∑ j, secondPartialModulus n φ i j δ)
                * (R + δ) ^ n * ‖y‖ ^ (2 * q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSP hN0) hPREF0
        have heq : (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * ((∑ i, ∑ j, secondPartialModulus n φ i j δ)
                * (R + δ) ^ n * ‖y‖ ^ (2 * q))
            = (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
              * ‖y‖ ^ (2 * q)) := by
          ring
        rw [heq] at hstep
        exact hstep
      exact le_trans (hAnt y) (ENNReal.ofReal_le_ofReal hfull)
    have hS_le : ∫⁻ y in B,
          ENNReal.ofReal (Φ n t y)
            * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume
        ≤ ENNReal.ofReal (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
          * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
          * (Cmom * t ^ q)) := by
      have hmono : ∫⁻ y in B,
            ENNReal.ofReal (Φ n t y)
              * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume
          ≤ ∫⁻ y in B, ENNReal.ofReal (Φ n t y) * ENNReal.ofReal
            (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
              * ‖y‖ ^ (2 * q)) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hBmeas] with y hy
        exact hGy_small y (mem_le y hy)
      have hH := hSmall δ t hδ ht
        ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n) hC0s0
      exact le_trans hmono hH
    -- LARGE part: pointwise bound on `‖y‖ > δ` via the global modulus bound.
    have hGy_large : ∀ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume)
          ≤ ENNReal.ofReal (Φ n t y) * ENNReal.ofReal
            (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
              * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q))) := by
      intro y
      gcongr
      have hS : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
          ≤ ∑ i, ∑ j, 2 * M i j := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact modulus_le_two_mul_bound n i j (M i j) (hM0 i j) (hMle i j) ‖y‖
          (norm_nonneg _)
      have hV : (R + ‖y‖) ^ n ≤ (2 : ℝ) ^ n * (R ^ n + ‖y‖ ^ n) :=
        add_pow_le_two_pow_mul R ‖y‖ hR (norm_nonneg _) n
      have hN0 : 0 ≤ ‖y‖ ^ (2 * q) := Real.rpow_nonneg (norm_nonneg _) _
      have hSP : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n
          ≤ (∑ i, ∑ j, 2 * M i j) * ((2 : ℝ) ^ n * (R ^ n + ‖y‖ ^ n)) :=
        mul_le_mul hS hV (by positivity) hMtot0
      have hfull : (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
              * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * q))
          ≤ (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n
            * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q)) := by
        have hstep : (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
                * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * q))
            ≤ (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * ((∑ i, ∑ j, 2 * M i j) * ((2 : ℝ) ^ n * (R ^ n + ‖y‖ ^ n))
                * ‖y‖ ^ (2 * q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSP hN0) hPREF0
        have heq : (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * ((∑ i, ∑ j, 2 * M i j) * ((2 : ℝ) ^ n * (R ^ n + ‖y‖ ^ n))
                * ‖y‖ ^ (2 * q))
            = (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n
              * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q)) := by
          ring
        rw [heq] at hstep
        exact hstep
      exact le_trans (hAnt y) (ENNReal.ofReal_le_ofReal hfull)
    have hL_le : ∫⁻ y in Bᶜ,
          ENNReal.ofReal (Φ n t y)
            * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume
        ≤ ENNReal.ofReal (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
          * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
          * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
            * Real.exp (-δ ^ 2 / (16 * t)))) := by
      have hmono : ∫⁻ y in Bᶜ,
            ENNReal.ofReal (Φ n t y)
              * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume
          ≤ ∫⁻ y in Bᶜ, ENNReal.ofReal (Φ n t y) * ENNReal.ofReal
            (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
              * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
              * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q))) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hBmeas.compl] with y hy
        exact hGy_large y
      have hH := hLarge R δ t hR hδ ht
        ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n) hC0l0
      exact le_trans hmono hH
    -- Combine the two parts through `ENNReal.toReal` monotonicity.
    have hsplit : (∫⁻ y, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume)
        = (∫⁻ y in B, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume)
        + (∫⁻ y in Bᶜ, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume) :=
      (lintegral_add_compl _ hBmeas).symm
    have hoRsmall : ENNReal.ofReal (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
        * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
        * (Cmom * t ^ q)) ≠ ⊤ := by
      simp
    have hoRlarge : ENNReal.ofReal (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
        * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
        * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t)))) ≠ ⊤ := by
      simp
    have hsmall_ne : (∫⁻ y in B, ENNReal.ofReal (Φ n t y)
        * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume) ≠ ⊤ :=
      ne_top_of_le_ne_top hoRsmall hS_le
    have hlarge_ne : (∫⁻ y in Bᶜ, ENNReal.ofReal (Φ n t y)
        * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume) ≠ ⊤ :=
      ne_top_of_le_ne_top hoRlarge hL_le
    have hsplit_toReal : (∫⁻ y, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal
        = (∫⁻ y in B, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal
        + (∫⁻ y in Bᶜ, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal := by
      rw [hsplit, ENNReal.toReal_add hsmall_ne hlarge_ne]
    have hsmallR0 : 0 ≤ ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
        * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
        * (Cmom * t ^ q) :=
      mul_nonneg hC0s0 (mul_nonneg hCmom0 (Real.rpow_nonneg (le_of_lt ht) _))
    have hlargeR0 : 0 ≤ ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
        * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
        * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t))) :=
      mul_nonneg hC0l0 (mul_nonneg
        (add_nonneg (mul_nonneg (mul_nonneg (by positivity) hC10)
          (Real.rpow_nonneg (le_of_lt ht) _))
          (mul_nonneg hC20 (Real.rpow_nonneg (le_of_lt ht) _)))
        (Real.exp_pos _).le)
    have hStoReal : (∫⁻ y in B, ENNReal.ofReal (Φ n t y)
        * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal
        ≤ ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
        * (Cmom * t ^ q) := by
      have h := ENNReal.toReal_mono hoRsmall hS_le
      rw [ENNReal.toReal_ofReal hsmallR0] at h
      exact h
    have hLtoReal : (∫⁻ y in Bᶜ, ENNReal.ofReal (Φ n t y)
        * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal
        ≤ ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
        * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t))) := by
      have h := ENNReal.toReal_mono hoRlarge hL_le
      rw [ENNReal.toReal_ofReal hlargeR0] at h
      exact h
    have hsmall_eq : ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
        * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
        * (Cmom * t ^ q)
        = t ^ q * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n
          * ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * Cmom)) := by
      ring
    -- NB: with `t ≤ 1`, the `C2 * t ^ (q + n / 2)` term is absorbed: `t ^ (n / 2) ≤ 1`
    -- gives `C2 * t ^ (q + n / 2) = C2 * t ^ q * t ^ (n / 2) ≤ C2 * t ^ q`.
    have habsorb : ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
        * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t)))
        ≤ t ^ q * (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n * (R ^ n * C1 + C2))
          * Real.exp (-δ ^ 2 / (16 * t))) := by
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have hn2 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      have hsplit : t ^ (q + (n : ℝ) / 2) = t ^ q * t ^ ((n : ℝ) / 2) :=
        Real.rpow_add ht q ((n : ℝ) / 2)
      have htn1 : t ^ ((n : ℝ) / 2) ≤ (1 : ℝ) :=
        Real.rpow_le_one ht0 ht1 hn2
      have htq0 : (0 : ℝ) ≤ t ^ q := Real.rpow_nonneg ht0 q
      have hC2 : C2 * t ^ (q + (n : ℝ) / 2) ≤ C2 * t ^ q := by
        rw [hsplit]
        have h : C2 * (t ^ q * t ^ ((n : ℝ) / 2)) ≤ C2 * (t ^ q * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htn1 htq0) hC20
        rwa [mul_one] at h
      have hsum : R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2)
          ≤ (R ^ n * C1 + C2) * t ^ q := by
        rw [add_mul]
        linarith [hC2]
      have hE0 : (0 : ℝ) ≤ Real.exp (-δ ^ 2 / (16 * t)) := (Real.exp_pos _).le
      have hstep : (R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
            * Real.exp (-δ ^ 2 / (16 * t))
          ≤ ((R ^ n * C1 + C2) * t ^ q) * Real.exp (-δ ^ 2 / (16 * t)) :=
        mul_le_mul_of_nonneg_right hsum hE0
      have hfull := mul_le_mul_of_nonneg_left hstep hC0l0
      have heq : ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
            * (((R ^ n * C1 + C2) * t ^ q) * Real.exp (-δ ^ 2 / (16 * t)))
          = t ^ q * (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2)
            * (((n : ℝ) ^ 2) ^ q) * C)
            * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n * (R ^ n * C1 + C2))
            * Real.exp (-δ ^ 2 / (16 * t))) := by
        ring
      rw [heq] at hfull
      exact hfull
    have h1 : (∫⁻ y in B, ENNReal.ofReal (Φ n t y)
        * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal
        + (∫⁻ y in Bᶜ, ENNReal.ofReal (Φ n t y)
        * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ q ∂volume) ∂volume).toReal
        ≤ ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
        * (Cmom * t ^ q)
        + ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
        * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t))) :=
      add_le_add hStoReal hLtoReal
    have h2 : ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n)
        * (Cmom * t ^ q)
        + ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
        * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n)
        * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
          * Real.exp (-δ ^ 2 / (16 * t)))
        ≤ t ^ q * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n
          * ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * Cmom))
        + t ^ q * (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n * (R ^ n * C1 + C2))
          * Real.exp (-δ ^ 2 / (16 * t))) :=
      add_le_add hsmall_eq.le habsorb
    have h3 : t ^ q * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n
          * ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * Cmom))
        + t ^ q * (((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n * (R ^ n * C1 + C2))
          * Real.exp (-δ ^ 2 / (16 * t)))
        = t ^ q * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n
          * ((((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
            * Cmom)
          + (((1 : ℝ) / 2) ^ (q - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ q) * C)
          * (∑ i, ∑ j, 2 * M i j) * (2 : ℝ) ^ n * (R ^ n * C1 + C2)
          * Real.exp (-δ ^ 2 / (16 * t))) := by
      ring
    rw [hsplit_toReal, ← h3]
    linarith [h1, h2]

end C3

section C4

open MeasureTheory
open scoped Topology


private theorem tendsto_generator_of_diff_le (n : ℕ) (hn : 0 < n)
    {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    (hJensenThm : ∀ {n : ℕ} {q : ℝ} (_hq1 : 1 ≤ q)
      {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
      {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) →
      Integrable (Function.uncurry F) (μ.prod volume) →
      ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ q) ∂volume
        ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ q) ∂volume ∂μ)
    (hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hRemThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x
        = ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          * ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)))
    (hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      (∀ (x z : EuclideanSpace ℝ (Fin n)),
        |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖z‖) →
      ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
      |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
        ≤ secondPartialModulus n φ i j ‖y‖)
    (hSumThm : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin n)),
      ∑ i : Fin n, ∑ j : Fin n, |y i * y j| ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2)
    (hEqThm : ∀ (n : ℕ) {p : ENNReal} (_hp0 : p ≠ 0) (_hpTop : p ≠ ⊤)
      {f : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable f volume → 0 < p.toReal →
      (eLpNorm f p volume).toReal ^ p.toReal
        = (∫⁻ x, ENNReal.ofReal ‖f x‖ ^ p.toReal ∂volume).toReal)
    (hProbThm : ∀ (n : ℕ) {t : ℝ} (_ht : 0 < t),
      (∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y = 1) →
      IsProbabilityMeasure
        (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)))
    (hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M)
    (hModMonoThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∀ {r₁ r₂ : ℝ}, 0 ≤ r₁ → r₁ ≤ r₂ →
      secondPartialModulus n φ i j r₁ ≤ secondPartialModulus n φ i j r₂)
    (hAthm : ∀ (n : ℕ) (_hn : 0 < n) {p : ENNReal} (_hp1 : 1 ≤ p) (_hp : p < ⊤)
      {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
      (_hφ_supp : HasCompactSupport φ)
      (_hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
      (_hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        (∀ (x z : EuclideanSpace ℝ (Fin n)),
          |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
            ≤ secondPartialModulus n φ i j ‖z‖) →
        ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
        |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖y‖),
      ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ (i j : Fin n) (y : EuclideanSpace ℝ (Fin n))
        (s : ℝ), 0 ≤ s → s ≤ 1 →
        ∫⁻ x, ENNReal.ofReal
          ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
          ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))
    (hC1thm : ∀ (n : ℕ) (_hn : 0 < n) {p : ENNReal} (_hp1 : 1 ≤ p) (_hp : p < ⊤)
      {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
      (_hφ_supp : HasCompactSupport φ)
      (_hJensenThm : ∀ {n : ℕ} {q : ℝ} (_hq1 : 1 ≤ q)
        {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
        {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ},
        AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) →
        Integrable (Function.uncurry F) (μ.prod volume) →
        ∫⁻ y, ENNReal.ofReal (‖∫ x, F x y ∂μ‖ ^ q) ∂volume
          ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖F x y‖ ^ q) ∂volume ∂μ)
      (_hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
        (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
        ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
        ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
          = if i = j then 2 * t else 0))
      (_hProbThm : ∀ (n : ℕ) {t : ℝ} (_ht : 0 < t),
        (∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y = 1) →
        IsProbabilityMeasure
          (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t
            y)))
      (_hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
      (_hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        (∀ (x z : EuclideanSpace ℝ (Fin n)),
          |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
            ≤ secondPartialModulus n φ i j ‖z‖) →
        ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
        |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖y‖)
      (_hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M),
      ∀ (t : ℝ), 0 < t →
        (∀ x : EuclideanSpace ℝ (Fin n),
          (∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
            (Φ n t y)))
          = ∫ y, Φ n t y * Dfn n φ x y)
        ∧ AEStronglyMeasurable
          (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (Φ n t y)))
          volume
        ∧ (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ
          (Fin n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume)
          ≤ ∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^
            p.toReal ∂volume) ∂volume)
    (hC2bypass : ∀ (n : ℕ) (_hn : 0 < n) {p : ENNReal} (_hp1 : 1 ≤ p)
    (_hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (_hφ : ContDiff ℝ 2 φ) (_hφ_supp : HasCompactSupport φ)
    (_hAthm : ∀ (n : ℕ) (_hn : 0 < n) {p : ENNReal} (_hp1 : 1 ≤ p) (_hp : p < ⊤)
      {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
      (_hφ_supp : HasCompactSupport φ)
      (_hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
      (_hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        (∀ (x z : EuclideanSpace ℝ (Fin n)),
          |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
            ≤ secondPartialModulus n φ i j ‖z‖) →
        ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
        |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖y‖),
      ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ (i j : Fin n) (y : EuclideanSpace ℝ (Fin n))
        (s : ℝ), 0 ≤ s → s ≤ 1 →
        ∫⁻ x, ENNReal.ofReal
          ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
          ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))
    (_hSumThm : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin n)),
      ∑ i : Fin n, ∑ j : Fin n, |y i * y j| ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2)
    (_hDijThm : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)),
      ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ y : EuclideanSpace ℝ (Fin n),
      (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
      ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
        * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal))))
    (hC3thm : ∀ (n : ℕ) (_hn : 0 < n) {p : ENNReal} (_hp1 : 1 ≤ p) (_hp : p < ⊤)
      {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
      (_hφ_supp : HasCompactSupport φ)
      (_hMomThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
        (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
        ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
        ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
          = if i = j then 2 * t else 0))
      (_hBndThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M)
      (_hModMonoThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
        Continuous (secondPartialFn n φ i j) →
        HasCompactSupport (secondPartialFn n φ i j) →
        ∀ {r₁ r₂ : ℝ}, 0 ≤ r₁ → r₁ ≤ r₂ →
        secondPartialModulus n φ i j r₁ ≤ secondPartialModulus n φ i j r₂)
      (_hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)),
      ∀ (C R : ℝ), 0 ≤ C → 0 ≤ R →
        (∀ y : EuclideanSpace ℝ (Fin n),
          (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
          ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
            p.toReal) * C)
            * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 *
              p.toReal)))) →
        ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ δ t : ℝ, 0 < δ → 0 < t → t ≤ 1 →
          (∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
            ∂volume) ∂volume).toReal
          ≤ t ^ p.toReal * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 *
            Real.exp (-δ ^ 2 / (16 * t))))
    (hSmallBall : ∀ (n : ℕ) (q : ℝ), 1 ≤ q →
      ∃ Cmom : ℝ, 0 ≤ Cmom ∧ ∀ (δ t : ℝ), 0 < δ → 0 < t → ∀ (C0 : ℝ), 0 ≤ C0 →
        ∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ,
          ENNReal.ofReal (Φ n t y) * ENNReal.ofReal (C0 * ‖y‖ ^ (2 * q)) ∂volume
          ≤ ENNReal.ofReal (C0 * (Cmom * t ^ q)))
    (hLargeCompl : ∀ (n : ℕ) (q : ℝ), 1 ≤ q →
      ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ (R δ t : ℝ), 0 ≤ R → 0 < δ → 0 < t →
        ∀ (C0 : ℝ), 0 ≤ C0 →
        ∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ,
          ENNReal.ofReal (Φ n t y)
            * ENNReal.ofReal (C0 * (R ^ n * ‖y‖ ^ (2 * q) + ‖y‖ ^ n * ‖y‖ ^ (2 * q))) ∂volume
          ≤ ENNReal.ofReal (C0 * ((R ^ n * C1 * t ^ q + C2 * t ^ (q + (n : ℝ) / 2))
            * Real.exp (-δ ^ 2 / (16 * t)))))
    : Filter.Tendsto
      (fun t : ℝ =>
        (eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- `q := p.toReal` is positive.
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp1)
  have hpTop' : p ≠ ⊤ := ne_of_lt hp
  have hq1 : 1 ≤ p.toReal := by
    have h10 : (1 : ENNReal).toReal = 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.toReal_ofReal zero_le_one
    rw [← h10]
    exact ENNReal.toReal_mono (ne_of_lt hp) hp1
  have hqpos : 0 < p.toReal := lt_of_lt_of_le (by norm_num) hq1
  have hqne : p.toReal ≠ 0 := ne_of_gt hqpos
  have hqq : p.toReal * (1 / p.toReal) = 1 := mul_one_div_cancel hqne
  -- Constants from the per-`(i,j)` bound.
  obtain ⟨C, R, hC, hR, hH⟩ := hC2bypass n hn hp1 hp hφ hφ_supp hAthm hSumThm hDijThm
  -- Step 1: congruence of the goal to the `Dfn` form for `t > 0`.
  have hcongr : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (eLpNorm (fun x => heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x) p
        volume).toReal / t
      = (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n)
        => ENNReal.ofReal (Φ n t y))) p volume).toReal / t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [Set.mem_Ioi] at ht
    congr 1
    congr 1
    apply MeasureTheory.eLpNorm_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have h1 : heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x
        = ∫ y, Φ n t y * Dfn n φ x y := by
      simp only [heatKernel_euclideanSpace]
      exact hRemThm n hφ hφ_supp ht x
    have h2 : (∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Φ n t y)))
        = ∫ y, Φ n t y * Dfn n φ x y :=
      (hC1thm n hn hp1 hp hφ hφ_supp hJensenThm hMomThm hProbThm hDijThm hSubThm hBndThm t ht).1 x
    simp only []
    rw [h1, ← h2]
  -- Reduce the goal to the `Dfn` form.
  refine Filter.Tendsto.congr' (hcongr.mono fun t h => h.symm) ?_
  -- Step 2: `eLpNorm` to `∫⁻` via `hEqThm`.
  have hE : ∀ t : ℝ, 0 < t →
      (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Φ n t y))) p volume).toReal ^ p.toReal
      = (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
        n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume).toReal := by
    intro t ht
    have hmeas : AEStronglyMeasurable
        (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (Φ n t y)))
        volume :=
      (hC1thm n hn hp1 hp hφ hφ_supp hJensenThm hMomThm hProbThm hDijThm hSubThm hBndThm t ht).2.1
    exact hEqThm n hp0 hpTop' hmeas hqpos
  -- Step 3: Jensen (`hC1thm`) + density conversion.
  have hJ : ∀ t : ℝ, 0 < t →
      (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
        n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume)
      ≤ ∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
        ∂volume) ∂volume :=
    fun t ht => (hC1thm n hn hp1 hp hφ hφ_supp hJensenThm hMomThm hProbThm hDijThm hSubThm hBndThm
      t ht).2.2
  -- Steps 2-5 combined: chain hE, hJ, hC3thm.
  obtain ⟨J1, J2, hJ1, hJ2, hY⟩ := hC3thm n hn hp1 hp hφ hφ_supp hMomThm hBndThm hModMonoThm
    hDijThm C R hC hR hH
  obtain ⟨K1, K2, hK1, hK2, hMain⟩ : ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ δ t : ℝ, 0 < δ → 0 < t → t ≤
    1 →
      (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (Φ n t y))) p volume).toReal ^ p.toReal
      ≤ t ^ p.toReal * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 *
        Real.exp (-δ ^ 2 / (16 * t))) := by
    refine ⟨J1, J2, hJ1, hJ2, fun δ t hδ ht ht1 => ?_⟩
    -- Finiteness of the `y`-integral, needed for `ENNReal.toReal_mono`,
    -- via the small-ball / large-complement moment bounds.
    have hbfin : (∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^
      p.toReal ∂volume) ∂volume) ≠ ⊤ := by
      have hPREFnn : 0 ≤ ((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C := by
        apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · exact Real.rpow_nonneg (by norm_num) _
            · norm_num
          · exact Real.rpow_nonneg (sq_nonneg _) _
        · exact hC
      obtain ⟨Cmom, hCmomnn, hSB⟩ := hSmallBall n p.toReal hq1
      obtain ⟨C1, C2, hC1nn, hC2nn, hLC⟩ := hLargeCompl n p.toReal hq1
      have hex : ∀ i j : Fin n, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M :=
        fun i j => hBndThm n i j (hDijThm i j).1 (hDijThm i j).2.1
      choose M hMnn hMbnd using hex
      have hmodBnd : ∀ (i j : Fin n) (r : ℝ), 0 ≤ r →
          secondPartialModulus n φ i j r ≤ 2 * M i j := by
        intro i j r hr
        unfold secondPartialModulus
        apply csSup_le
        · exact ⟨_, 0, 0, by simpa using hr, rfl⟩
        · intro v hv
          simp only [Set.mem_ofPred_eq] at hv
          obtain ⟨x, z, -, rfl⟩ := hv
          have htri : |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ |secondPartialFn n φ i j (x - z)| + |secondPartialFn n φ i j x| := by
            have h := abs_sub_le (secondPartialFn n φ i j (x - z)) 0 (secondPartialFn n φ i j x)
            simpa using h
          have h1 := hMbnd i j (x - z)
          have h2 := hMbnd i j x
          linarith
      have hSy_nn : ∀ y : EuclideanSpace ℝ (Fin n),
          0 ≤ (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) := by
        intro y
        apply Finset.sum_nonneg
        intro i _
        apply Finset.sum_nonneg
        intro j _
        exact (hDijThm i j).2.2.2.1 _
      have hMtotnn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, 2 * M i j := by
        apply Finset.sum_nonneg
        intro i _
        apply Finset.sum_nonneg
        intro j _
        exact mul_nonneg zero_le_two (hMnn i j)
      have hsumBnd : ∀ y : EuclideanSpace ℝ (Fin n),
          (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) ≤ ∑ i, ∑ j, 2 * M i j := by
        intro y
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact hmodBnd i j ‖y‖ (norm_nonneg _)
      have hpow2 : ∀ y : EuclideanSpace ℝ (Fin n),
          (R + ‖y‖) ^ n ≤ 2 ^ n * (R ^ n + ‖y‖ ^ n) := by
        intro y
        have hle : R + ‖y‖ ≤ 2 * max R ‖y‖ := by
          have h1 : R ≤ max R ‖y‖ := le_max_left _ _
          have h2 : ‖y‖ ≤ max R ‖y‖ := le_max_right _ _
          linarith
        have hnn : 0 ≤ R + ‖y‖ := add_nonneg hR (norm_nonneg _)
        calc (R + ‖y‖) ^ n ≤ (2 * max R ‖y‖) ^ n := pow_le_pow_left₀ hnn hle n
          _ = 2 ^ n * (max R ‖y‖) ^ n := mul_pow _ _ _
          _ ≤ 2 ^ n * (R ^ n + ‖y‖ ^ n) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg zero_le_two n)
              rcases le_total R ‖y‖ with h | h
              · rw [max_eq_right h]
                exact le_add_of_nonneg_left (pow_nonneg hR n)
              · rw [max_eq_left h]
                exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) n)
      have hballPt : ∀ y : EuclideanSpace ℝ (Fin n),
          y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ) →
          ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal)))
          ≤ ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n)
            * ‖y‖ ^ (2 * p.toReal) := by
        intro y hy
        have hy1 : ‖y‖ ≤ 1 := by
          have h := Metric.mem_closedBall.mp hy
          rwa [dist_zero_right] at h
        have hmod_le : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖)
            ≤ ∑ i, ∑ j, secondPartialModulus n φ i j 1 := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hModMonoThm n i j (hDijThm i j).1 (hDijThm i j).2.1 (norm_nonneg _) hy1
        have hG_le : (R + ‖y‖) ^ n ≤ (R + 1) ^ n :=
          pow_le_pow_left₀ (add_nonneg hR (norm_nonneg _)) (add_le_add_right hy1 R) n
        have hS1_nn : 0 ≤ (∑ i, ∑ j, secondPartialModulus n φ i j 1) := by
          apply Finset.sum_nonneg
          intro i _
          apply Finset.sum_nonneg
          intro j _
          exact (hDijThm i j).2.2.2.1 _
        have hGy_nn : 0 ≤ (R + ‖y‖) ^ n := pow_nonneg (add_nonneg hR (norm_nonneg _)) n
        have hNy_nn : 0 ≤ ‖y‖ ^ (2 * p.toReal) := Real.rpow_nonneg (norm_nonneg _) _
        have hM_le : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 *
          p.toReal)
            ≤ ((∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * ‖y‖ ^ (2 * p.toReal) :=
              by
          apply mul_le_mul_of_nonneg_right _ hNy_nn
          exact mul_le_mul hmod_le hG_le hGy_nn hS1_nn
        have hP := mul_le_mul_of_nonneg_left hM_le hPREFnn
        have hrw : (((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (((∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * ‖y‖ ^ (2 * p.toReal))
            = ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
              * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * ‖y‖ ^ (2 * p.toReal) :=
                by
          ring
        rwa [hrw] at hP
      have hcomplPt : ∀ y : EuclideanSpace ℝ (Fin n),
          ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal)))
          ≤ ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
            * (R ^ n * ‖y‖ ^ (2 * p.toReal) + ‖y‖ ^ n * ‖y‖ ^ (2 * p.toReal)) := by
        intro y
        have hNy_nn : 0 ≤ ‖y‖ ^ (2 * p.toReal) := Real.rpow_nonneg (norm_nonneg _) _
        have hM_le : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 *
          p.toReal)
            ≤ ((∑ i, ∑ j, 2 * M i j) * 2 ^ n)
              * (R ^ n * ‖y‖ ^ (2 * p.toReal) + ‖y‖ ^ n * ‖y‖ ^ (2 * p.toReal)) := by
          have h1 : (∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 *
            p.toReal)
              ≤ ((∑ i, ∑ j, 2 * M i j) * (2 ^ n * (R ^ n + ‖y‖ ^ n))) * ‖y‖ ^ (2 * p.toReal) := by
            apply mul_le_mul_of_nonneg_right _ hNy_nn
            exact mul_le_mul (hsumBnd y) (hpow2 y)
              (pow_nonneg (add_nonneg hR (norm_nonneg _)) n) hMtotnn
          have h2 : ((∑ i, ∑ j, 2 * M i j) * (2 ^ n * (R ^ n + ‖y‖ ^ n))) * ‖y‖ ^ (2 * p.toReal)
              = ((∑ i, ∑ j, 2 * M i j) * 2 ^ n)
                * (R ^ n * ‖y‖ ^ (2 * p.toReal) + ‖y‖ ^ n * ‖y‖ ^ (2 * p.toReal)) := by
            ring
          rwa [h2] at h1
        have hP := mul_le_mul_of_nonneg_left hM_le hPREFnn
        have hrw : (((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (((∑ i, ∑ j, 2 * M i j) * 2 ^ n)
              * (R ^ n * ‖y‖ ^ (2 * p.toReal) + ‖y‖ ^ n * ‖y‖ ^ (2 * p.toReal)))
            = ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
              * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
              * (R ^ n * ‖y‖ ^ (2 * p.toReal) + ‖y‖ ^ n * ‖y‖ ^ (2 * p.toReal)) := by
          ring
        rwa [hrw] at hP
      have hC0ball_nn : 0 ≤ ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
          * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) := by
        apply mul_nonneg
        · apply mul_nonneg
          · exact hPREFnn
          · apply Finset.sum_nonneg
            intro i _
            apply Finset.sum_nonneg
            intro j _
            exact (hDijThm i j).2.2.2.1 _
        · exact pow_nonneg (add_nonneg hR zero_le_one) n
      have hC0c_nn : 0 ≤ ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
          * (∑ i, ∑ j, 2 * M i j) * 2 ^ n) := by
        apply mul_nonneg
        · apply mul_nonneg
          · exact hPREFnn
          · exact hMtotnn
        · exact pow_nonneg zero_le_two n
      have hball : (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ),
          ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
            ∂volume) ∂volume)
          ≤ ENNReal.ofReal (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
            p.toReal) * C)
            * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n)
            * (Cmom * t ^ p.toReal)) := by
        have hSB1 := hSB (1 : ℝ) t zero_lt_one ht
          ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) hC0ball_nn
        apply le_trans _ hSB1
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem
          (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ)) measurableSet_closedBall]
            with y hy
        have h2 := hballPt y hy
        have h12 := le_trans (hH y) (ENNReal.ofReal_le_ofReal h2)
        exact mul_le_mul_of_nonneg_left h12 zero_le
      have hcompl : (∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ))ᶜ,
          ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
            ∂volume) ∂volume)
          ≤ ENNReal.ofReal (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
            p.toReal) * C)
            * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
            * ((R ^ n * C1 * t ^ p.toReal + C2 * t ^ (p.toReal + (n : ℝ) / 2))
              * Real.exp (-(1 : ℝ) ^ 2 / (16 * t)))) := by
        have hLC1 := hLC R (1 : ℝ) t hR zero_lt_one ht
          ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (∑ i, ∑ j, 2 * M i j) * 2 ^ n) hC0c_nn
        apply le_trans _ hLC1
        apply lintegral_mono_ae
        apply Filter.Eventually.of_forall
        intro y
        have h2 := hcomplPt y
        have h12 := le_trans (hH y) (ENNReal.ofReal_le_ofReal h2)
        exact mul_le_mul_of_nonneg_left h12 zero_le
      have hsplit : (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ),
            ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
              ∂volume) ∂volume)
          + (∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ))ᶜ,
            ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
              ∂volume) ∂volume)
          = (∫⁻ y, ENNReal.ofReal (Φ n t y)
            * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume) ∂volume) :=
        lintegral_add_compl _ measurableSet_closedBall
      have hAnn : 0 ≤ (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
          * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * (Cmom * t ^ p.toReal)) :=
        mul_nonneg hC0ball_nn (mul_nonneg hCmomnn (Real.rpow_nonneg (le_of_lt ht) _))
      have hBnn' : 0 ≤ (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
          * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
          * ((R ^ n * C1 * t ^ p.toReal + C2 * t ^ (p.toReal + (n : ℝ) / 2))
            * Real.exp (-(1 : ℝ) ^ 2 / (16 * t)))) := by
        apply mul_nonneg hC0c_nn
        apply mul_nonneg
        · apply add_nonneg
          · apply mul_nonneg
            · apply mul_nonneg
              · exact pow_nonneg hR n
              · exact hC1nn
            · exact Real.rpow_nonneg (le_of_lt ht) _
          · apply mul_nonneg
            · exact hC2nn
            · exact Real.rpow_nonneg (le_of_lt ht) _
        · exact Real.exp_nonneg _
      have hfin : (∫⁻ y, ENNReal.ofReal (Φ n t y)
          * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume) ∂volume)
          ≤ ENNReal.ofReal ((((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
            p.toReal) * C)
            * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * (Cmom * t ^ p.toReal))
            + (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
            * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
            * ((R ^ n * C1 * t ^ p.toReal + C2 * t ^ (p.toReal + (n : ℝ) / 2))
              * Real.exp (-(1 : ℝ) ^ 2 / (16 * t))))) := by
        calc (∫⁻ y, ENNReal.ofReal (Φ n t y)
              * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume) ∂volume)
            = (∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ),
                ENNReal.ofReal (Φ n t y)
                * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume) ∂volume)
              + (∫⁻ y in (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ))ᶜ,
                ENNReal.ofReal (Φ n t y)
                * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume) ∂volume) := hsplit.symm
          _ ≤ ENNReal.ofReal (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
            p.toReal) * C)
                * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * (Cmom * t ^ p.toReal))
              + ENNReal.ofReal (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
                p.toReal) * C)
                * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
                * ((R ^ n * C1 * t ^ p.toReal + C2 * t ^ (p.toReal + (n : ℝ) / 2))
                  * Real.exp (-(1 : ℝ) ^ 2 / (16 * t)))) := add_le_add hball hcompl
          _ = ENNReal.ofReal ((((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
            p.toReal) * C)
              * (∑ i, ∑ j, secondPartialModulus n φ i j 1) * (R + 1) ^ n) * (Cmom * t ^ p.toReal))
              + (((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^ p.toReal) * C)
              * (∑ i, ∑ j, 2 * M i j) * 2 ^ n)
              * ((R ^ n * C1 * t ^ p.toReal + C2 * t ^ (p.toReal + (n : ℝ) / 2))
                * Real.exp (-(1 : ℝ) ^ 2 / (16 * t))))) := (ENNReal.ofReal_add hAnn hBnn').symm
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    calc (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n)
      => ENNReal.ofReal (Φ n t y))) p volume).toReal ^ p.toReal
        = (∫⁻ x, ENNReal.ofReal ‖(∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ
          (Fin n) => ENNReal.ofReal (Φ n t y)))‖ ^ p.toReal ∂volume).toReal := hE t ht
      _ ≤ (∫⁻ y, ENNReal.ofReal (Φ n t y) * (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal
        ∂volume) ∂volume).toReal := ENNReal.toReal_mono hbfin (hJ t ht)
      _ ≤ t ^ p.toReal * ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * J1 + J2 *
        Real.exp (-δ ^ 2 / (16 * t))) := hY δ t hδ ht ht1
  -- The bracket is nonnegative.
  have hBnn : ∀ δ t : ℝ, 0 < δ → 0 ≤ (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1
    + K2 * Real.exp (-δ ^ 2 / (16 * t)) := by
    intro δ t hδ
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg _ _) hK1
      · apply Finset.sum_nonneg
        intro i _
        apply Finset.sum_nonneg
        intro j _
        exact (hDijThm i j).2.2.2.1 δ
      · apply pow_nonneg
        exact add_nonneg hR (le_of_lt hδ)
    · apply mul_nonneg hK2 (Real.exp_nonneg _)
  -- The modulus part vanishes as `δ → 0+`.
  have hmod0 : Filter.Tendsto (fun δ => (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n *
    K1)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h0 : (∑ i : Fin n, ∑ j : Fin n, (0 : ℝ)) = 0 := by simp
    have hS : Filter.Tendsto (fun δ : ℝ => ∑ i : Fin n, ∑ j : Fin n, secondPartialModulus n φ i j δ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∑ i : Fin n, ∑ j : Fin n, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact (hDijThm i j).2.2.2.2.2
    rw [h0] at hS
    have hGcont : Continuous (fun δ : ℝ => (R + δ) ^ n * K1) := by fun_prop
    have hG : Filter.Tendsto (fun δ : ℝ => (R + δ) ^ n * K1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((R + 0) ^ n * K1)) :=
      hGcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hP : Filter.Tendsto
        (fun δ : ℝ => (∑ i : Fin n, ∑ j : Fin n, secondPartialModulus n φ i j δ) * ((R + δ) ^ n *
          K1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hPm := hS.mul hG
      rw [zero_mul] at hPm
      exact hPm
    have hfn : (fun δ : ℝ => (∑ i : Fin n, ∑ j : Fin n, secondPartialModulus n φ i j δ) * ((R + δ)
      ^ n * K1))
        = (fun δ : ℝ => (∑ i : Fin n, ∑ j : Fin n, secondPartialModulus n φ i j δ) * (R + δ) ^ n *
          K1) := by
      funext δ
      show (∑ i : Fin n, ∑ j : Fin n, secondPartialModulus n φ i j δ) * ((R + δ) ^ n * K1)
        = (∑ i : Fin n, ∑ j : Fin n, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1
      ring
    rwa [hfn] at hP
  -- Step 6: `ε`-`δ` assembly.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεq : (0 : ℝ) < ε ^ p.toReal := by positivity
  have hpos : (0 : ℝ) < ε ^ p.toReal / 2 := by linarith
  obtain ⟨δ, hδpos, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R +
    δ) ^ n * K1 < ε ^ p.toReal / 2 := by
    have hev := hmod0.eventually (eventually_lt_nhds hpos)
    have hev2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 < δ ∧ (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 < ε ^ p.toReal / 2 :=
          by
      filter_upwards [hev, self_mem_nhdsWithin] with δ h1 h2
      exact ⟨Set.mem_Ioi.mp h2, h1⟩
    exact hev2.exists
  have htail0 : Filter.Tendsto (fun t => K2 * Real.exp (-δ ^ 2 / (16 * t)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
    have hc : (-δ ^ 2 / 16 : ℝ) < 0 := by linarith
    have h1div : Filter.Tendsto (fun t : ℝ => 1 / t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    have hmul : Filter.Tendsto (fun t : ℝ => (-δ ^ 2 / 16) * (1 / t))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot :=
      h1div.const_mul_atTop_of_neg hc
    have hexp : Filter.Tendsto (fun t : ℝ => Real.exp ((-δ ^ 2 / 16) * (1 / t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      Real.tendsto_exp_atBot.comp hmul
    have hK : Filter.Tendsto (fun t : ℝ => K2 * Real.exp ((-δ ^ 2 / 16) * (1 / t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (K2 * 0)) :=
      hexp.const_mul K2
    rw [mul_zero] at hK
    have hfn : (fun t : ℝ => K2 * Real.exp ((-δ ^ 2 / 16) * (1 / t)))
        = (fun t : ℝ => K2 * Real.exp (-δ ^ 2 / (16 * t))) := by
      funext t
      show K2 * Real.exp ((-δ ^ 2 / 16) * (1 / t)) = K2 * Real.exp (-δ ^ 2 / (16 * t))
      rw [mul_one_div, div_div]
    rwa [hfn] at hK
  have htail_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), K2 * Real.exp (-δ ^ 2 / (16 * t)) < ε ^
    p.toReal / 2 :=
    htail0.eventually (eventually_lt_nhds hpos)
  filter_upwards [htail_ev, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds
    zero_lt_one)] with t htail htmem ht1
  rw [Set.mem_Ioi] at htmem
  have hTnn : 0 ≤ (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ
    (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t :=
    div_nonneg ENNReal.toReal_nonneg (le_of_lt htmem)
  have hBlt : (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp (-δ ^ 2
    / (16 * t)) < ε ^ p.toReal := by
    linarith [hδsmall, htail]
  have hpow_le : ((eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ
    (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t) ^ p.toReal
      ≤ (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp (-δ ^ 2 / (16
        * t)) := by
    have hLnn : 0 ≤ (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace
      ℝ (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal :=
      ENNReal.toReal_nonneg
    have htnn : 0 ≤ t := le_of_lt htmem
    have htq : 0 < t ^ p.toReal := by positivity
    have h := hMain δ t hδpos htmem (le_of_lt ht1)
    rw [Real.div_rpow hLnn htnn, div_le_iff₀ htq]
    rw [mul_comm (t ^ p.toReal) _] at h
    exact h
  have hle : (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin
    n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t
      ≤ ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp (-δ ^ 2 /
        (16 * t))) ^ (1 / p.toReal) := by
    have h1 : ((((eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ
      (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t) ^ p.toReal) ^ (1 /
        p.toReal))
        ≤ ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp (-δ ^ 2 /
          (16 * t))) ^ (1 / p.toReal) :=
      Real.rpow_le_rpow (by positivity) hpow_le (by positivity)
    have h2 : ((((eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ
      (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t) ^ p.toReal) ^ (1 /
        p.toReal))
        = (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n)
          => ENNReal.ofReal (Φ n t y))) p volume).toReal / t := by
      rw [← Real.rpow_mul hTnn, hqq, Real.rpow_one]
    rwa [h2] at h1
  have hlt : ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp (-δ ^ 2
    / (16 * t))) ^ (1 / p.toReal) < ε := by
    have hBnn' : 0 ≤ (∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp
      (-δ ^ 2 / (16 * t)) :=
      hBnn δ t hδpos
    have h1 : ((∑ i, ∑ j, secondPartialModulus n φ i j δ) * (R + δ) ^ n * K1 + K2 * Real.exp (-δ ^
      2 / (16 * t))) ^ (1 / p.toReal)
        < (ε ^ p.toReal) ^ (1 / p.toReal) :=
      Real.rpow_lt_rpow hBnn' hBlt (by positivity)
    have h2 : ((ε ^ p.toReal) ^ (1 / p.toReal)) = ε := by
      rw [← Real.rpow_mul (le_of_lt hε), hqq, Real.rpow_one]
    rwa [h2] at h1
  have hdist : dist ((eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y :
    EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t) 0
      = (eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y : EuclideanSpace ℝ (Fin n)
        => ENNReal.ofReal (Φ n t y))) p volume).toReal / t := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hTnn]
  have hgoal : dist ((eLpNorm (fun x => ∫ y, Dfn n φ x y ∂(volume.withDensity fun y :
    EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y))) p volume).toReal / t) 0 < ε :=
      by
    rw [hdist]
    exact lt_of_le_of_lt hle hlt
  exact hgoal

end C4

section LpEstApplyHelpers

open MeasureTheory
open scoped Topology

private theorem dij_bounded (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n)
    (hcont : Continuous (secondPartialFn n φ i j))
    (hsupp : HasCompactSupport (secondPartialFn n φ i j)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |secondPartialFn n φ i j x| ≤ M := by
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hcont
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

private theorem eLpNorm_toReal_rpow_eq_lintegral_ofReal (n : ℕ) {p : ENNReal} (hp0 : p ≠ 0)
    (hpTop : p ≠ ⊤) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hae : AEStronglyMeasurable f volume) (hq_pos : 0 < p.toReal) :
    (eLpNorm f p volume).toReal ^ p.toReal
      = (∫⁻ x, ENNReal.ofReal ‖f x‖ ^ p.toReal ∂volume).toReal := by
  have hEq := eLpNorm_eq_lintegral_rpow_eNorm_toReal (μ := volume) (f := f) hp0 hpTop hae
  have hInt : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume)
      = ∫⁻ x, ENNReal.ofReal ‖f x‖ ^ p.toReal ∂volume := by
    apply lintegral_congr
    intro x
    rw [Real.eNorm_eq_ofReal_abs, Real.norm_eq_abs]
  rw [hInt] at hEq
  have hq_ne : p.toReal ≠ 0 := ne_of_gt hq_pos
  calc (eLpNorm f p volume).toReal ^ p.toReal
      = (((∫⁻ x, ENNReal.ofReal ‖f x‖ ^ p.toReal ∂volume) ^ (1 / p.toReal) : ENNReal).toReal)
        ^ p.toReal := by rw [hEq]
    _ = ((∫⁻ x, ENNReal.ofReal ‖f x‖ ^ p.toReal ∂volume).toReal ^ (1 / p.toReal)) ^ p.toReal := by
        rw [← ENNReal.toReal_rpow]
    _ = (∫⁻ x, ENNReal.ofReal ‖f x‖ ^ p.toReal ∂volume).toReal := by
        rw [← Real.rpow_mul ENNReal.toReal_nonneg]
        rw [one_div, inv_mul_cancel₀ hq_ne, Real.rpow_one]

end LpEstApplyHelpers

section IsProb

open MeasureTheory
open scoped Topology


private theorem isProbability_heatDensity (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hInt : ∫ (y : EuclideanSpace ℝ (Fin n)), Φ n t y = 1) :
    IsProbabilityMeasure
      (volume.withDensity fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (Φ n t y)) :=
        by
  have hcont : Continuous (Φ n t) := by
    unfold heatKernel
    continuity
  have hmeas : AEStronglyMeasurable (Φ n t) volume :=
    hcont.aestronglyMeasurable
  have hnn : ∀ y, 0 ≤ Φ n t y := by
    intro y
    unfold heatKernel
    refine mul_nonneg (Real.rpow_nonneg ?_ _) (Real.exp_nonneg _)
    positivity
  have hnn_ae : 0 ≤ᵐ[volume] (Φ n t) := Filter.Eventually.of_forall hnn
  have hfi : Integrable (Φ n t) volume := by
    by_contra hcon
    rw [integral_undef hcon] at hInt
    norm_num at hInt
  rw [isProbabilityMeasure_iff, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal hfi hnn_ae, hInt,
    ENNReal.ofReal_one]

end IsProb

section HalfAsm

open MeasureTheory





private theorem coord_continuous (n : ℕ) (i : Fin n) :
    Continuous (fun y : EuclideanSpace ℝ (Fin n) => y i) :=
  PiLp.continuous_apply _ _ i

private theorem abs_mul_le_half_sum_sq (a b : ℝ) : |a * b| ≤ (a * a + b * b) / 2 := by
  have h0 := sq_nonneg (|a| - |b|)
  rw [sub_sq, sq_abs a, sq_abs b] at h0
  rw [abs_mul, ← pow_two a, ← pow_two b]
  linarith

private theorem integrable_kernel_coord_mul (n : ℕ) (t : ℝ) (ht : 0 < t)
    (hm2 : ∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)),
      Φ n t y * (y i * y j) = if i = j then 2 * t else 0)
    (i j : Fin n) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y * (y i * y j)) := by
  have hdiag : ∀ k : Fin n, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Φ n t y * (y k * y k)) := by
    intro k
    by_contra hnot
    have hval := hm2 k k
    rw [integral_undef hnot, ite_eq_left rfl] at hval
    have hne : (2 : ℝ) * t ≠ 0 := ne_of_gt (by linarith)
    exact hne hval.symm
  by_cases hij : i = j
  · subst hij
    exact hdiag i
  · have hg : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (Φ n t y * (y i * y i) + Φ n t y * (y j * y j)) / 2) :=
      ((hdiag i).add (hdiag j)).div_const 2
    have hf : AEStronglyMeasurable
        (fun y : EuclideanSpace ℝ (Fin n) => Φ n t y * (y i * y j)) volume :=
      ((heatKernel_continuous n t ht).mul
        ((coord_continuous n i).mul (coord_continuous n j))).aestronglyMeasurable
    have hbound : ∀ y : EuclideanSpace ℝ (Fin n),
        ‖Φ n t y * (y i * y j)‖ ≤
          (Φ n t y * (y i * y i) + Φ n t y * (y j * y j)) / 2 := by
      intro y
      have hk : 0 ≤ Φ n t y := heatKernel_nonneg n t ht y
      have hmain := abs_mul_le_half_sum_sq (y i) (y j)
      rw [Real.norm_eq_abs]
      calc |Φ n t y * (y i * y j)|
          = Φ n t y * |y i * y j| := by rw [abs_mul, abs_of_nonneg hk]
        _ ≤ Φ n t y * ((y i * y i + y j * y j) / 2) :=
            mul_le_mul_of_nonneg_left hmain hk
        _ = (Φ n t y * (y i * y i) + Φ n t y * (y j * y j)) / 2 := by ring
    exact Integrable.mono' hg hf (ae_of_all _ hbound)

/-- Half-part identification, assembled from Gaussian second moments
and the Laplacian identification. -/
private theorem gaussian_half_second_order_asm (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    (hMomentsThm : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
      ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
      ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
        = if i = j then 2 * t else 0))
    (hLapBridgeThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x : EuclideanSpace ℝ (Fin n)),
      Laplacian.laplacian φ x
        = ∑ i, deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) i r)))
            ((WithLp.toLp 2 (Function.update x i v)) i))
            (x i)) :
    ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
        * Real.exp (-‖y‖ ^ 2 / (4 * t)))
      * ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
      = t * Laplacian.laplacian φ x := by
  have _ := hφ_supp
  have hm2K : ∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)),
      Φ n t y * (y i * y j) = if i = j then 2 * t else 0 :=
    fun i j => by simpa only [heatKernel_euclideanSpace] using (hMomentsThm n ht).2.2 i j
  have hInt : ∀ i j : Fin n, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Φ n t y * (y i * y j)) :=
    fun i j => integrable_kernel_coord_mul n t ht hm2K i j
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
      Φ n t y * ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
        = ∑ i, ∑ j, Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i)) := by
    intro y
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hSumm : ∀ i j : Fin n, Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))) := by
    intro i j
    have h := (hInt i j).const_mul ((1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
    have heq : ∀ y : EuclideanSpace ℝ (Fin n),
        ((1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i)) * (Φ n t y * (y i * y j))
          = Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i)) :=
      fun y => by ring
    exact h.congr (ae_of_all _ heq)
  have hIn : ∀ i : Fin n, ∀ j ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))) :=
    fun i j _ => hSumm i j
  have hOut : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ j, Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))) :=
    fun i _ => integrable_finsetSum _ (fun j _ => hSumm i j)
  have hval : ∀ i j : Fin n, (∫ y : EuclideanSpace ℝ (Fin n),
      Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i)))
      = (1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i) * (if i = j then 2 * t else 0) := by
    intro i j
    have heq : ∀ y : EuclideanSpace ℝ (Fin n),
        Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
          = ((1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i)) * (Φ n t y * (y i * y j)) :=
      fun y => by ring
    simp only [heq, integral_const_mul, hm2K i j]
  have hcoll : ∀ i : Fin n, (∑ j, (1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i) * (if i = j then 2 * t else 0))
      = t *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) i r)))
          ((WithLp.toLp 2 (Function.update x i v)) i))
          (x i) := by
    intro i
    have hper : ∀ j : Fin n, (1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i) * (if i = j then 2 * t else 0)
        = (if j = i then (1 / 2 : ℝ) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) i r)))
          ((WithLp.toLp 2 (Function.update x i v)) i))
          (x i) * (2 * t) else 0) := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hji, ite_eq_right (Ne.symm hji), mul_zero]
    simp only [hper]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    ring
  simp only [← heatKernel_euclideanSpace]
  change ∫ (y : EuclideanSpace ℝ (Fin n)),
      Φ n t y * ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
      = t * Laplacian.laplacian φ x
  calc ∫ (y : EuclideanSpace ℝ (Fin n)),
          Φ n t y * ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i))
        = ∑ i, ∑ j, ∫ (y : EuclideanSpace ℝ (Fin n)),
            Φ n t y * ((1 / 2) * (y i * y j) *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) j r)))
          ((WithLp.toLp 2 (Function.update x i v)) j))
          (x i)) := by
          simp only [hpt]
          rw [integral_finsetSum _ hOut]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_finsetSum _ (hIn i)]
      _ = ∑ i, t *
        deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
          (WithLp.toLp 2 (Function.update x i v)) i r)))
          ((WithLp.toLp 2 (Function.update x i v)) i))
          (x i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [hval]
          exact hcoll i
      _ = t * Laplacian.laplacian φ x := by
          rw [← Finset.mul_sum, hLapBridgeThm n hφ x]

end HalfAsm

section P1Ennreal

open scoped Convolution

private theorem continuous_heatKernel (n : ℕ) (t : ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => Φ n t x := by
  unfold heatKernel
  fun_prop

private theorem memLp_top_heatKernel (n : ℕ) (t : ℝ) (ht : 0 < t) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => Φ n t x) ⊤ volume := by
  refine memLp_top_of_bound (continuous_heatKernel n t).aestronglyMeasurable
    ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)) ?_
  filter_upwards with x
  have hC : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) := by
    apply Real.rpow_nonneg
    positivity
  have hx2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  have he : -‖x‖ ^ 2 / (4 * t) ≤ (0 : ℝ) :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx2) (by positivity)
  have hexp : Real.exp (-‖x‖ ^ 2 / (4 * t)) ≤ 1 := Real.exp_le_one_iff.mpr he
  have hK : (0 : ℝ) ≤ Φ n t x := by
    rw [heatKernel_euclideanSpace]
    exact mul_nonneg hC (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hK, heatKernel_euclideanSpace]
  calc (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))
      ≤ (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp hC
    _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) := mul_one _

private theorem heatConvolution_eq_conv (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatConvolution n φ t x
      = (φ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Φ n t) x := by
  unfold heatConvolution
  rw [MeasureTheory.convolution_mul]

private theorem heatConvolution_fun_eq (n : ℕ) (φ : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ) :
    heatConvolution n φ t
      = φ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Φ n t :=
  funext (heatConvolution_eq_conv n φ t)

private theorem continuous_heatConvolution (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ) (t : ℝ) :
    Continuous (heatConvolution n φ t) := by
  have hK : LocallyIntegrable (fun x : EuclideanSpace ℝ (Fin n) => Φ n t x) volume :=
    (continuous_heatKernel n t).locallyIntegrable
  have hcont := HasCompactSupport.continuous_convolution_left
    (L := ContinuousLinearMap.mul ℝ ℝ) hφ_supp hφ.continuous hK
  rw [heatConvolution_fun_eq n φ t]
  exact hcont

private theorem integrable_heatConvolution (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ) (t : ℝ) (ht : 0 < t) :
    Integrable (heatConvolution n φ t) volume := by
  rw [heatConvolution_fun_eq n φ t]
  have hφint : Integrable φ volume :=
    hφ.continuous.integrable_of_hasCompactSupport hφ_supp
  have hKint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => Φ n t x) volume :=
    integrable_heatKernel ht
  exact Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hφint hKint

private theorem memLp_phi_of_contDiff (n : ℕ) {p : ENNReal}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ_supp : HasCompactSupport φ) : MemLp φ p volume :=
  hφ.continuous.memLp_of_hasCompactSupport hφ_supp

private theorem continuous_laplacian_phi (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (Laplacian.laplacian φ) := by
  classical
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)))]
  apply continuous_finsetSum
  intro i _
  exact (ContinuousMultilinearMap.uniformContinuous_eval_const _).continuous.comp
    (hφ.continuous_iteratedFDeriv le_rfl)

private theorem hasCompactSupport_laplacian_phi (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ_supp : HasCompactSupport φ) : HasCompactSupport (Laplacian.laplacian φ) := by
  apply hφ_supp.mono'
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxout
  rw [notMem_tsupport_iff_eventuallyEq] at hxout
  have hΔ := InnerProductSpace.laplacian_congr_nhds hxout
  have hΔ0 : Laplacian.laplacian (0 : EuclideanSpace ℝ (Fin n) → ℝ) = 0 :=
    InnerProductSpace.laplacian_const
  rw [hΔ0] at hΔ
  have h2 := Filter.Eventually.self_of_nhds hΔ
  have hx0 : Laplacian.laplacian φ x = 0 := by simpa using h2
  exact hx hx0

private theorem memLp_laplacian_phi (n : ℕ) {p : ENNReal}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ_supp : HasCompactSupport φ) : MemLp (Laplacian.laplacian φ) p volume :=
  (continuous_laplacian_phi n hφ).memLp_of_hasCompactSupport
    (hasCompactSupport_laplacian_phi n hφ_supp)

private theorem enorm_heatConvolution_le (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (_hφ_supp : HasCompactSupport φ) (t : ℝ) (_ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(heatConvolution n φ t) x‖ₑ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm φ 1 volume
      * eLpNorm (Φ n t) ⊤ volume := by
  rw [heatConvolution_fun_eq n φ t]
  exact eNorm_convolution_le (L := ContinuousLinearMap.mul ℝ ℝ) (p := 1) (q := ⊤)
    hφ.continuous.aestronglyMeasurable (continuous_heatKernel n t).aestronglyMeasurable x

private theorem eLpNorm_bound_heatConvolution (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ) (t : ℝ) (ht : 0 < t) :
    ‖ContinuousLinearMap.mul ℝ ℝ‖ₑ * eLpNorm φ 1 volume
      * eLpNorm (Φ n t) ⊤ volume < ⊤ := by
  have hφ1 : eLpNorm φ 1 volume < ⊤ := memLp_phi_of_contDiff n hφ hφ_supp (p := 1)
  have hKt : eLpNorm (Φ n t) ⊤ volume < ⊤ := memLp_top_heatKernel n t ht
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top eNorm_lt_top hφ1) hKt

private theorem eLpNorm_lt_top_of_uniform_enorm_bound (n : ℕ) {p : ENNReal}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hf : AEStronglyMeasurable f volume) (hint : Integrable f volume) (B : ENNReal)
    (hB : B < ⊤) (hle : ∀ x, ‖f x‖ₑ ≤ B) : eLpNorm f p volume < ⊤ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  rw [eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 hp hf]
  have hq1 : (1 : ℝ) ≤ p.toReal := by
    have h := (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).mpr hp1
    simpa using h
  have hexp : (0 : ℝ) ≤ p.toReal - 1 := by linarith
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖f x‖ₑ ^ p.toReal ≤ B ^ (p.toReal - 1) * ‖f x‖ₑ := by
    intro x
    have hsplit : ‖f x‖ₑ ^ p.toReal = ‖f x‖ₑ ^ (p.toReal - 1) * ‖f x‖ₑ ^ (1 : ℝ) := by
      have h := ENNReal.rpow_add_of_nonneg (p.toReal - 1) 1 hexp zero_le_one (x := ‖f x‖ₑ)
      rw [show p.toReal - 1 + 1 = p.toReal by ring] at h
      exact h
    rw [hsplit, ENNReal.rpow_one]
    exact mul_le_mul_left (ENNReal.rpow_le_rpow (hle x) hexp) _
  have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => ‖f x‖ₑ) volume :=
    hf.aemeasurable.eNorm
  have hint' : ∫⁻ x, ‖f x‖ₑ ∂volume < ⊤ :=
    hasFiniteIntegral_iff_eNorm.mp hint.hasFiniteIntegral
  calc ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂volume
      ≤ ∫⁻ x, B ^ (p.toReal - 1) * ‖f x‖ₑ ∂volume :=
        lintegral_mono_ae (Filter.Eventually.of_forall hpt)
    _ = B ^ (p.toReal - 1) * ∫⁻ x, ‖f x‖ₑ ∂volume := lintegral_const_mul'' _ hmeas
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hexp hB.ne) hint'

private theorem memLp_heatConvolution (n : ℕ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ_supp : HasCompactSupport φ) (t : ℝ) (ht : 0 < t) :
    MemLp (heatConvolution n φ t) p volume := by
  apply eLpNorm_lt_top_of_uniform_enorm_bound n hp1 hp
  · exact (continuous_heatConvolution n hφ hφ_supp t).aestronglyMeasurable
  · exact integrable_heatConvolution n hφ hφ_supp t ht
  · exact eLpNorm_bound_heatConvolution n hφ hφ_supp t ht
  · exact fun x => enorm_heatConvolution_le n hφ hφ_supp t ht x

private theorem eLpNorm_generator_eventually_ne_top (n : ℕ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφ_supp : HasCompactSupport φ) (t : ℝ) (ht : 0 < t) :
    eLpNorm (fun x => heatConvolution n φ t x - φ x
      - t * Laplacian.laplacian φ x) p volume ≠ ⊤ := by
  have hH : MemLp (heatConvolution n φ t) p volume :=
    memLp_heatConvolution n hp1 hp.ne hφ hφ_supp t ht
  have hP : MemLp φ p volume := memLp_phi_of_contDiff n hφ hφ_supp
  have hL : MemLp (fun x => t * Laplacian.laplacian φ x) p volume :=
    (memLp_laplacian_phi n hφ hφ_supp).const_mul t
  have hmem : MemLp (fun x => heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x)
      p volume := (hH.sub hP).sub hL
  exact ne_of_lt hmem

private theorem heat_semigroup_generator_eq_laplacian_ennreal_of_real (n : ℕ) {p : ENNReal}
    (_hp1 : 1 ≤ p)
    (_hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
    (_hφ_supp : HasCompactSupport φ)
    (hReal : Filter.Tendsto
      (fun t : ℝ => (eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hFinite : ∀ (t : ℝ), 0 < t →
      eLpNorm (fun x => heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x) p volume ≠ ⊤) :
    Filter.Tendsto
      (fun t : ℝ => eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume / ENNReal.ofReal t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hEq : (fun t : ℝ => ENNReal.ofReal
      ((eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun t : ℝ => eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume / ENNReal.ofReal t := by
    filter_upwards [self_mem_nhdsWithin] with t htmem
    simp only [Set.mem_Ioi] at htmem
    rw [ENNReal.ofReal_div_of_pos htmem, ENNReal.ofReal_toReal (hFinite t htmem)]
  have hT := ENNReal.tendsto_ofReal hReal
  simp only [ENNReal.ofReal_zero] at hT
  exact hT.congr' hEq

private theorem heat_semigroup_generator_eq_laplacian_of_ennreal (n : ℕ) {p : ENNReal}
    (_hp1 : 1 ≤ p)
    (_hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (_hφ : ContDiff ℝ 2 φ)
    (_hφ_supp : HasCompactSupport φ)
    (hENN : Filter.Tendsto
      (fun t : ℝ => eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume / ENNReal.ofReal t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto
      (fun t : ℝ => (eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hEq : (fun t : ℝ => (eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume / ENNReal.ofReal t).toReal)
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun t : ℝ => (eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t := by
    filter_upwards [self_mem_nhdsWithin] with t htmem
    simp only [Set.mem_Ioi] at htmem
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal htmem.le]
  have hT := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hENN
  simp only [ENNReal.toReal_zero] at hT
  exact hT.congr' hEq

end P1Ennreal

section FinalGlueH5

/-- **The heat semigroup's generator is the Laplacian, in `ENNReal`.** Let `1 ≤ p < ∞` and let
`φ` be a compactly supported `C²` function on `EuclideanSpace ℝ (Fin n)`. Then
`eLpNorm (heatConvolution n φ t - φ - t * Δφ) p volume / t → 0` as `t → 0⁺`: the right-hand
difference quotient `(heatConvolution n φ t - φ) / t` converges to `Δφ` in `L^p`. This
`ENNReal`-valued form is the genuine `L^p` statement: `ENNReal.toReal` sends `⊤` to `0`, so a
real-valued limit alone could report convergence even when the remainder is not in `L^p`. -/
theorem heat_semigroup_generator_eq_laplacian_ennreal (n : ℕ) {p : ENNReal}
    (hp1 : 1 ≤ p) (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ) :
    Filter.Tendsto
      (fun t : ℝ => eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume / ENNReal.ofReal t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hMoments : ∀ (n : ℕ) {t : ℝ}, 0 < t →
      (∫ (y : EuclideanSpace ℝ (Fin n)), (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)) = 1)
        ∧ (∀ i : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)),
            ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖y‖ ^ 2 / (4 * t))) * y i = 0)
        ∧ (∀ i j : Fin n, ∫ (y : EuclideanSpace ℝ (Fin n)),
            ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
              * Real.exp (-‖y‖ ^ 2 / (4 * t))) * (y i * y j)
            = if i = j then 2 * t else 0) :=
    fun n t ht => ⟨heatKernel_mass n ht, fun i => heatKernel_firstMoment n ht i,
      fun i j => heatKernel_secondMoment n ht i j⟩
  have hTaylor : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x y : EuclideanSpace ℝ (Fin n)),
      φ (x - y) - φ x + ∑ i, y i * deriv (fun s => φ (WithLp.toLp 2 (Function.update x i s))) (x i)
        = ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i) :=
    fun n φ h1 x y => taylor_two_integral_remainder_lpasm n h1 x y
  have hLapBridge : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x : EuclideanSpace ℝ (Fin n)),
      Laplacian.laplacian φ x
        = ∑ i, deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) i r)))
            ((WithLp.toLp 2 (Function.update x i v)) i))
            (x i) :=
    fun n φ h1 x => laplacian_eq_sum_diag_secondPartial n h1 x
  have hHalf : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-‖y‖ ^ 2 / (4 * t)))
        * ((1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x i v)) j r)))
            ((WithLp.toLp 2 (Function.update x i v)) j))
            (x i))
        = t * Laplacian.laplacian φ x :=
    fun n φ h1 h2 t ht x =>
      gaussian_half_second_order_asm n h1 h2 ht x hMoments hLapBridge
  have hSplit : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → ∀ (x y : EuclideanSpace ℝ (Fin n)),
      ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
          deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
            ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
            ((x - s • y) i)
        = (1 / 2 : ℝ) * ∑ i, ∑ j, y i * y j *
            deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)
          + ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)) :=
    fun n φ h1 x y => s_integral_split n h1 x y
  have hRem : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ},
      ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∀ {t : ℝ}, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      heatConvolution n φ t x - φ x - t * Laplacian.laplacian φ x
        = ∫ (y : EuclideanSpace ℝ (Fin n)), ((4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * Real.exp (-‖y‖ ^ 2 / (4 * t)))
          * ∫ s in (0 : ℝ)..1, (1 - s) * ∑ i, ∑ j, y i * y j *
            (deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update (x - s • y) i v)) j r)))
              ((WithLp.toLp 2 (Function.update (x - s • y) i v)) j))
              ((x - s • y) i)
            - deriv (fun v => deriv (fun r => φ (WithLp.toLp 2 (Function.update
              (WithLp.toLp 2 (Function.update x i v)) j r)))
              ((WithLp.toLp 2 (Function.update x i v)) j))
              (x i)) :=
    fun n φ h1 h2 t ht x =>
      heatConvolution_sub_eq_remainder_asm n h1 h2 ht x hMoments hTaylor hHalf hSplit
  have hDij : ∀ (i j : Fin n),
      Continuous (secondPartialFn n φ i j)
        ∧ HasCompactSupport (secondPartialFn n φ i j)
        ∧ UniformContinuous (secondPartialFn n φ i j)
        ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
        ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖)
        ∧ Filter.Tendsto (secondPartialModulus n φ i j)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    fun i j => secondPartial_props n hφ hφ_supp i j
  have hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      (∀ (x z : EuclideanSpace ℝ (Fin n)),
        |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
          ≤ secondPartialModulus n φ i j ‖z‖) →
      ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
      |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
        ≤ secondPartialModulus n φ i j ‖y‖ :=
    fun n φ i j hcont hsupp hdom x y s hs0 hs1 =>
      secondPartial_sub_le_modulus_aux n φ i j hcont hsupp hdom x y s hs0 hs1
  have hModMonoThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
      Continuous (secondPartialFn n φ i j) →
      HasCompactSupport (secondPartialFn n φ i j) →
      ∀ {r₁ r₂ : ℝ}, 0 ≤ r₁ → r₁ ≤ r₂ →
      secondPartialModulus n φ i j r₁ ≤ secondPartialModulus n φ i j r₂ :=
    fun n φ i j hcont hsupp r₁ r₂ hr₁ hle =>
      secondPartialModulus_mono_aux n φ i j hcont hsupp hr₁ hle
  have hC2bypass : ∀ (n : ℕ) (hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p)
      (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
      (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ)
      (hAthm : ∀ (n : ℕ) (hn : 0 < n) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p < ⊤)
        {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
        (hφ_supp : HasCompactSupport φ)
        (hDijThm : ∀ (i j : Fin n),
          Continuous (secondPartialFn n φ i j)
            ∧ HasCompactSupport (secondPartialFn n φ i j)
            ∧ UniformContinuous (secondPartialFn n φ i j)
            ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
            ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
                |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                  ≤ secondPartialModulus n φ i j ‖z‖)
            ∧ Filter.Tendsto (secondPartialModulus n φ i j)
                (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
        (hSubThm : ∀ (n : ℕ) {φ : EuclideanSpace ℝ (Fin n) → ℝ} (i j : Fin n),
          Continuous (secondPartialFn n φ i j) →
          HasCompactSupport (secondPartialFn n φ i j) →
          (∀ (x z : EuclideanSpace ℝ (Fin n)),
            |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
              ≤ secondPartialModulus n φ i j ‖z‖) →
          ∀ (x y : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 ≤ s → s ≤ 1 →
          |secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x|
            ≤ secondPartialModulus n φ i j ‖y‖),
        ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ (i j : Fin n) (y : EuclideanSpace ℝ (Fin n))
          (s : ℝ), 0 ≤ s → s ≤ 1 →
          ∫⁻ x, ENNReal.ofReal
            ‖secondPartialFn n φ i j (x - s • y) - secondPartialFn n φ i j x‖ ^ p.toReal ∂volume
            ≤ ENNReal.ofReal (C * secondPartialModulus n φ i j ‖y‖ * (R + ‖y‖) ^ n))
      (hSumThm : ∀ (n : ℕ) (y : EuclideanSpace ℝ (Fin n)),
        ∑ i : Fin n, ∑ j : Fin n, |y i * y j| ≤ (n : ℝ) ^ 2 * ‖y‖ ^ 2)
      (hDijThm : ∀ (i j : Fin n),
        Continuous (secondPartialFn n φ i j)
          ∧ HasCompactSupport (secondPartialFn n φ i j)
          ∧ UniformContinuous (secondPartialFn n φ i j)
          ∧ (∀ r : ℝ, 0 ≤ secondPartialModulus n φ i j r)
          ∧ (∀ (x z : EuclideanSpace ℝ (Fin n)),
              |secondPartialFn n φ i j (x - z) - secondPartialFn n φ i j x|
                ≤ secondPartialModulus n φ i j ‖z‖)
          ∧ Filter.Tendsto (secondPartialModulus n φ i j)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)),
      ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ y : EuclideanSpace ℝ (Fin n),
      (∫⁻ x, ENNReal.ofReal ‖Dfn n φ x y‖ ^ p.toReal ∂volume)
      ≤ ENNReal.ofReal ((((1 : ℝ) / 2) ^ (p.toReal - 1) * ((1 : ℝ) / 2) * (((n : ℝ) ^ 2) ^
        p.toReal) * C)
        * ((∑ i, ∑ j, secondPartialModulus n φ i j ‖y‖) * (R + ‖y‖) ^ n * ‖y‖ ^ (2 * p.toReal))) :=
    fun n hn p hp1 hp φ hφ hφ_supp hAthm hSumThm hDijThm =>
      Dfn_lintegral_le_v2 n hn hp1 hp hφ hφ_supp hAthm hSumThm hDijThm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact heat_semigroup_generator_eq_laplacian_ennreal_of_real 0 hp1 hp hφ hφ_supp
      (n_zero_case hp1 hp hφ hφ_supp hRem)
      (eLpNorm_generator_eventually_ne_top 0 hp1 hp hφ hφ_supp)
  · exact heat_semigroup_generator_eq_laplacian_ennreal_of_real n hp1 hp hφ hφ_supp
      (tendsto_generator_of_diff_le n hn hp1 hp hφ hφ_supp
        lintegral_norm_integral_le hMoments hDij hRem hSubThm sum_abs_mul_le_norm_sq
        eLpNorm_toReal_rpow_eq_lintegral_ofReal isProbability_heatDensity dij_bounded
        hModMonoThm lintegral_diff_le jensen_density_bundle hC2bypass y_integral_estimate
        smallBall_integral_bound largeCompl_integral_bound)
      (eLpNorm_generator_eventually_ne_top n hp1 hp hφ hφ_supp)

/-- **The heat semigroup's generator is the Laplacian.** Let `1 ≤ p < ∞` and let `φ` be a
compactly supported `C²` function on `EuclideanSpace ℝ (Fin n)`. Then
`‖heatConvolution n φ t - φ - t * Δφ‖_p / t → 0` as `t → 0⁺`: the right-hand difference quotient
`(heatConvolution n φ t - φ) / t` converges to `Δφ` in `L^p`. This is the real-valued corollary
of `heat_semigroup_generator_eq_laplacian_ennreal`. -/
theorem heat_semigroup_generator_eq_laplacian (n : ℕ) {p : ENNReal}
    (hp1 : 1 ≤ p) (hp : p < ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ_supp : HasCompactSupport φ) :
    Filter.Tendsto
      (fun t : ℝ =>
        (eLpNorm (fun x => heatConvolution n φ t x - φ x
          - t * Laplacian.laplacian φ x) p volume).toReal / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact heat_semigroup_generator_eq_laplacian_of_ennreal n hp1 hp hφ hφ_supp
    (heat_semigroup_generator_eq_laplacian_ennreal n hp1 hp hφ hφ_supp)


end FinalGlueH5

end MathlibExt.Analysis.PDE.HeatKernel
