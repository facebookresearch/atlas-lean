/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.MGFAnalytic
import MathlibExt.Probability.GaussianLogSobolev

/-!
# Concentration of Lipschitz functions of a standard Gaussian vector

Let `γ` be the standard Gaussian measure on `ℝⁿ`, let `L ≥ 0` and let `f : ℝⁿ → ℝ` be
`L`-Lipschitz for the Euclidean norm. Then `f - ∫ f dγ` is sub-Gaussian with variance proxy `L²`:
`∫ exp (t (f - ∫ f dγ)) dγ ≤ exp (L² t² / 2)` for every real `t`, and hence
`γ {x | t ≤ |f x - ∫ f dγ|} ≤ 2 exp (-t² / (2 L²))` for every `t ≥ 0` (M. J. Wainwright,
*High-Dimensional Statistics*, 2019, §2.3; R. Vershynin, arXiv:1011.3027, Proposition 5.34, for
the one-sided tail). When `L = 0`, Lean reads `-t² / (2 L²)` as `0`, since it defines division by
zero as zero, so the right-hand side of the tail bound is `2` and the bound holds trivially (`f`
is then constant).

The variance proxy `L²` cannot be lowered: for `u` with `‖u‖ = L`, the linear functional
`x ↦ ⟪u, x⟫` is `L`-Lipschitz and centred, and it is a Gaussian variable of variance exactly `L²`,
whose moment generating function is `exp (L² t² / 2)`.

## Proof outline

The proof is Herbst's argument applied to Gross' logarithmic Sobolev inequality
(`MathlibExt.Probability.GaussianLogSobolev`), as in M. Ledoux (1999, §2.3).

1. *Herbst's differential inequality.* Let `g` be smooth and `L`-Lipschitz, so that `‖Dg‖ ≤ L`,
   and let `X = g - ∫ g dγ`. By Fernique's theorem, `X` has exponential moments of all orders.
   Gross' inequality for the density `exp (t X) / ∫ exp (t X) dγ`, whose Fisher information is at
   most `L² t²`, gives `t K'(t) - K(t) ≤ L² t² / 2` for the cumulant generating function
   `K(t) = log ∫ exp (t X) dγ`.
2. *Integration.* The function `t ↦ K(t) / t - L² t / 2` has a nonpositive derivative on
   `t > 0` and on `t < 0`, and it tends to `K'(0) = ∫ X dγ = 0` as `t → 0`. Hence
   `K(t) ≤ L² t² / 2` for every `t`.
3. *Smoothing.* Convolving a Lipschitz `f` with a normed bump function supported in the ball of
   radius `ε` gives a smooth `L`-Lipschitz function `g` with `|g - f| ≤ L ε`, so that
   `∫ exp (t (f - ∫ f dγ)) dγ ≤ exp (2 |t| L ε) ∫ exp (t (g - ∫ g dγ)) dγ`. Let `ε → 0`.
4. *Tails.* The Chernoff bound for sub-Gaussian variables, applied to `f - ∫ f dγ` and to its
   negative, gives the two-sided tail bound.

## Main results

* `lipschitz_concentration_stdGaussian`: the sub-Gaussian bound and the tail bound.

## Implementation notes

The theorem keeps the full name it had in the wanted module, so its namespace still reads
`HighDimensionalStatisticsWanted`. The intermediate steps are private and are stated for the
standard Gaussian measure on any finite-dimensional real inner product space.

## References

* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
  University Press, 2019, §2.3.
* R. Vershynin, Introduction to the non-asymptotic analysis of random matrices, in *Compressed
  Sensing: Theory and Applications*, Cambridge University Press, 2012, arXiv:1011.3027,
  Proposition 5.34.
* M. Ledoux, Concentration of measure and logarithmic Sobolev inequalities, *Séminaire de
  Probabilités XXXIII*, Lecture Notes in Math. 1709, Springer, 1999, 120–216, §2.3.
* L. Gross, Logarithmic Sobolev inequalities, *Amer. J. Math.* 97 (1975), 1061–1083.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology Real
open scoped NNReal ENNReal ContDiff Convolution

namespace MathlibExt.Probability.HighDimensionalStatisticsWanted

/-! ### Herbst's argument -/

section Herbst

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

/-- **Herbst's argument.** If `X` is centred, has exponential moments of all orders and
`t (cgf X)'(t) - cgf X t ≤ c t² / 2` for every `t`, then `cgf X t ≤ c t² / 2` for every `t`. -/
private lemma cgf_le_of_mul_deriv_cgf_sub_cgf_le
    (hexp : ∀ t : ℝ, Integrable (fun y => exp (t * X y)) μ) (hmean : μ[X] = 0) {c : ℝ}
    (hH : ∀ t : ℝ, t * deriv (cgf X μ) t - cgf X μ t ≤ c * t ^ 2 / 2) (t : ℝ) :
    cgf X μ t ≤ c * t ^ 2 / 2 := by
  have hint : interior (integrableExpSet X μ) = Set.univ := by
    rw [Set.eq_univ_of_forall (s := integrableExpSet X μ) hexp, interior_univ]
  have hd : ∀ s, HasDerivAt (cgf X μ) (deriv (cgf X μ) s) s := fun s =>
    (analyticAt_cgf (by simp [hint])).differentiableAt.hasDerivAt
  set ψ : ℝ → ℝ := fun s => cgf X μ s / s - c * s / 2 with hψ_def
  have hψd : ∀ s, s ≠ 0 →
      HasDerivAt ψ ((s * deriv (cgf X μ) s - cgf X μ s) / s ^ 2 - c / 2) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => cgf X μ s / s)
        ((deriv (cgf X μ) s * s - cgf X μ s * 1) / s ^ 2) s := (hd s).div (hasDerivAt_id' s) hs
    have h2 : HasDerivAt (fun s : ℝ => c * s / 2) (c * 1 / 2) s :=
      ((hasDerivAt_id' s).const_mul c).div_const 2
    convert h1.sub h2 using 1
    ring
  have hψd_nonpos : ∀ s, s ≠ 0 → (s * deriv (cgf X μ) s - cgf X μ s) / s ^ 2 - c / 2 ≤ 0 := by
    intro s hs
    rw [sub_nonpos, div_le_iff₀ (by positivity)]
    linarith [hH s]
  have hslope : Tendsto (fun s => cgf X μ s / s) (𝓝[≠] 0) (𝓝 0) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp (hd 0))
    rw [deriv_cgf_zero (by simp [hint]), hmean, zero_div] at h
    refine h.congr fun s => ?_
    simp [cgf_zero, div_eq_inv_mul]
  have hψlim : Tendsto ψ (𝓝[≠] 0) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => c * s / 2) (𝓝[≠] 0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => c * s / 2) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using hslope.sub h
  have hanti : ∀ D : Set ℝ, Convex ℝ D → IsOpen D → (∀ s ∈ D, s ≠ 0) → AntitoneOn ψ D := by
    intro D hD hDo hD0
    refine antitoneOn_of_deriv_nonpos hD ?_ ?_ ?_
    · exact fun s hs => (hψd s (hD0 s hs)).continuousAt.continuousWithinAt
    · intro s hs
      rw [hDo.interior_eq] at hs
      exact (hψd s (hD0 s hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [hDo.interior_eq] at hs
      rw [(hψd s (hD0 s hs)).deriv]
      exact hψd_nonpos s (hD0 s hs)
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hA := hanti (Set.Iio 0) (convex_Iio 0) isOpen_Iio fun s hs => hs.ne
    have h0 : 0 ≤ ψ t := by
      refine le_of_tendsto (x := 𝓝[<] 0)
        (hψlim.mono_left (nhdsWithin_mono _ fun s hs => ?_)) ?_
      · exact (Set.mem_Iio.mp hs).ne
      · filter_upwards [Ioo_mem_nhdsLT ht] with s hs
        exact hA ht hs.2 hs.1.le
    have h1 : c * t / 2 ≤ cgf X μ t / t := by simpa [hψ_def, sub_nonneg] using h0
    rw [le_div_iff_of_neg ht] at h1
    linarith
  · simp [cgf_zero]
  · have hA := hanti (Set.Ioi 0) (convex_Ioi 0) isOpen_Ioi fun s hs => hs.ne'
    have h0 : ψ t ≤ 0 := by
      refine ge_of_tendsto (x := 𝓝[>] 0)
        (hψlim.mono_left (nhdsWithin_mono _ fun s hs => ?_)) ?_
      · exact (Set.mem_Ioi.mp hs).ne'
      · filter_upwards [Ioo_mem_nhdsGT ht] with s hs
        exact hA hs.1 ht hs.2.le
    have h1 : cgf X μ t / t ≤ c * t / 2 := by simpa [hψ_def, sub_nonpos] using h0
    rw [div_le_iff₀ ht] at h1
    linarith

end Herbst

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The Herbst inequality from Gross' inequality -/

/-- Gross' inequality applied to the density `exp (t X) / E[exp (t X)]` gives the Herbst
inequality `t (cgf X)'(t) - cgf X t ≤ L² t² / 2` for a smooth `X` with `‖DX‖ ≤ L` and
exponential moments of all orders. -/
private lemma mul_deriv_cgf_sub_cgf_le {X : E → ℝ} (hX : ContDiff ℝ ∞ X) {L : ℝ}
    (hgrad : ∀ x, ‖fderiv ℝ X x‖ ≤ L)
    (hexp : ∀ t : ℝ, Integrable (fun x => exp (t * X x)) (stdGaussian E)) (t : ℝ) :
    t * deriv (cgf X (stdGaussian E)) t - cgf X (stdGaussian E) t ≤ L ^ 2 * t ^ 2 / 2 := by
  set γ := stdGaussian E
  have hint : interior (integrableExpSet X γ) = Set.univ := by
    rw [Set.eq_univ_of_forall (s := integrableExpSet X γ) hexp, interior_univ]
  have hmem : t ∈ interior (integrableExpSet X γ) := by simp [hint]
  set Z := mgf X γ t with hZ_def
  have hZ : 0 < Z := mgf_pos (hexp t)
  rw [deriv_cgf hmem]
  set f : E → ℝ := fun x => exp (t * X x) / Z with hf_def
  have hf : ContDiff ℝ ∞ f := ((contDiff_const.mul hX).exp).div_const Z
  have hfpos : ∀ x, 0 < f x := fun x => div_pos (exp_pos _) hZ
  have hfi : Integrable f γ := (hexp t).div_const Z
  have hfint : ∫ x, f x ∂γ = 1 := by
    rw [integral_div]
    exact div_self hZ.ne'
  have hLSI := MathlibExt.Probability.GaussianLogSobolevWanted.klDiv_withDensity_stdGaussian_le
    hf hfpos hfint
  have hderiv : ∀ x, ‖fderiv ℝ f x‖ = f x * |t| * ‖fderiv ℝ X x‖ := by
    intro x
    have h : HasFDerivAt f (Z⁻¹ • exp (t * X x) • t • fderiv ℝ X x) x := by
      convert (((hX.differentiable (by simp)) x).hasFDerivAt.const_mul t).exp.const_mul Z⁻¹
        using 1
      funext y
      simp [hf_def, div_eq_inv_mul]
    rw [h.fderiv, norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hZ).le,
      Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, hf_def]
    ring
  have hrhs : (1 / 2 : ℝ≥0∞) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂γ ≤
      ENNReal.ofReal (L ^ 2 * t ^ 2 / 2) := by
    have hpt : ∀ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ≤
        ENNReal.ofReal (L ^ 2 * t ^ 2 * f x) := by
      intro x
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_div_of_pos (hfpos x)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ (hfpos x), hderiv x]
      have h1 : |t| * ‖fderiv ℝ X x‖ ≤ |t| * L := by gcongr; exact hgrad x
      have h2 : (|t| * ‖fderiv ℝ X x‖) ^ 2 ≤ (|t| * L) ^ 2 := by gcongr
      have h3 : 0 ≤ f x * f x := by have := hfpos x; positivity
      calc (f x * |t| * ‖fderiv ℝ X x‖) ^ 2 = f x * f x * (|t| * ‖fderiv ℝ X x‖) ^ 2 := by ring
        _ ≤ f x * f x * (|t| * L) ^ 2 := by gcongr
        _ = L ^ 2 * t ^ 2 * f x * f x := by rw [mul_pow, sq_abs]; ring
    calc (1 / 2 : ℝ≥0∞) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂γ
        ≤ (1 / 2 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (L ^ 2 * t ^ 2 * f x) ∂γ := by
          gcongr with x
          exact hpt x
      _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (L ^ 2 * t ^ 2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi.const_mul _)
            (ae_of_all _ fun x => by have := hfpos x; positivity), integral_const_mul, hfint,
            mul_one]
      _ = ENNReal.ofReal (L ^ 2 * t ^ 2 / 2) := by
          rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
              rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat],
            ← ENNReal.ofReal_mul (by norm_num)]
          ring_nf
  have hac : γ.withDensity (fun x => ENNReal.ofReal (f x)) ≪ γ :=
    withDensity_absolutelyContinuous _ _
  have : IsFiniteMeasure (γ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hfi.hasFiniteIntegral
  have hkl : (klDiv (γ.withDensity fun x => ENNReal.ofReal (f x)) γ).toReal =
      ∫ x, klFun (f x) ∂γ := by
    rw [toReal_klDiv_eq_integral_klFun hac]
    refine integral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_withDensity γ (f := fun x => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp hf.continuous.measurable)] with x hx
    rw [hx, ENNReal.toReal_ofReal (hfpos x).le]
  have hle : ∫ x, klFun (f x) ∂γ ≤ L ^ 2 * t ^ 2 / 2 := by
    rw [← hkl]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hLSI.trans hrhs)
  have hXe : Integrable (fun x => X x * exp (t * X x)) γ := by
    simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1
  have hklfun : ∀ x, klFun (f x) =
      t / Z * (X x * exp (t * X x)) - log Z / Z * exp (t * X x) + 1 - f x := by
    intro x
    rw [klFun, hf_def, log_div (exp_pos _).ne' hZ.ne', log_exp]
    ring
  have hcalc : ∫ x, klFun (f x) ∂γ = t * (∫ x, X x * exp (t * X x) ∂γ) / Z - log Z := by
    have h1 : Integrable (fun x => t / Z * (X x * exp (t * X x))) γ := hXe.const_mul _
    have h2 : Integrable (fun x => log Z / Z * exp (t * X x)) γ := (hexp t).const_mul _
    have h12 : Integrable (fun x => t / Z * (X x * exp (t * X x)) - log Z / Z * exp (t * X x))
      γ := h1.sub h2
    have h123 : Integrable
        (fun x => t / Z * (X x * exp (t * X x)) - log Z / Z * exp (t * X x) + 1) γ :=
      h12.add (integrable_const _)
    simp_rw [hklfun]
    rw [integral_sub h123 hfi, integral_add h12 (integrable_const _),
      integral_sub h1 h2, integral_const_mul, integral_const_mul, hfint]
    have hZ' : ∫ x, exp (t * X x) ∂γ = Z := rfl
    rw [hZ']
    field_simp
    simp
  rw [hcalc] at hle
  simpa [cgf, ← hZ_def, mul_div_assoc] using hle

/-! ### Exponential moments and the smooth case -/

/-- A Lipschitz function has Gaussian exponential moments of all orders, by Fernique's
theorem. -/
private lemma integrable_exp_mul_of_lipschitzWith {g : E → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (t : ℝ) : Integrable (fun x => exp (t * g x)) (stdGaussian E) := by
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq (stdGaussian E)
  refine (hint.const_mul (exp (|t| * |g 0| + (|t| * K) ^ 2 / (4 * C)))).mono'
    (continuous_exp.comp (continuous_const.mul hg.continuous)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (exp_pos _).le, ← exp_add]
  refine exp_le_exp.mpr ?_
  have h1 : |g x| ≤ |g 0| + K * ‖x‖ := by
    have := hg.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at this
    linarith [abs_sub_abs_le_abs_sub (g x) (g 0)]
  have h2 : t * g x ≤ |t| * |g 0| + |t| * K * ‖x‖ := by
    calc t * g x ≤ |t| * |g x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |t| * (|g 0| + K * ‖x‖) := by gcongr
      _ = _ := by ring
  have h3 : |t| * K * ‖x‖ ≤ C * ‖x‖ ^ 2 + (|t| * K) ^ 2 / (4 * C) := by
    have h := sq_nonneg (2 * C * ‖x‖ - |t| * K)
    have h4 : (|t| * K) ^ 2 / (4 * C) * (4 * C) = (|t| * K) ^ 2 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  linarith

/-- Exponential moments of a shifted Lipschitz function. -/
private lemma integrable_exp_mul_sub_of_lipschitzWith {g : E → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (c t : ℝ) :
    Integrable (fun x => exp (t * (g x - c))) (stdGaussian E) := by
  refine ((integrable_exp_mul_of_lipschitzWith hg t).const_mul (exp (-(t * c)))).congr
    (ae_of_all _ fun x => ?_)
  simp only
  rw [← exp_add]
  ring_nf

/-- A Lipschitz function is integrable for the standard Gaussian measure. -/
private lemma integrable_of_lipschitzWith {g : E → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Integrable g (stdGaussian E) :=
  integrable_of_mem_interior_integrableExpSet (by
    rw [Set.eq_univ_of_forall (s := integrableExpSet g (stdGaussian E))
      (integrable_exp_mul_of_lipschitzWith hg), interior_univ]
    exact Set.mem_univ 0)

/-- **The Herbst bound for smooth Lipschitz functions.** If `g` is smooth and `L`-Lipschitz,
then `E[exp (t (g - E g))] ≤ exp (L² t² / 2)` under the standard Gaussian measure. -/
private lemma mgf_sub_integral_le_of_contDiff {g : E → ℝ} (hg : ContDiff ℝ ∞ g) {L : ℝ≥0}
    (hgL : LipschitzWith L g) (t : ℝ) :
    mgf (fun x => g x - ∫ y, g y ∂stdGaussian E) (stdGaussian E) t ≤
      exp ((L : ℝ) ^ 2 * t ^ 2 / 2) := by
  set γ := stdGaussian E
  set X : E → ℝ := fun x => g x - ∫ y, g y ∂γ with hX_def
  have hexp : ∀ s : ℝ, Integrable (fun x => exp (s * X x)) γ :=
    integrable_exp_mul_sub_of_lipschitzWith hgL _
  have hmean : γ[X] = 0 := by
    simp only [hX_def]
    rw [integral_sub (integrable_of_lipschitzWith hgL) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hgrad : ∀ x, ‖fderiv ℝ X x‖ ≤ L := by
    intro x
    simp only [hX_def, fderiv_sub_const]
    exact norm_fderiv_le_of_lipschitz ℝ hgL
  have hcgf := cgf_le_of_mul_deriv_cgf_sub_cgf_le hexp hmean
    (mul_deriv_cgf_sub_cgf_le (hg.sub contDiff_const) hgrad hexp) t
  rw [← exp_cgf (hexp t)]
  exact exp_le_exp.mpr hcgf

/-! ### Smoothing -/

/-- A Lipschitz function is uniformly approximated by smooth functions with the same Lipschitz
constant: convolve it with a normed bump function supported in a small ball. -/
private lemma exists_contDiff_lipschitzWith_abs_sub_le {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧ ∀ x, |g x - f x| ≤ δ := by
  set μ : Measure E := Measure.addHaar
  set ε : ℝ := δ / (L + 1) with hε_def
  have hε : 0 < ε := by positivity
  let φ : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hfc : Continuous f := hf.continuous
  refine ⟨φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f,
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (hfc.locallyIntegrable (μ := μ)), ?_, fun x => ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have hix : ∀ z, Integrable (fun s => φ.normed μ s * f (z - s)) μ := fun z =>
      (φ.continuous_normed.mul (hfc.comp (continuous_const.sub continuous_id)))
        |>.integrable_of_hasCompactSupport φ.hasCompactSupport_normed.mul_right
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.dist_eq]
    rw [← integral_sub (hix x) (hix y), ← Real.norm_eq_abs]
    calc ‖∫ s, (φ.normed μ s * f (x - s) - φ.normed μ s * f (y - s)) ∂μ‖
        ≤ ∫ s, φ.normed μ s * (L * dist x y) ∂μ := by
          refine norm_integral_le_of_norm_le ((φ.integrable_normed (μ := μ)).mul_const _)
            (ae_of_all _ fun s => ?_)
          rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed s)]
          gcongr
          · exact φ.nonneg_normed s
          · have := hf.dist_le_mul (x - s) (y - s)
            rwa [dist_sub_right, Real.dist_eq, ← Real.norm_eq_abs] at this
      _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]
  · have h := φ.dist_normed_convolution_le (μ := μ) (x₀ := x) (ε := L * ε)
      hfc.aestronglyMeasurable fun y hy => by
        have := hf.dist_le_mul y x
        exact this.trans (by gcongr; exact (Metric.mem_ball.mp hy).le)
    rw [Real.dist_eq] at h
    refine h.trans ?_
    rw [hε_def, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith

/-! ### Lipschitz functions -/

/-- **Gaussian concentration of Lipschitz functions**, in moment generating function form: an
`L`-Lipschitz function of a standard Gaussian vector, once centred, is sub-Gaussian with
variance proxy `L²`. -/
private lemma hasSubgaussianMGF_sub_integral_of_lipschitzWith {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂stdGaussian E) (L ^ 2) (stdGaussian E) := by
  set γ := stdGaussian E
  refine ⟨integrable_exp_mul_sub_of_lipschitzWith hf _, fun t => ?_⟩
  have key : ∀ δ : ℝ, 0 < δ → mgf (fun x => f x - ∫ y, f y ∂γ) γ t ≤
      exp (2 * |t| * δ) * exp ((L : ℝ) ^ 2 * t ^ 2 / 2) := by
    intro δ hδ
    obtain ⟨g, hg, hgL, hgf⟩ := exists_contDiff_lipschitzWith_abs_sub_le hf hδ
    have hint : |∫ y, g y ∂γ - ∫ y, f y ∂γ| ≤ δ := by
      rw [← integral_sub (integrable_of_lipschitzWith hgL) (integrable_of_lipschitzWith hf),
        ← Real.norm_eq_abs]
      have h := norm_integral_le_of_norm_le_const (μ := γ) (C := δ)
        (f := fun x => g x - f x) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgf x)
      rwa [probReal_univ, mul_one] at h
    have hpt : ∀ x, exp (t * (f x - ∫ y, f y ∂γ)) ≤
        exp (2 * |t| * δ) * exp (t * (g x - ∫ y, g y ∂γ)) := by
      intro x
      rw [← exp_add]
      refine exp_le_exp.mpr ?_
      have h1 : |(f x - ∫ y, f y ∂γ) - (g x - ∫ y, g y ∂γ)| ≤ 2 * δ := by
        calc |(f x - ∫ y, f y ∂γ) - (g x - ∫ y, g y ∂γ)|
            = |(∫ y, g y ∂γ - ∫ y, f y ∂γ) - (g x - f x)| := by ring_nf
          _ ≤ |∫ y, g y ∂γ - ∫ y, f y ∂γ| + |g x - f x| := abs_sub _ _
          _ ≤ 2 * δ := by linarith [hgf x]
      have h2 : t * ((f x - ∫ y, f y ∂γ) - (g x - ∫ y, g y ∂γ)) ≤ |t| * (2 * δ) := by
        calc t * ((f x - ∫ y, f y ∂γ) - (g x - ∫ y, g y ∂γ))
            ≤ |t * ((f x - ∫ y, f y ∂γ) - (g x - ∫ y, g y ∂γ))| := le_abs_self _
          _ = |t| * |(f x - ∫ y, f y ∂γ) - (g x - ∫ y, g y ∂γ)| := abs_mul _ _
          _ ≤ |t| * (2 * δ) := by gcongr
      nlinarith
    calc mgf (fun x => f x - ∫ y, f y ∂γ) γ t
        ≤ ∫ x, exp (2 * |t| * δ) * exp (t * (g x - ∫ y, g y ∂γ)) ∂γ :=
          integral_mono (integrable_exp_mul_sub_of_lipschitzWith hf _ t)
            ((integrable_exp_mul_sub_of_lipschitzWith hgL _ t).const_mul _) hpt
      _ = exp (2 * |t| * δ) * mgf (fun x => g x - ∫ y, g y ∂γ) γ t := integral_const_mul _ _
      _ ≤ exp (2 * |t| * δ) * exp ((L : ℝ) ^ 2 * t ^ 2 / 2) := by
          gcongr
          exact mgf_sub_integral_le_of_contDiff hg hgL t
  have hlim : Tendsto (fun δ : ℝ => exp (2 * |t| * δ) * exp ((L : ℝ) ^ 2 * t ^ 2 / 2))
      (𝓝[>] 0) (𝓝 (exp ((L : ℝ) ^ 2 * t ^ 2 / 2))) := by
    have hc : Continuous (fun δ : ℝ => exp (2 * |t| * δ) * exp ((L : ℝ) ^ 2 * t ^ 2 / 2)) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
  simpa [NNReal.coe_pow] using h

end Gaussian

/-! ### Concentration of Lipschitz functions of a standard Gaussian vector -/

/-- **Concentration of Lipschitz functions of Gaussian variables** (Wainwright,
*High-Dimensional Statistics*, 2019, §2.3; R. Vershynin, arXiv:1011.3027, Proposition 5.34 for the
one-sided tail). Let `X` be a standard Gaussian vector in
`ℝⁿ` and `f : ℝⁿ → ℝ` be `L`-Lipschitz for the Euclidean norm. Then `f(X) - E[f(X)]` is
sub-Gaussian with parameter `L` (variance proxy `L²`), and hence
`P(|f(X) - E[f(X)]| ≥ t) ≤ 2 exp (-t² / (2 L²))` for every `t ≥ 0`. -/
theorem lipschitz_concentration_stdGaussian {n : ℕ} {L : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))) (L ^ 2)
        (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      ∀ t : ℝ, 0 ≤ t →
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real
            {x | t ≤ |f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))|} ≤
          2 * exp (-t ^ 2 / (2 * L ^ 2)) := by
  have h := hasSubgaussianMGF_sub_integral_of_lipschitzWith hf
  refine ⟨h, fun t ht => ?_⟩
  set γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  set X : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x - ∫ y, f y ∂γ
  have hset : {x | t ≤ |X x|} = {x | t ≤ X x} ∪ {x | t ≤ (-X) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, le_abs]
  have h1 := h.measure_ge_le ht
  have h2 := h.neg.measure_ge_le ht
  push_cast at h1 h2
  calc γ.real {x | t ≤ |X x|} ≤ γ.real {x | t ≤ X x} + γ.real {x | t ≤ (-X) x} := by
        rw [hset]; exact measureReal_union_le _ _
    _ ≤ exp (-t ^ 2 / (2 * L ^ 2)) + exp (-t ^ 2 / (2 * L ^ 2)) := add_le_add h1 h2
    _ = 2 * exp (-t ^ 2 / (2 * L ^ 2)) := by ring

end MathlibExt.Probability.HighDimensionalStatisticsWanted
