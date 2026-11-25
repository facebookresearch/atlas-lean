/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.HoeffdingBounded

/-!
# Random Fourier features

For a probability measure `p` on a real inner product space (the Fourier transform of a
shift-invariant kernel, by Bochner's theorem), the random feature
`z_{ω,b}(x) = √2 cos(⟪ω, x⟫ + b)`, with `ω ~ p` and `b` uniform on `[0, 2π]` independent, satisfies
`E[z_{ω,b}(x) z_{ω,b}(y)] = Re φ_p(x - y)`, where `φ_p` is the characteristic function of `p`
(A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007, Section 2,
equation (2) and the cosine features that follow it). When the kernel `k(Δ) = φ_p(Δ)` is real,
this is `k(x - y)`: the random features give an unbiased estimate of the kernel. Averaging `D`
independent features, the estimate concentrates: Hoeffding's inequality applied to the products
gives the tail bound `2 exp(-D ε² / 8)`, a weaker constant than the source's `2 exp(-D ε² / 4)`.

## Main definitions

- `fourierFeature ω b x`: the random feature `√2 cos(⟪ω, x⟫ + b)`.
- `phaseMeasure`: the uniform law of the phase `b` on `(0, 2π]`.

## Main results

- `phase_average_fourierFeature_mul`: averaging over the phase gives `cos ⟪ω, x - y⟫`.
- `integral_fourierFeature_mul`: unbiasedness, `E[z(x) z(y)] = Re φ_p(x - y)`.
- `integral_avg_fourierFeature_mul`: the same for the average of `D` independent features.
- `measureReal_abs_avg_fourierFeature_mul_sub_ge_le`: the pointwise Hoeffding bound
  `P(|(1/D) ∑ⱼ z_j(x) z_j(y) - Re φ_p(x - y)| ≥ ε) ≤ 2 exp(-D ε² / 8)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped InnerProductSpace

namespace CSLibExt.MachineLearning.RandomFeatures

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Random Fourier feature.** The feature `z_{ω,b}(x) = √2 cos(⟪ω, x⟫ + b)` of the input `x`,
for a frequency `ω` and a phase `b`.

Source: A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007,
Section 2 (the real-valued mapping `z_ω(x) = √2 cos(ω'x + b)` after equation (2)). -/
noncomputable def fourierFeature (ω : E) (b : ℝ) (x : E) : ℝ :=
  √2 * Real.cos (⟪ω, x⟫_ℝ + b)

/-- **Uniform phase.** The uniform probability measure on `(0, 2π]`, the law of the phase `b` of a
random Fourier feature.

Source: A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007,
Section 2 (`b` drawn uniformly from `[0, 2π]`; the endpoint is a null set). -/
noncomputable def phaseMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Set.Ioc 0 (2 * π))

instance : IsProbabilityMeasure phaseMeasure := by
  constructor
  have h : (0 : ℝ) < 2 * π := by positivity
  simp only [phaseMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using h) ENNReal.ofReal_ne_top

private theorem intervalIntegral_cos_two_mul_add (c : ℝ) :
    ∫ b in (0 : ℝ)..2 * π, Real.cos (2 * b + c) = 0 := by
  rw [intervalIntegral.integral_comp_mul_add (fun t => Real.cos t) two_ne_zero c, integral_cos]
  have : 2 * (2 * π) + c = c + ((2 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
  rw [this, Real.sin_add_int_mul_two_pi]
  simp

private theorem fourierFeature_mul (ω : E) (b : ℝ) (x y : E) :
    fourierFeature ω b x * fourierFeature ω b y =
      Real.cos (⟪ω, x⟫_ℝ - ⟪ω, y⟫_ℝ) + Real.cos (2 * b + (⟪ω, x⟫_ℝ + ⟪ω, y⟫_ℝ)) := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  set u := ⟪ω, x⟫_ℝ + b
  set v := ⟪ω, y⟫_ℝ + b
  have e1 : ⟪ω, x⟫_ℝ - ⟪ω, y⟫_ℝ = u - v := by simp only [u, v]; ring
  have e2 : 2 * b + (⟪ω, x⟫_ℝ + ⟪ω, y⟫_ℝ) = u + v := by simp only [u, v]; ring
  have hs := Real.cos_sub u v
  have ha := Real.cos_add u v
  have hf : fourierFeature ω b x * fourierFeature ω b y =
      (√2 * √2) * (Real.cos u * Real.cos v) := by
    simp only [fourierFeature, u, v]; ring
  rw [e1, e2, hf, h2, hs, ha]
  ring

/-- **Averaging a random Fourier feature over the phase.** For every frequency `ω` and inputs
`x, y`, `(1 / 2π) ∫₀^{2π} z_{ω,b}(x) z_{ω,b}(y) db = cos ⟪ω, x - y⟫`.

Source: A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007,
Section 2 ("a consequence of the sum of angles formula"). -/
theorem phase_average_fourierFeature_mul (ω x y : E) :
    (2 * π)⁻¹ * ∫ b in (0 : ℝ)..2 * π, fourierFeature ω b x * fourierFeature ω b y =
      Real.cos ⟪ω, x - y⟫_ℝ := by
  simp_rw [fourierFeature_mul]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun b : ℝ =>
      Real.cos (2 * b + (⟪ω, x⟫_ℝ + ⟪ω, y⟫_ℝ))).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral_cos_two_mul_add, inner_sub_right]
  have : (0 : ℝ) < 2 * π := by positivity
  simp only [sub_zero, smul_eq_mul, add_zero]
  field_simp

private theorem integral_phase (ω x y : E) :
    ∫ b, fourierFeature ω b x * fourierFeature ω b y ∂phaseMeasure = Real.cos ⟪ω, x - y⟫_ℝ := by
  rw [← phase_average_fourierFeature_mul, phaseMeasure, integral_smul_measure,
    intervalIntegral.integral_of_le (by positivity), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

private theorem continuous_fourierFeature_mul (x y : E) :
    Continuous fun q : E × ℝ => fourierFeature q.1 q.2 x * fourierFeature q.1 q.2 y := by
  unfold fourierFeature
  fun_prop

private theorem abs_fourierFeature_mul_le (ω : E) (b : ℝ) (x y : E) :
    |fourierFeature ω b x * fourierFeature ω b y| ≤ 2 := by
  rw [fourierFeature_mul]
  calc |Real.cos (⟪ω, x⟫_ℝ - ⟪ω, y⟫_ℝ) + Real.cos (2 * b + (⟪ω, x⟫_ℝ + ⟪ω, y⟫_ℝ))|
      ≤ |Real.cos (⟪ω, x⟫_ℝ - ⟪ω, y⟫_ℝ)| + |Real.cos (2 * b + (⟪ω, x⟫_ℝ + ⟪ω, y⟫_ℝ))| :=
        abs_add_le _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
    _ = 2 := by norm_num

variable [MeasurableSpace E] [BorelSpace E]

/-- **Random Fourier features are unbiased.** Let `p` be a probability measure on a real inner
product space, and let `ω ~ p` and `b` uniform on `[0, 2π]` be independent. Then for all inputs
`x, y`, `E[z_{ω,b}(x) z_{ω,b}(y)] = Re φ_p(x - y)`, where `φ_p = charFun p` is the characteristic
function `φ_p(Δ) = ∫ exp(i ⟪ω, Δ⟫) dp(ω)`. In particular, for a shift-invariant kernel
`k(x, y) = φ_p(x - y)` that is real-valued, `E[z(x) z(y)] = k(x, y)`.

Source: A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007,
Section 2, equation (2) and the real-valued features that follow it (there `p` is the Fourier
transform of a real, properly scaled positive-definite kernel, given by Bochner's theorem,
Theorem 1). -/
theorem integral_fourierFeature_mul (p : Measure E) [IsProbabilityMeasure p] (x y : E) :
    ∫ q, fourierFeature q.1 q.2 x * fourierFeature q.1 q.2 y ∂(p.prod phaseMeasure) =
      (charFun p (x - y)).re := by
  have hint : Integrable (fun q : E × ℝ => fourierFeature q.1 q.2 x * fourierFeature q.1 q.2 y)
      (p.prod phaseMeasure) :=
    Integrable.of_bound (continuous_fourierFeature_mul x y).aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun q => by
        simpa [Real.norm_eq_abs] using abs_fourierFeature_mul_le q.1 q.2 x y)
  rw [integral_prod _ hint]
  simp_rw [integral_phase]
  have hc : Integrable (fun ω : E => Complex.exp (⟪ω, x - y⟫_ℝ * Complex.I)) p :=
    Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun ω => by
      rw [Complex.norm_exp_ofReal_mul_I])
  rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re hc]
  simp [Complex.exp_ofReal_mul_I_re]

/-- **Averaging `D` random Fourier features is unbiased.** With `D` independent pairs
`(ωⱼ, bⱼ) ~ p ⊗ U[0, 2π]` and the normalized feature map `z(x) = D^{-1/2} (z_{ωⱼ,bⱼ}(x))ⱼ`, the
estimate `z(x)'z(y) = (1/D) ∑ⱼ z_{ωⱼ,bⱼ}(x) z_{ωⱼ,bⱼ}(y)` has expectation `Re φ_p(x - y)`.

Source: A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007,
Section 2 (the `D`-dimensional map of Algorithm 1 and the sample average after equation (2)). -/
theorem integral_avg_fourierFeature_mul (p : Measure E) [IsProbabilityMeasure p] (D : ℕ)
    (hD : 0 < D) (x y : E) :
    ∫ θ, (1 / D : ℝ) * ∑ j, fourierFeature (θ j).1 (θ j).2 x * fourierFeature (θ j).1 (θ j).2 y
        ∂(Measure.pi fun _ : Fin D => p.prod phaseMeasure) = (charFun p (x - y)).re := by
  have hcont := continuous_fourierFeature_mul (E := E) x y
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_comp_eval (μ := fun _ : Fin D => p.prod phaseMeasure)
      (f := fun q : E × ℝ => fourierFeature q.1 q.2 x * fourierFeature q.1 q.2 y)
      hcont.aestronglyMeasurable, integral_fourierFeature_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    field_simp
  · intro j _
    exact Integrable.of_bound ((hcont.measurable.comp (measurable_pi_apply j)).aestronglyMeasurable)
      2
      (Filter.Eventually.of_forall fun θ => by
        simpa [Real.norm_eq_abs] using abs_fourierFeature_mul_le (θ j).1 (θ j).2 x y)

/-- **Concentration of random Fourier features at a pair of points.** With `D ≥ 1` independent
pairs `(ωⱼ, bⱼ) ~ p ⊗ U[0, 2π]`, for all inputs `x, y` and every `ε ≥ 0`,
`P(|(1/D) ∑ⱼ z_{ωⱼ,bⱼ}(x) z_{ωⱼ,bⱼ}(y) - Re φ_p(x - y)| ≥ ε) ≤ 2 exp(-D ε² / 8)`.

Source: A. Rahimi and B. Recht, *Random features for large-scale kernel machines*, NIPS 2007,
Section 2 (the Hoeffding bound before Claim 1). The source states the sharper exponent
`-D ε² / 4`; the bound proved here is Hoeffding's inequality applied to the products
`z_ω(x) z_ω(y)`, which lie in `[-2, 2]`, and has the weaker exponent `-D ε² / 8`. -/
theorem measureReal_abs_avg_fourierFeature_mul_sub_ge_le (p : Measure E) [IsProbabilityMeasure p]
    (D : ℕ) (hD : 0 < D) (x y : E) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin D => p.prod phaseMeasure).real
        {θ | ε ≤ |(1 / D : ℝ) * ∑ j, fourierFeature (θ j).1 (θ j).2 x *
          fourierFeature (θ j).1 (θ j).2 y - (charFun p (x - y)).re|} ≤
      2 * Real.exp (-(D * ε ^ 2) / 8) := by
  set μ := Measure.pi fun _ : Fin D => p.prod phaseMeasure
  have hcont := continuous_fourierFeature_mul (E := E) x y
  set g : E × ℝ → ℝ := fun q => fourierFeature q.1 q.2 x * fourierFeature q.1 q.2 y
  have hindep : iIndepFun (fun (j : Fin D) (θ : Fin D → E × ℝ) => g (θ j)) μ :=
    iIndepFun_pi (X := fun _ => g) fun _ => hcont.aemeasurable
  have hmeas : ∀ j : Fin D, AEMeasurable (fun θ : Fin D → E × ℝ => g (θ j)) μ := fun j =>
    (hcont.measurable.comp (measurable_pi_apply j)).aemeasurable
  have hbd : ∀ j : Fin D, ∀ᵐ θ ∂μ, g (θ j) ∈ Set.Icc (-2 : ℝ) 2 := fun j =>
    Filter.Eventually.of_forall fun θ => abs_le.mp (abs_fourierFeature_mul_le (θ j).1 (θ j).2 x y)
  have h := MathlibExt.Probability.HoeffdingBounded.measureReal_abs_avg_sub_ge_le hindep hmeas
    hbd hε
  have hmean : ∀ j : Fin D, μ[fun θ : Fin D → E × ℝ => g (θ j)] = (charFun p (x - y)).re :=
    fun j => by
      rw [integral_comp_eval (μ := fun _ : Fin D => p.prod phaseMeasure) (f := g)
        hcont.aestronglyMeasurable]
      exact integral_fourierFeature_mul p x y
  have havg : (1 / D : ℝ) * ∑ j : Fin D, μ[fun θ : Fin D → E × ℝ => g (θ j)] =
      (charFun p (x - y)).re := by
    simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    field_simp
  rw [havg] at h
  refine h.trans_eq ?_
  congr 2
  norm_num
  ring

end CSLibExt.MachineLearning.RandomFeatures
