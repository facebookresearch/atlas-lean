/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Auerbach's Hölder condition problem

At exponent `1/2`, the function `√x * cos (π / x)` refutes Auerbach's claim.
Its square-root envelope controls increments from zero, and it is differentiable elsewhere.
Its values at consecutive reciprocal integers violate every uniform Hölder bound on `[0, 1]`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ScottishBook83Wanted

/-- Auerbach's Problem 83 from the Scottish Book: if a continuous
function `f` satisfies, at every point `x`, that the difference
quotients `|f (x + h) - f x| / |h| ^ a` stay below a constant `M` for
all sufficiently small nonzero `h` — that is, if the limsup of the
quotients as `h → 0` is `< M`, with `0 < a < 1` — does `f` then satisfy
a Hölder condition of exponent `a` on `[0, 1]`? The conclusion is on a
compact interval: on all of `ℝ`, `f = id` already fails it. -/
def ScottishBookProblem83Claim : Prop :=
  ∀ (a M : ℝ), 0 < a → a < 1 → 0 < M → ∀ f : ℝ → ℝ,
    Continuous f →
    (∀ x : ℝ, ∃ M' : ℝ, M' < M ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ,
      0 < |h| → |h| < δ →
      |f (x + h) - f x| / Real.rpow |h| a ≤ M') →
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |f x - f y| ≤ C * Real.rpow |x - y| a

open Filter Real
open scoped Topology

private noncomputable def oscillation (x : ℝ) : ℝ := √x * cos (π / x)

private lemma abs_oscillation_le (x : ℝ) : |oscillation x| ≤ √|x| := by
  calc
    |oscillation x| = √x * |cos (π / x)| := by
      rw [oscillation, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
    _ ≤ √x * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one _) (sqrt_nonneg _)
    _ ≤ √|x| := by simpa using sqrt_le_sqrt (le_abs_self x)

private lemma differentiableAt_oscillation {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ oscillation x := by
  unfold oscillation
  fun_prop (disch := assumption)

private lemma continuous_oscillation : Continuous oscillation := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain rfl | hx := eq_or_ne x 0
  · apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨ε ^ 2, sq_pos_of_pos hε, fun {y} hy ↦ ?_⟩
    simp only [Real.dist_eq, sub_zero] at hy
    have hzero : oscillation 0 = 0 := by simp [oscillation]
    rw [Real.dist_eq, hzero, sub_zero]
    exact (abs_oscillation_le y).trans_lt ((sqrt_lt (abs_nonneg _) hε.le).2 hy)
  · exact (differentiableAt_oscillation hx).continuousAt

-- Off the origin, the ordinary difference quotient tends to the derivative. Multiplying
-- its absolute value by `√|h|` shows that the half-order quotient tends to zero.
private lemma local_bound (x : ℝ) : ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ →
    |oscillation (x + h) - oscillation x| / √|h| ≤ 1 := by
  obtain rfl | hx := eq_or_ne x 0
  · refine ⟨1, zero_lt_one, fun h hh _ ↦ ?_⟩
    simpa [oscillation, div_le_one₀ (sqrt_pos.2 hh)] using abs_oscillation_le h
  have hs := (differentiableAt_oscillation hx).hasDerivAt.tendsto_slope_zero.abs
  have hr : Tendsto (fun h : ℝ ↦ √|h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa [Function.comp_def] using
      ((continuous_sqrt.comp continuous_abs).tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun h : ℝ ↦ |oscillation (x + h) - oscillation x| / √|h|)
      (𝓝[≠] 0) (𝓝 0) := by
    convert hs.mul hr using 1
    · ext h
      simp only [smul_eq_mul, abs_mul, abs_inv]
      rw [div_eq_mul_inv, ← sqrt_div_self]
      ring
    · simp
  obtain ⟨δ, hδ, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim 1 zero_lt_one
  refine ⟨δ, hδ, fun h hh hδh ↦ ?_⟩
  have := hb (x := h) (by simpa using abs_pos.mp hh) (by simpa [Real.dist_eq] using hδh)
  simpa only [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (sqrt_nonneg _))] using this.le

private lemma no_uniform_bound (C : ℝ)
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |oscillation x - oscillation y| ≤ C * √|x - y|) : False := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C ^ 2 + 1)
  let k : ℝ := 2 * n
  have hk : 1 ≤ k := by dsimp [k]; linarith [sq_nonneg C]
  have hkpos : 0 < k := by linarith
  have hkp : 0 < k + 1 := by linarith
  have hmem {t : ℝ} (ht : 1 ≤ t) : t⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ ht⟩
  -- The cosine takes opposite signs at the two ends of this gap.
  have hb := hC k⁻¹ (hmem hk) (k + 1)⁻¹ (hmem (by linarith))
  have hpeak : oscillation k⁻¹ = √k⁻¹ := by
    rw [oscillation, div_inv_eq_mul, show π * k = n * (2 * π) by dsimp [k]; ring,
      cos_nat_mul_two_pi, mul_one]
  have htrough : oscillation (k + 1)⁻¹ = -√(k + 1)⁻¹ := by
    rw [oscillation, div_inv_eq_mul,
      show π * (k + 1) = n * (2 * π) + π by dsimp [k]; ring,
      cos_nat_mul_two_pi_add_pi, mul_neg_one]
  have hgap : k⁻¹ - (k + 1)⁻¹ = k⁻¹ / (k + 1) := by
    field_simp
    ring
  rw [hpeak, htrough, sub_neg_eq_add, abs_of_nonneg (by positivity), hgap,
    abs_of_nonneg (by positivity), sqrt_div (inv_nonneg.mpr hkpos.le), ← mul_div_assoc] at hb
  -- Even the positive peak alone forces the Hölder constant to be at least `√(k + 1)`.
  have hsmall : √k⁻¹ ≤ C * √k⁻¹ / √(k + 1) := by linarith [sqrt_nonneg (k + 1)⁻¹]
  have hle := (le_div_iff₀ (sqrt_pos.2 hkp)).mp hsmall
  have hC' : √(k + 1) ≤ C := by
    exact le_of_mul_le_mul_left (by simpa only [mul_comm C] using hle) (by positivity : 0 < √k⁻¹)
  exact (lt_sqrt_of_sq_lt (by dsimp [k]; linarith [sq_nonneg C])).not_ge hC'

/--
Auerbach's Problem 83 is false: the pointwise limsup condition does
not imply a Hölder condition. Source: H. Auerbach, Problem 83 of the
Scottish Book; typescript Ad 83 records the negative answer, with
Marcinkiewicz's counterexample: a triangular function on intervals
`1 / n - xₙ`, `1 / n + xₙ` with height `1 / n` and suitably small
half-widths `xₙ`, whose difference quotients are small near every
point but which is not globally Hölder.
-/
theorem auerbach83_refuted : ¬ ScottishBookProblem83Claim := by
  intro claim
  obtain ⟨C, hC⟩ := claim (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
    oscillation continuous_oscillation (fun x ↦ ⟨1, by norm_num, by
      simpa only [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using local_bound x⟩)
  exact no_uniform_bound C (by simpa only [Real.sqrt_eq_rpow, Real.rpow_eq_pow] using hC)

end MathlibExt.Analysis.Calculus.ScottishBook83Wanted
