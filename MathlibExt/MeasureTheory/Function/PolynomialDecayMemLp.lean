/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace MathlibExt.MeasureTheory.Function.PolynomialDecay

/-!
# Polynomial decay implies `L^p` membership on `ℝ`

If `‖f x‖ ≤ C * (1 + |x|) ^ (-q)` almost everywhere for some `C ≥ 0` and
`q > 1`, then `f` belongs to `L^p (ℝ)` for every `1 ≤ p ≤ ∞`. The proof
estimates `‖f‖ₚ ^ p` by a constant multiple
of `∫ (1 + ‖x‖) ^ (-(q * p))`, which is integrable by `integrable_one_add_norm`
since `1 < q ≤ q * p` for `p ≥ 1`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/LpSpaces.lean`,
`LpSpaces.memLp_of_polynomial_decay` (Corollary, April 6, 2021 section).
The a.e. version restores the bound stated in the source's prose; the
pointwise version remains available as a corollary.
-/

/-- **Polynomial decay implies $L^p$ membership.** Let $E$ be a normed additive commutative group
and let $f : \mathbb{R} \to E$ be almost everywhere strongly measurable. Suppose there are real
numbers $C \ge 0$ and $q > 1$ such that $\|f(x)\| \le C (1 + |x|)^{-q}$ for almost every
$x \in \mathbb{R}$. Then $f \in L^p(\mathbb{R})$, with respect to Lebesgue measure, for every
$p \in [1, \infty]$. -/
theorem memLp_of_polynomial_decay_ae
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_meas : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) {q : ℝ} (hq : 1 < q)
    (hbound : ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ C * (1 + |x|) ^ (-q))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp f p volume := by
  by_cases hp_top : p = ⊤
  · subst hp_top
    apply memLp_top_of_bound hf_meas C
    filter_upwards [hbound] with x hx
    calc ‖f x‖ ≤ C * (1 + |x|) ^ (-q) := hx
      _ ≤ C * 1 := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.rpow_le_one_of_one_le_of_nonpos
          · linarith [abs_nonneg x]
          · linarith
      _ = C := mul_one C
  · have hp_ne_zero : p ≠ 0 := by positivity
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
    have hp_ge_one : (1 : ℝ) ≤ p.toReal := by
      have : (1 : ℝ≥0∞).toReal ≤ p.toReal :=
        (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
      simpa using this
    have hqp : (Module.finrank ℝ ℝ : ℝ) < q * p.toReal := by
      simp [Module.finrank_self]
      calc (1 : ℝ) < q := hq
        _ = q * 1 := (mul_one q).symm
        _ ≤ q * p.toReal := mul_le_mul_of_nonneg_left hp_ge_one (by linarith)
    have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(q * p.toReal))) volume :=
      integrable_one_add_norm hqp
    show eLpNorm f p volume < ⊤
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_top hf_meas]
    calc ∫⁻ (x : ℝ), ‖f x‖ₑ ^ p.toReal ∂volume
        ≤ ∫⁻ (x : ℝ), ENNReal.ofReal
            (C ^ p.toReal * (1 + ‖x‖) ^ (-(q * p.toReal))) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [hbound] with x hx
          rw [(ofReal_norm (f x)).symm,
              ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp_pos.le]
          apply ENNReal.ofReal_le_ofReal
          have hbound' : ‖f x‖ ≤ C * (1 + ‖x‖) ^ (-q) := by
            have := hx
            rwa [show |x| = ‖x‖ from (Real.norm_eq_abs x).symm] at this
          calc ‖f x‖ ^ p.toReal
              ≤ (C * (1 + ‖x‖) ^ (-q)) ^ p.toReal :=
                Real.rpow_le_rpow (norm_nonneg _) hbound' hp_pos.le
            _ = C ^ p.toReal * ((1 + ‖x‖) ^ (-q)) ^ p.toReal :=
                Real.mul_rpow hC (Real.rpow_nonneg (by positivity) _)
            _ = C ^ p.toReal * (1 + ‖x‖) ^ (-(q * p.toReal)) := by
                congr 1
                rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖x‖)]
                ring_nf
      _ < ⊤ := by
          simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hC _)]
          rw [lintegral_const_mul _ (by measurability)]
          apply ENNReal.mul_lt_top
          · exact ENNReal.ofReal_lt_top
          · rw [← lintegral_enorm_of_nonneg (fun x => Real.rpow_nonneg (by positivity) _)]
            exact hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral

/-- **Pointwise polynomial decay implies $L^p$ membership.** Let $E$ be a normed additive
commutative group and let $f : \mathbb{R} \to E$ be almost everywhere strongly measurable. Suppose
there are real numbers $C \ge 0$ and $q > 1$ such that $\|f(x)\| \le C (1 + |x|)^{-q}$ for every
$x \in \mathbb{R}$. Then $f \in L^p(\mathbb{R})$, with respect to Lebesgue measure, for every
$p \in [1, \infty]$. -/
theorem memLp_of_polynomial_decay
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf_meas : AEStronglyMeasurable f volume)
    {C : ℝ} (hC : 0 ≤ C) {q : ℝ} (hq : 1 < q)
    (hbound : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-q))
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemLp f p volume :=
  memLp_of_polynomial_decay_ae hf_meas hC hq
    (Filter.Eventually.of_forall hbound) hp

end MathlibExt.MeasureTheory.Function.PolynomialDecay
