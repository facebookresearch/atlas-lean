/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Azuma's inequality

A martingale `Z₀, …, Zₙ` whose increments are bounded, `|Zᵢ - Zᵢ₋₁| ≤ cᵢ`, satisfies the
Gaussian tail bound `P(Zₙ - Z₀ ≥ a) ≤ exp(-a² / (2 ∑ cᵢ²))`.

## Main results

* `ProbabilityTheory.condExp_exp_mul_le_of_abs_le`: the conditional Hoeffding lemma in symmetric
  form. If `m` is a sub-σ-algebra, `|X| ≤ c` almost everywhere and `μ[X | m] = 0`, then
  `μ[exp (t * X) | m] ≤ exp (c ^ 2 * t ^ 2 / 2)` almost everywhere, on any measurable space.
* `ProbabilityTheory.hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero`: the conditional
  Hoeffding lemma in Mathlib's language. On a standard Borel space, if `X ∈ [a, b]` almost
  everywhere and `μ[X | m] = 0`, then `X` is conditionally sub-Gaussian given `m` with parameter
  `((b - a) / 2) ^ 2`, as `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` needs.
* `MeasureTheory.Martingale.hasSubgaussianMGF_sub_of_abs_sub_le`: if a martingale `Z` satisfies
  `|Zᵢ - Zᵢ₋₁| ≤ cᵢ` almost everywhere for `1 ≤ i ≤ n`, then `Zₙ - Z₀` has a sub-Gaussian
  moment-generating function with parameter `∑_{i=1}^n cᵢ²`.
* `MathlibExt.Probability.AzumaInequalityWanted.azuma_inequality`: Azuma's inequality
  (K. Azuma, 1967; Y. Zhao, *The Probabilistic Method in Combinatorics*, Theorem 8.6).

## Proof outline

The proof is the one of Y. Zhao's notes (Theorem 8.6 and Lemma 8.7), with conditional expectations
given the filtration.

* For `|x| ≤ c`, convexity of `exp` on the segment `[-c, c]` gives
  `exp (t * x) ≤ cosh (t * c) + x * sinh (t * c) / c` (Mathlib's
  `Real.exp_mul_le_cosh_add_mul_sinh`). Taking conditional expectations and using
  `μ[X | m] = 0` gives `μ[exp (t * X) | m] ≤ cosh (t * c) ≤ exp (c ^ 2 * t ^ 2 / 2)`.
* Write `Zₙ₊₁ - Z₀ = (Zₙ - Z₀) + Dₙ₊₁` with `Dₙ₊₁ = Zₙ₊₁ - Zₙ`. The martingale property gives
  `μ[Dₙ₊₁ | ℱₙ] = 0`, and `Zₙ - Z₀` is `ℱₙ`-measurable, so the tower property and the
  conditional Hoeffding lemma give
  `E[exp (t (Zₙ₊₁ - Z₀))] = E[exp (t (Zₙ - Z₀)) μ[exp (t Dₙ₊₁) | ℱₙ]]
    ≤ exp (cₙ₊₁ ^ 2 t ^ 2 / 2) E[exp (t (Zₙ - Z₀))]`.
  By induction, `Zₙ - Z₀` has a sub-Gaussian moment-generating function with parameter
  `∑_{i=1}^n cᵢ²`.
* The Chernoff bound for sub-Gaussian random variables (`HasSubgaussianMGF.measure_ge_le`) then
  gives Azuma's inequality. When `∑ cᵢ² = 0`, the bound reads `exp (-a² / 0) = exp 0 = 1` by
  Lean's convention `x / 0 = 0`.

## Implementation notes

Mathlib's conditionally sub-Gaussian random variables (`ProbabilityTheory.HasCondSubgaussianMGF`)
are defined through the conditional expectation kernel, which needs `StandardBorelSpace Ω`, and
Mathlib's Azuma-Hoeffding inequality `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`
is stated in those terms. Azuma's inequality below is stated on an arbitrary measurable space, so
its proof works with conditional expectations directly, through the symmetric conditional Hoeffding
lemma. The standard Borel form of the conditional Hoeffding lemma is provided as well; it is proved
from Mathlib's Hoeffding lemma `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
applied to the conditional expectation kernel.

`azuma_inequality` keeps the full name it had in the former wanted module, so its namespace still
reads `AzumaInequalityWanted`.

## References

* K. Azuma, *Weighted sums of certain dependent random variables*, Tôhoku Mathematical Journal
  19 (1967), 357–367.
* W. Hoeffding, *Probability inequalities for sums of bounded random variables*, Journal of the
  American Statistical Association 58 (1963), 13–30.
* Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019,
  Theorem 8.6 and Lemma 8.7 (https://yufeizhao.com/pm/sp19/pmnotes.pdf).
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- For `|x| ≤ c`, convexity of `exp` bounds `exp (t * x)` by the chord through `-c` and `c`:
this is `Real.exp_mul_le_cosh_add_mul_sinh` applied to `x / c` and `t * c`. -/
private lemma exp_mul_le_cosh_add_mul_sinh_div {c x : ℝ} (hx : |x| ≤ c) (t : ℝ) :
    exp (t * x) ≤ cosh (t * c) + sinh (t * c) / c * x := by
  rcases ((abs_nonneg x).trans hx).eq_or_lt with hc | hc
  · have hx0 : x = 0 := abs_nonpos_iff.mp (hc ▸ hx)
    simp [hx0, ← hc]
  have h := exp_mul_le_cosh_add_mul_sinh (t := x / c)
    (by rwa [abs_div, abs_of_pos hc, div_le_one hc]) (t * c)
  convert h using 2
  · field_simp
  · field_simp

/-- **Conditional Hoeffding lemma for symmetric bounds.** Let `μ` be a finite measure, `m` a
sub-σ-algebra and `X` an almost everywhere measurable real random variable with `|X| ≤ c` almost
everywhere, whose conditional expectation `μ[X | m]` given `m` vanishes almost everywhere. Then for
every real `t`, the conditional moment-generating function `μ[exp (t * X) | m]` is almost
everywhere at most `exp (c ^ 2 * t ^ 2 / 2)`. The space need not be standard Borel. -/
theorem condExp_exp_mul_le_of_abs_le [IsFiniteMeasure μ] (hm : m ≤ m0) {X : Ω → ℝ} {c : ℝ}
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ c) (hc : μ[X | m] =ᵐ[μ] 0) (t : ℝ) :
    μ[fun ω ↦ exp (t * X ω) | m] ≤ᵐ[μ] fun _ ↦ exp (c ^ 2 * t ^ 2 / 2) := by
  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (-c) c := hb.mono fun _ h ↦ abs_le.mp h
  have hXint : Integrable X μ := Integrable.of_mem_Icc (-c) c hX hIcc
  have hexp : Integrable (fun ω ↦ exp (t * X ω)) μ := integrable_exp_mul_of_mem_Icc hX hIcc
  set A := cosh (t * c)
  set B := sinh (t * c) / c
  have hlin_eq : (fun ω ↦ A + B * X ω) = (fun _ ↦ A) + B • X := rfl
  have hlin : Integrable (fun ω ↦ A + B * X ω) μ := by
    rw [hlin_eq]
    exact (integrable_const A).add (hXint.smul B)
  have h1 := condExp_mono (m := m) hexp hlin
    (hb.mono fun _ h ↦ exp_mul_le_cosh_add_mul_sinh_div h t)
  have h2 : μ[fun ω ↦ A + B * X ω | m] =ᵐ[μ] fun _ ↦ A := by
    rw [hlin_eq]
    filter_upwards [condExp_add (integrable_const A) (hXint.smul B) m, condExp_smul B X m, hc]
      with ω h h₁ h₂
    rw [h, Pi.add_apply, h₁, condExp_const hm]
    simp [h₂]
  filter_upwards [h1, h2] with ω h1 h2
  rw [h2] at h1
  refine h1.trans ((cosh_le_exp_half_sq _).trans_eq ?_)
  ring_nf

/-- **Conditional Hoeffding lemma.** Let `μ` be a finite measure on a standard Borel space and `m`
a sub-σ-algebra. If an almost everywhere measurable real random variable `X` takes values in
`[a, b]` almost everywhere and its conditional expectation `μ[X | m]` given `m` vanishes almost
everywhere, then `X` is conditionally sub-Gaussian given `m` with parameter `((b - a) / 2) ^ 2`:
`exp (t * X)` is integrable for every real `t`, and for almost every point with respect to the
restriction of `μ` to `m`, the moment-generating function of `X` under the conditional
distribution given `m` at that point is at most `exp ((b - a) ^ 2 * t ^ 2 / 8)` for every real
`t`. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] (hm : m ≤ m0) {X : Ω → ℝ} {a b : ℝ} (hX : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hc : μ[X | m] =ᵐ[μ] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) μ := by
  change Kernel.HasSubgaussianMGF X _ (condExpKernel μ m) (μ.trim hm)
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX hb
  have hb' : ∀ᵐ ω' ∂(μ.trim hm), ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω ∈ Set.Icc a b :=
    Measure.ae_ae_of_ae_comp (by rwa [condExpKernel_comp_trim hm])
  have hmk : ∀ᵐ ω' ∂(μ.trim hm), ∀ᵐ ω ∂(condExpKernel μ m ω'), X ω = hX.mk X ω :=
    Measure.ae_ae_of_ae_comp (by rw [condExpKernel_comp_trim hm]; exact hX.ae_eq_mk)
  have hint : ∀ᵐ ω' ∂(μ.trim hm), ∫ ω, X ω ∂(condExpKernel μ m ω') = 0 := by
    have h1 := condExp_ae_eq_trim_integral_condExpKernel hm (Integrable.of_mem_Icc a b hX hb)
    have h2 : μ[X | m] =ᵐ[μ.trim hm] 0 :=
      stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_const hc
    filter_upwards [h1, h2] with ω' h1 h2
    rw [← h1, h2, Pi.zero_apply]
  filter_upwards [hb', hmk, hint] with ω' hb' hmk hint
  exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    ⟨hX.mk X, hX.measurable_mk, hmk⟩ hb' hint).mgf_le

end ProbabilityTheory

namespace MeasureTheory.Martingale

open ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sub-Gaussian bound for martingales with bounded increments.** Let `Z₀, Z₁, …` be a real
martingale with respect to a filtration on a probability space, let `n` be a natural number and
suppose `|Zᵢ - Zᵢ₋₁| ≤ cᵢ` almost everywhere for `1 ≤ i ≤ n`. Then `Zₙ - Z₀` has a sub-Gaussian
moment-generating function with parameter `∑_{i=1}^n cᵢ²`: for every real `t`,
`exp (t (Zₙ - Z₀))` is integrable and `E[exp (t (Zₙ - Z₀))] ≤ exp ((∑_{i=1}^n cᵢ²) t² / 2)`. -/
theorem hasSubgaussianMGF_sub_of_abs_sub_le [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {Z : ℕ → Ω → ℝ} (hZ : Martingale Z ℱ μ) {n : ℕ} {c : ℕ → ℝ}
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂μ, |Z i ω - Z (i - 1) ω| ≤ c i) :
    HasSubgaussianMGF (fun ω ↦ Z n ω - Z 0 ω) (∑ i ∈ Finset.Icc 1 n, ‖c i‖₊ ^ 2) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih fun i hi ↦ hc i (Finset.Icc_subset_Icc_right n.le_succ hi)
    set D := Z (n + 1) - Z n with hD_def
    have hD : ∀ᵐ ω ∂μ, |D ω| ≤ c (n + 1) := by
      simpa [hD_def] using hc (n + 1) (Finset.right_mem_Icc.2 (Nat.le_add_left 1 n))
    have hDint : Integrable D μ := (hZ.integrable (n + 1)).sub (hZ.integrable n)
    have hDc : μ[D | ℱ n] =ᵐ[μ] 0 := by
      filter_upwards [condExp_sub (hZ.integrable (n + 1)) (hZ.integrable n) (ℱ n),
        hZ.condExp_ae_eq n.le_succ] with ω h h'
      rw [hD_def, h, condExp_of_stronglyMeasurable (ℱ.le n) (hZ.stronglyMeasurable n)
        (hZ.integrable n)]
      simp [h']
    have hcond := condExp_exp_mul_le_of_abs_le (ℱ.le n) hDint.aemeasurable hD hDc
    have hDbd (t : ℝ) : ∀ᵐ ω ∂μ, ‖exp (t * D ω)‖ ≤ exp (|t| * c (n + 1)) := by
      filter_upwards [hD] with ω hω
      rw [norm_of_nonneg (exp_pos _).le, exp_le_exp]
      calc t * D ω ≤ |t * D ω| := le_abs_self _
        _ = |t| * |D ω| := abs_mul _ _
        _ ≤ |t| * c (n + 1) := mul_le_mul_of_nonneg_left hω (abs_nonneg t)
    have hsplit (t : ℝ) : (fun ω ↦ exp (t * (Z (n + 1) ω - Z 0 ω))) =
        fun ω ↦ exp (t * (Z n ω - Z 0 ω)) * exp (t * D ω) := by
      ext ω
      rw [← exp_add, hD_def, Pi.sub_apply]
      ring_nf
    have hDexp (t : ℝ) : Integrable (fun ω ↦ exp (t * D ω)) μ :=
      integrable_exp_mul_of_mem_Icc hDint.aemeasurable (hD.mono fun _ h ↦ abs_le.mp h)
    have hprod (t : ℝ) : Integrable
        (fun ω ↦ exp (t * (Z n ω - Z 0 ω)) * exp (t * D ω)) μ :=
      (ih.integrable_exp_mul t).mul_bdd
        (continuous_exp.comp_aestronglyMeasurable (hDint.1.const_mul t)) (hDbd t)
    have hSm (t : ℝ) : StronglyMeasurable[ℱ n] fun ω ↦ exp (t * (Z n ω - Z 0 ω)) :=
      continuous_exp.comp_stronglyMeasurable (((hZ.stronglyMeasurable n).sub
        ((hZ.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le n)))).const_mul t)
    have hpull (t : ℝ) := condExp_mul_of_stronglyMeasurable_left (hSm t) (hprod t) (hDexp t)
    rw [Finset.sum_Icc_succ_top (by lia : 1 ≤ n + 1)]
    refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
    · rw [hsplit t]
      exact hprod t
    calc mgf (fun ω ↦ Z (n + 1) ω - Z 0 ω) μ t
        = ∫ ω, exp (t * (Z n ω - Z 0 ω)) * exp (t * D ω) ∂μ := by
          rw [mgf, hsplit t]
      _ = ∫ ω, (μ[(fun ω ↦ exp (t * (Z n ω - Z 0 ω))) * (fun ω ↦ exp (t * D ω)) | ℱ n]) ω ∂μ :=
          (integral_condExp (ℱ.le n)).symm
      _ = ∫ ω, exp (t * (Z n ω - Z 0 ω)) * (μ[fun ω ↦ exp (t * D ω) | ℱ n]) ω ∂μ :=
          integral_congr_ae (hpull t)
      _ ≤ ∫ ω, exp (t * (Z n ω - Z 0 ω)) * exp (c (n + 1) ^ 2 * t ^ 2 / 2) ∂μ := by
          refine integral_mono_ae (integrable_condExp.congr (hpull t))
            ((ih.integrable_exp_mul t).mul_const _) ?_
          filter_upwards [hcond t] with ω hω
          exact mul_le_mul_of_nonneg_left hω (exp_pos _).le
      _ = mgf (fun ω ↦ Z n ω - Z 0 ω) μ t * exp (c (n + 1) ^ 2 * t ^ 2 / 2) :=
          integral_mul_const _ _
      _ ≤ exp ((∑ i ∈ Finset.Icc 1 n, ‖c i‖₊ ^ 2 : ℝ≥0) * t ^ 2 / 2) *
            exp (c (n + 1) ^ 2 * t ^ 2 / 2) := by
          gcongr
          exact ih.mgf_le t
      _ = exp ((∑ i ∈ Finset.Icc 1 n, ‖c i‖₊ ^ 2 + ‖c (n + 1)‖₊ ^ 2 : ℝ≥0) * t ^ 2 / 2) := by
          rw [← exp_add]
          push_cast
          rw [Real.norm_eq_abs, sq_abs]
          ring_nf

end MeasureTheory.Martingale

namespace MathlibExt.Probability.AzumaInequalityWanted

/-- **Azuma's inequality.** Let `Z₀, Z₁, …` be a martingale with respect to a filtration on a
probability space, let `n` be a natural number and suppose `|Zᵢ - Zᵢ₋₁| ≤ cᵢ` everywhere for
`1 ≤ i ≤ n`. Then for every `a > 0`,
`P(Zₙ - Z₀ ≥ a) ≤ exp(-a² / (2 ∑_{i=1}^{n} cᵢ²))`
(Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Theorem 8.6,
general form; the case `cᵢ = 1`, `a = λ√n` gives `P(Zₙ - Z₀ ≥ λ√n) ≤ e^{-λ²/2}`). -/
theorem azuma_inequality {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ ω, |Z i ω - Z (i - 1) ω| ≤ c i) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ Z n ω - Z 0 ω} ≤
      Real.exp (-a ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, c i ^ 2)) := by
  have h := (hZ.hasSubgaussianMGF_sub_of_abs_sub_le
    fun i hi ↦ ae_of_all μ (hc i hi)).measure_ge_le ha.le
  have hsum : ((∑ i ∈ Finset.Icc 1 n, ‖c i‖₊ ^ 2 : ℝ≥0) : ℝ) =
      ∑ i ∈ Finset.Icc 1 n, c i ^ 2 := by
    push_cast
    simp only [Real.norm_eq_abs, sq_abs]
  rwa [hsum] at h

end MathlibExt.Probability.AzumaInequalityWanted
