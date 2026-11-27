/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.WithDensity
public import MathlibExt.Combinatorics.Enumerative.Catalan.Bounds
public import MathlibExt.MeasureTheory.Measure.MomentDeterminacy

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The Wigner semicircle distribution and its moments

The semicircle distribution `σ` is the probability measure on `ℝ` with density
`√(4 - x²) / (2π)` on `[-2, 2]`. It is the limit law in Wigner's semicircle law for the
empirical spectral distributions of normalised Wigner matrices.

Its moments are the Catalan numbers: `∫ x ^ (2k) dσ = C_k` and `∫ x ^ (2k+1) dσ = 0`.
In the moment-method proof of the semicircle law, `C_k` counts the non-crossing pairings
(Dyck words of semilength `k`) that dominate `𝔼 tr (W/√n)^(2k) / n`, and the computation below
identifies the limit with `σ`.

The proof substitutes `x = 2 cos θ`, `θ ∈ [0, π]`, which turns the moment into
`2^(n+2) / (2π) · ∫₀^π cos^n θ sin² θ dθ`, and then uses the reduction formula
`∫₀^π cos^(n+2) = (n+1)/(n+2) ∫₀^π cos^n` (Mathlib's `integral_cos_pow`).

## Main definitions

* `ProbabilityTheory.semicirclePDFReal`: the density `x ↦ √(4 - x²) / (2π)`.
* `ProbabilityTheory.semicircleReal`: the semicircle distribution.

## Main results

* `ProbabilityTheory.integral_pow_two_mul_semicircleReal`: even moments are Catalan numbers.
* `ProbabilityTheory.integral_pow_two_mul_add_one_semicircleReal`: odd moments vanish.
* `ProbabilityTheory.integral_pow_two_mul_semicircleReal_eq_card_dyckWord`: the `2k`-th moment
  is the number of Dyck words of semilength `k`.
* `ProbabilityTheory.isProbabilityMeasure_semicircleReal`: `σ` is a probability measure.
* `ProbabilityTheory.eq_semicircleReal_of_integral_pow_eq`: `σ` is determined by its moments, so a
  finite measure with the moments of `σ` is `σ`; this is how the moment method identifies the
  limit in the semicircle law.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  §2.4.2 (the moment method for the semicircular law), Exercise 2.4.9 (the moments are the
  Catalan numbers `C_{k/2}`, defined in `(2.88)`) and Lemma 2.3.15 (Catalan numbers count Dyck
  words).
* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.1.1.
-/

@[expose] public section

open MeasureTheory Real Set intervalIntegral

namespace ProbabilityTheory

/-- The density of the Wigner semicircle distribution, `x ↦ √(4 - x²) / (2π)`. It vanishes
outside `[-2, 2]` because `Real.sqrt` is `0` on negative numbers. -/
noncomputable def semicirclePDFReal (x : ℝ) : ℝ := √(4 - x ^ 2) / (2 * π)

/-- The semicircle density is nonnegative. -/
lemma semicirclePDFReal_nonneg (x : ℝ) : 0 ≤ semicirclePDFReal x := by
  unfold semicirclePDFReal; positivity

/-- The semicircle density is continuous on `ℝ`; it vanishes at and beyond `±2`. -/
lemma continuous_semicirclePDFReal : Continuous semicirclePDFReal := by
  unfold semicirclePDFReal; fun_prop

/-- The **Wigner semicircle distribution** `σ` on `ℝ`: Lebesgue measure on `[-2, 2]` with
density `√(4 - x²) / (2π)`, so `σ(A) = ∫_{A ∩ [-2, 2]} √(4 - x²) / (2π) dx`
(Tao, *Topics in Random Matrix Theory*, §2.4, equation `(2.81)`). -/
noncomputable def semicircleReal : Measure ℝ :=
  (volume.restrict (Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (semicirclePDFReal x))

/-- Integrals against the semicircle distribution are interval integrals over `[-2, 2]`
weighted by the density. -/
theorem integral_semicircleReal (g : ℝ → ℝ) :
    ∫ x, g x ∂semicircleReal = ∫ x in (-2 : ℝ)..2, semicirclePDFReal x * g x := by
  rw [semicircleReal, integral_withDensity_eq_integral_toReal_smul
    (continuous_semicirclePDFReal.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (semicirclePDFReal_nonneg x)]

/-- The reduction formula `∫₀^π cos^(n+2) = (n+1)/(n+2) ∫₀^π cos^n`. -/
private lemma integral_cos_pow_add_two_zero_pi (n : ℕ) :
    ∫ θ in (0 : ℝ)..π, cos θ ^ (n + 2) =
      (n + 1) / (n + 2) * ∫ θ in (0 : ℝ)..π, cos θ ^ n := by
  rw [integral_cos_pow]; simp

private lemma integral_cos_pow_two_mul_add_one_zero_pi (k : ℕ) :
    ∫ θ in (0 : ℝ)..π, cos θ ^ (2 * k + 1) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, integral_cos_pow_add_two_zero_pi, ih,
      mul_zero]

private lemma integral_cos_pow_two_mul_zero_pi (k : ℕ) :
    ∫ θ in (0 : ℝ)..π, cos θ ^ (2 * k) = π * k.centralBinom / 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, integral_cos_pow_add_two_zero_pi, ih]
    have h : ((k + 1 : ℕ) : ℝ) * (k + 1).centralBinom = 2 * (2 * k + 1) * k.centralBinom := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hk : (0 : ℝ) < k + 1 := by positivity
    rw [show ((k + 1).centralBinom : ℝ) = 2 * (2 * k + 1) * k.centralBinom / (k + 1) by
      rw [eq_div_iff hk.ne', mul_comm, ← h]; push_cast; ring]
    push_cast
    field_simp
    ring

/-- Substitution `x = 2 cos θ`: `∫_{-2}^2 xⁿ √(4 - x²) dx = 2^(n+2) ∫₀^π cosⁿ θ sin² θ dθ`,
written with `sin² = 1 - cos²`. -/
private lemma integral_pow_mul_sqrt_four_sub_sq (n : ℕ) :
    ∫ x in (-2 : ℝ)..2, x ^ n * √(4 - x ^ 2) =
      2 ^ (n + 2) * ((∫ θ in (0 : ℝ)..π, cos θ ^ n) - ∫ θ in (0 : ℝ)..π, cos θ ^ (n + 2)) := by
  set g : ℝ → ℝ := fun x => x ^ n * √(4 - x ^ 2) with hg
  have hsub := integral_comp_mul_deriv (a := 0) (b := π) (f := fun θ => 2 * cos θ)
    (f' := fun θ => -(2 * sin θ)) (g := g)
    (fun θ _ => by simpa using (hasDerivAt_cos θ).const_mul 2)
    (by fun_prop) (by rw [hg]; fun_prop)
  have hsub' : ∫ θ in (0 : ℝ)..π, (g ∘ fun θ => 2 * cos θ) θ * -(2 * sin θ) =
      -∫ x in (-2 : ℝ)..2, g x := by
    rw [hsub]; simp only [cos_zero, cos_pi, mul_one, mul_neg]; exact integral_symm _ _
  have key : ∫ x in (-2 : ℝ)..2, g x =
      ∫ θ in (0 : ℝ)..π, 2 ^ (n + 2) * (cos θ ^ n - cos θ ^ (n + 2)) := by
    rw [← neg_neg (∫ x in (-2 : ℝ)..2, g x), ← hsub', ← intervalIntegral.integral_neg]
    refine integral_congr fun θ hθ => ?_
    rw [uIcc_of_le pi_pos.le] at hθ
    have hs : 0 ≤ sin θ := sin_nonneg_of_mem_Icc hθ
    have hsq : √(4 - (2 * cos θ) ^ 2) = 2 * sin θ := by
      rw [show 4 - (2 * cos θ) ^ 2 = (2 * sin θ) ^ 2 by nlinarith [sin_sq_add_cos_sq θ]]
      exact sqrt_sq (by positivity)
    simp only [Function.comp, hg, hsq]
    have : sin θ ^ 2 = 1 - cos θ ^ 2 := by nlinarith [sin_sq_add_cos_sq θ]
    rw [mul_pow]
    linear_combination (2 ^ (n + 2) * cos θ ^ n) * this
  change ∫ x in (-2 : ℝ)..2, g x = _
  rw [key, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((by fun_prop : Continuous fun θ => cos θ ^ n).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun θ => cos θ ^ (n + 2)).intervalIntegrable _ _)]

/-- The `n`-th moment of the semicircle distribution in terms of `∫₀^π cosⁿ`. -/
private lemma integral_pow_semicircleReal (n : ℕ) :
    ∫ x, x ^ n ∂semicircleReal =
      2 ^ (n + 2) / (2 * π * (n + 2)) * ∫ θ in (0 : ℝ)..π, cos θ ^ n := by
  rw [integral_semicircleReal]
  have : ∀ x : ℝ, semicirclePDFReal x * x ^ n = (2 * π)⁻¹ * (x ^ n * √(4 - x ^ 2)) := by
    intro x; unfold semicirclePDFReal; field_simp
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_pow_mul_sqrt_four_sub_sq,
    integral_cos_pow_add_two_zero_pi]
  have hn : (0 : ℝ) < n + 2 := by positivity
  field_simp
  ring

/-- **The even moments of the semicircle distribution are the Catalan numbers**:
`∫ x^(2k) dσ(x) = C_k` (Tao, *Topics in Random Matrix Theory*, §2.4.2, Exercise 2.4.9). -/
theorem integral_pow_two_mul_semicircleReal (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂semicircleReal = catalan k := by
  rw [integral_pow_semicircleReal, integral_cos_pow_two_mul_zero_pi]
  have h : ((k + 1 : ℕ) : ℝ) * catalan k = k.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom k
  have hk : (0 : ℝ) < k + 1 := by positivity
  rw [show (catalan k : ℝ) = k.centralBinom / (k + 1) by
    rw [eq_div_iff hk.ne', mul_comm, ← h]; push_cast; ring]
  rw [show (2 : ℝ) ^ (2 * k + 2) = 4 ^ k * 4 by rw [pow_add, pow_mul]; norm_num]
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  push_cast
  ring

/-- **The odd moments of the semicircle distribution vanish.** -/
theorem integral_pow_two_mul_add_one_semicircleReal (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) ∂semicircleReal = 0 := by
  rw [integral_pow_semicircleReal, integral_cos_pow_two_mul_add_one_zero_pi, mul_zero]

/-- The `2k`-th moment of the semicircle distribution is the number of Dyck words of
semilength `k`, the combinatorial count behind the moment method. -/
theorem integral_pow_two_mul_semicircleReal_eq_card_dyckWord (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂semicircleReal =
      Fintype.card {p : DyckWord // p.semilength = k} := by
  rw [integral_pow_two_mul_semicircleReal, DyckWord.card_dyckWord_semilength_eq_catalan]

/-- **The semicircle distribution is a probability measure**: `∫_{-2}^2 √(4 - x²) dx = 2π`. -/
instance isProbabilityMeasure_semicircleReal : IsProbabilityMeasure semicircleReal := by
  constructor
  have hint : Integrable semicirclePDFReal (volume.restrict (Icc (-2 : ℝ) 2)) :=
    continuous_semicirclePDFReal.integrableOn_Icc
  rw [semicircleReal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall semicirclePDFReal_nonneg)]
  have h0 := integral_pow_two_mul_semicircleReal 0
  rw [integral_semicircleReal, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc] at h0
  simp only [mul_zero, pow_zero, mul_one, catalan_zero, Nat.cast_one] at h0
  rw [h0, ENNReal.ofReal_one]

/-- The semicircle distribution gives no mass outside `[-2, 2]` (Tao, *Topics in Random Matrix
Theory*, `(2.81)`). -/
theorem semicircleReal_compl_Icc : semicircleReal (Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [semicircleReal, withDensity_apply _ measurableSet_Icc.compl,
    Measure.restrict_restrict measurableSet_Icc.compl, compl_inter_self, Measure.restrict_empty,
    lintegral_zero_measure]

/-- Every power `xᵏ` is integrable against the semicircle distribution, which is a finite measure
supported in `[-2, 2]`, so its moments (Tao, *Topics in Random Matrix Theory*, Exercise 2.4.9) are
genuine integrals. -/
theorem integrable_pow_semicircleReal (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) semicircleReal := by
  have h : semicircleReal.restrict (Icc (-2 : ℝ) 2) = semicircleReal :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr semicircleReal_compl_Icc)
  rw [← h]
  exact (continuous_pow k).integrableOn_Icc

/-- **The semicircle distribution is determined by its moments** (Tao, *Topics in Random Matrix
Theory*, §2.4.2). If a finite measure `ν` on `ℝ` has integrable even powers and the same moments
as the semicircle distribution `σ`, `∫ xᵏ dν = ∫ xᵏ dσ` for every `k`, then `ν = σ`. Its even
moments are then the Catalan numbers `C_k ≤ 4ᵏ`, which confines `ν` to `[-2, 2]`, and compactly
supported measures are determined by their moments. -/
theorem eq_semicircleReal_of_integral_pow_eq {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ (2 * k)) ν)
    (heq : ∀ k : ℕ, ∫ x, x ^ k ∂ν = ∫ x, x ^ k ∂semicircleReal) : ν = semicircleReal := by
  have hsupp : ν {x | 2 < |x|} = 0 := by
    refine measure_lt_abs_eq_zero_of_integral_pow_le (C := 1) two_pos hint fun k => ?_
    rw [heq, integral_pow_two_mul_semicircleReal, one_mul, pow_mul]
    norm_num
    exact_mod_cast catalan_le_four_pow k
  have hset : (Icc (-2 : ℝ) 2)ᶜ = {x | 2 < |x|} := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq, ← abs_le, not_le]
  exact ext_of_forall_integral_pow_eq_of_compl_Icc (hset ▸ hsupp) semicircleReal_compl_Icc heq

end ProbabilityTheory
