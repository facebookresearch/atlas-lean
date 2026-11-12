/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Biology.StatisticalGenetics.RareVariantInference.BurdenSKAT
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Characteristic function of a weighted chi-square mixture

For `Q ~ ∑ⱼ λⱼ χ²₁` (`weightedChiSq`, `ξⱼ` independent standard normal),
`𝔼 exp(i t Q) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}` (`charFun_weightedChiSq`), principal branch; each base
has real part `1`. The one-term case is `charFun_map_mul_sq_gaussianReal`:
`𝔼 exp(i t c ξ²) = (1 - 2 i c t)^{-1/2}`.

## Attribution

Moved verbatim (statements and proofs unchanged) from
`MathlibExt/Biology/StatisticalGenetics/RareVariantInference/BurdenSKATO.lean`
(T88, PR #1621, commit 45948b862),
section `Davies`. Only the namespace changed. The law `weightedChiSq` is the canonical one
from `MathlibExt.Biology.StatisticalGenetics.BurdenSKAT` (T37), imported rather than redefined.

## API-00 receipt (base `origin/main` f8123a751)

Reuse search of `MathlibExt`, `WantedExt`, `CSLibExt` and the pinned Mathlib for the
chi-square characteristic function found nothing. Reused: T37's `weightedChiSq`; Mathlib's
`charFun`, `charFun_map_sum_pi_eq_prod`, `integral_gaussian_complex`, `Measure.pi_map_pi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.BurdenSKAT

namespace MathlibExt.Analysis.WeightedChiSquare

open Real Set Filter Topology

open Complex in
private theorem ofReal_mul_cpow' {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ((a : ℂ) * z) ^ s = (a : ℂ) ^ s * z ^ s := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.2 ha.ne') hz),
    cpow_def_of_ne_zero (ofReal_ne_zero.2 ha.ne'), cpow_def_of_ne_zero hz, log_ofReal_mul ha hz,
    ← Complex.exp_add, ofReal_log ha.le]
  ring_nf

open Complex in
/-- The characteristic function of `c χ²₁`: `𝔼 exp(i t c ξ²) = (1 - 2 i c t)^{-1/2}`. -/
theorem charFun_map_mul_sq_gaussianReal (c t : ℝ) :
    charFun ((gaussianReal 0 1).map fun x => c * x ^ 2) t =
      (1 - 2 * c * t * I) ^ (-(1 / 2) : ℂ) := by
  set w : ℂ := 1 - 2 * c * t * I
  set b : ℂ := 1 / 2 - c * t * I
  have hw0 : w ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [w] at this
  have hbre : 0 < b.re := by simp [b]
  have hwarg : w.arg ≠ π := by
    have h := abs_arg_lt_pi_div_two_iff.2 (Or.inl (by simp [w] : 0 < w.re))
    intro hπ
    rw [hπ, abs_of_pos pi_pos] at h
    linarith [pi_pos]
  have hpi : (π : ℂ) / b = ((2 * π : ℝ) : ℂ) * w⁻¹ := by
    have hb : b = w / 2 := by simp only [b, w]; ring
    rw [hb]
    push_cast
    field_simp
  have hsq : ((2 * π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h : ∀ x : ℝ, gaussianPDFReal 0 1 x • cexp (↑t * ↑(c * x ^ 2) * I) =
      ((√(2 * π))⁻¹ : ℝ) * cexp (-b * (x : ℂ) ^ 2) := by
    intro x
    rw [gaussianPDFReal, Complex.real_smul, ofReal_mul, ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    · simp
    · simp only [b]; push_cast; ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian_complex hbre, hpi,
    ofReal_mul_cpow' (by positivity) (inv_ne_zero hw0), hsq, inv_cpow _ _ hwarg, cpow_neg]
  have : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; positivity
  push_cast
  field_simp

open Complex in
/-- **Characteristic function of a weighted chi-square mixture**:
`𝔼 exp(i t ∑ⱼ λⱼ ξⱼ²) = ∏ⱼ (1 - 2 i λⱼ t)^{-1/2}`. -/
theorem charFun_weightedChiSq {k : Type*} [Fintype k] (lam : k → ℝ) (t : ℝ) :
    charFun (weightedChiSq lam) t = ∏ j, (1 - 2 * lam j * t * I) ^ (-(1 / 2) : ℂ) := by
  have hpi : (Measure.pi fun _ : k => gaussianReal 0 1).map (fun ξ j => lam j * ξ j ^ 2) =
      Measure.pi fun j => (gaussianReal 0 1).map fun x => lam j * x ^ 2 :=
    Measure.pi_map_pi (f := fun j x => lam j * x ^ 2) fun j => by fun_prop
  have hw : weightedChiSq lam = (Measure.pi fun j => (gaussianReal 0 1).map
      fun x => lam j * x ^ 2).map fun p => ∑ j, p j := by
    rw [← hpi, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hw, charFun_map_sum_pi_eq_prod, Finset.prod_apply]
  exact Finset.prod_congr rfl fun j _ => charFun_map_mul_sq_gaussianReal (lam j) t

end MathlibExt.Analysis.WeightedChiSquare
