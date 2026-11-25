/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Erdős's quarter lower bound for minimum overlap

The overlap of an admissible pair is a convolution after reflecting the first function.
Its integral is one, and all its mass lies in the translation interval of length four.
-/

@[expose] public section

open MeasureTheory Set
open scoped Convolution

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **Erdős's unpublished upper bound $4/9$ for the minimum-overlap constant (statement).** The
statement that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 4/9$.

Source: Erdős, unpublished; Optimization Problems, Constant 1b. -/
def upperBound_Erdos_unpublished_fourNinths : Prop := C₁ᵦ ≤ (4 : ℝ) / 9

/-- **The proposition $1/4 \le C_{1b}$.** This is the proposition that the continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $1/4 \le C_{1b}$.

Source: Erdős 1955; Optimization Problems, Constant 1b. -/
def lowerBound_E1955_quarter : Prop := (1 : ℝ) / 4 ≤ C₁ᵦ

private theorem integral_complement {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) :
    (∫ t, g t) = 1 := by
  have hsum : (∫ t in continuousSupportInterval, f t + g t) = 2 := calc
    _ = ∫ _ in continuousSupportInterval, (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc h.complementary
    _ = 2 := by norm_num [continuousSupportInterval, Real.volume_real_Icc]
  rw [integral_add h.integrable_f.integrableOn h.integrable_g.integrableOn,
    setIntegral_eq_integral_of_forall_compl_eq_zero h.zero_outside_f,
    setIntegral_eq_integral_of_forall_compl_eq_zero h.zero_outside_g, h.integral_f] at hsum
  linarith

private theorem integral_overlap {f g : ℝ → ℝ} (h : ContinuousAdmissible f g) :
    (∫ x in continuousTranslationInterval, continuousOverlap f g x) = 1 := by
  have hzero (x : ℝ) (hx : x ∉ continuousTranslationInterval) : continuousOverlap f g x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have hout : x + t ∉ continuousSupportInterval := by
      intro hxt
      exact hx ⟨by linarith [hxt.1, ht.2], by linarith [hxt.2, ht.1]⟩
    simp [continuousOverlapIntegrand, h.zero_outside_g _ hout]
  have hconv (x : ℝ) : continuousOverlap f g x = ((fun t ↦ f (-t)) ⋆ g) x := by
    unfold continuousOverlap
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht ↦ by simp [continuousOverlapIntegrand, h.zero_outside_f t ht])]
    change (∫ t, f t * g (x + t)) = ∫ t, f (-t) * g (x - t)
    simpa only [sub_eq_add_neg] using
      (integral_neg_eq_self (fun t ↦ f t * g (x + t)) volume).symm
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  simp_rw [hconv]
  rw [integral_convolution _ h.integrable_f.comp_neg h.integrable_g, integral_neg_eq_self,
    h.integral_f, integral_complement h]
  norm_num

/-- **Erdős's lower bound $C_{1b} \ge 1/4$.** The continuous Erdős minimum-overlap constant
$C_{1b}$ satisfies $1/4 \le C_{1b}$.

Source: Erdős 1955 and Optimization Problems 1b. -/
theorem lowerBound_E1955_quarter_holds : lowerBound_E1955_quarter := by
  apply continuousMinimumOverlapConstant_isGreatest.2
  intro f g h
  have hbound (x : ℝ) (hx : x ∈ continuousTranslationInterval) :
      ‖continuousOverlap f g x‖ ≤ continuousPairScore f g := by
    rw [Real.norm_of_nonneg (continuousOverlap_nonneg h x)]
    exact le_csSup h.overlapValues_bddAbove ⟨x, hx, rfl⟩
  have havg := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := continuousTranslationInterval) measure_Icc_lt_top hbound
  rw [integral_overlap h] at havg
  norm_num [continuousTranslationInterval, Real.volume_real_Icc] at havg
  linarith

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
