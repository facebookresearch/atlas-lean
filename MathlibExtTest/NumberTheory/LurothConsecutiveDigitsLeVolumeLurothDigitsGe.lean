/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothConsecutiveDigitsLeVolumeLurothDigitsGe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the lower bound for large Lüroth digit values

Applications in dimension zero and to a coordinate function in dimension one.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 7.
-/

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.NumberTheory.LurothConsecutiveDigitsLeVolumeLurothDigitsGe

example : (∫⁻ _ : Fin 0 → ℝ, (1 : ℝ≥0∞)) ≤ 1 := by
  simpa only [one_mul, le_refl, implies_true, and_true, Set.ofPred_mem_eq, Set.ofPred_true,
    Fin.forall_fin_zero, Measure.restrict_univ, Fin.prod_univ_zero, ENNReal.ofReal_one,
    Real.volume_Ioc, sub_zero] using
    MetaMathlibExt.le_volume_lurothDigits_ge (m := 0) (fun _ => 1)
    (fun _ _ => zero_lt_one) 1 (fun _ _ => by simp) 1

example :
    (∫⁻ x in {x : Fin 1 → ℝ | (∀ i, 2 ≤ x i) ∧ 6 ≤ x 0},
      ENNReal.ofReal (∏ i, 1 / x i ^ 2)) ≤
      volume {x ∈ Set.Ioc (0 : ℝ) 1 | 3 ≤ (MetaMathlibExt.lurothDigitSeq x 0 : ℝ)} := by
  have hpos (x : Fin 1 → ℝ) (hx : ∀ i, 2 ≤ x i) : 0 < x 0 := by linarith [hx 0]
  have hM (x : Fin 1 → ℝ) (hx : ∀ i, 2 ≤ x i) : x 0 ≤ 2 * (⌊x 0⌋₊ : ℝ) := by
    have hlo : (2 : ℝ) ≤ ⌊x 0⌋₊ := by
      exact_mod_cast (Nat.le_floor_iff (by linarith [hx 0])).2 (hx 0)
    have hhi := Nat.lt_floor_add_one (x 0)
    linarith
  simpa only [show (2 : ℝ) * 3 = 6 by norm_num, Fin.val_zero] using
    MetaMathlibExt.le_volume_lurothDigits_ge (fun x : Fin 1 → ℝ => x 0)
    hpos 2 hM 3

end MathlibExtTest.NumberTheory.LurothConsecutiveDigitsLeVolumeLurothDigitsGe
