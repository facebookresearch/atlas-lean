/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# A logarithmic upper bound for the Gamma function

For `x > 4`, monotonicity and the Gamma recurrence give `x ≤ Γ(x)`.
Thus `Γ(x + 1) ≤ Γ(x)^2`, and bounding the logarithm by its argument suffices.
-/

namespace MetaMathlibExt

open Real

/-- **Upper bound $\Gamma(x + 1) \ln \Gamma(x + 1) \le \Gamma(x)^{\Gamma(x)}$.** For every real
number $x > 4$, $\Gamma(x + 1) \ln \Gamma(x + 1) \le \Gamma(x)^{\Gamma(x)}$.

Source: Karol Gryszka, *Exponential versus Factorial Revisited*, Journal of
Integer Sequences 28 (2025), Article 25.2.8, Lemma 9 (`jis-2025-25.2.8-lem-9`). -/
public theorem Gamma_add_one_mul_log_le_Gamma_rpow_self {x : ℝ} (hx : 4 < x) :
    Real.Gamma (x + 1) * Real.log (Real.Gamma (x + 1)) ≤ Real.Gamma x ^ Real.Gamma x := by
  have hx₁ : 0 < x - 1 := by linarith
  have hprev : 2 ≤ Gamma (x - 1) := by
    have h := Gamma_strictMonoOn_Ici.monotoneOn (a := 3) (b := x - 1)
      (by norm_num) (by change 2 ≤ x - 1; linarith) (by linarith)
    simpa using h
  have hxΓ : x ≤ Gamma x := calc
    x ≤ (x - 1) * 2 := by linarith
    _ ≤ (x - 1) * Gamma (x - 1) := mul_le_mul_of_nonneg_left hprev hx₁.le
    _ = Gamma x := by rw [← Gamma_add_one hx₁.ne', sub_add_cancel]
  have hΓ : 0 ≤ Gamma x := by linarith
  have hadd : Gamma (x + 1) ≤ Gamma x ^ 2 := by
    rw [Gamma_add_one (by linarith : x ≠ 0), sq]
    exact mul_le_mul_of_nonneg_right hxΓ hΓ
  have hpos := (Gamma_pos_of_pos (by linarith : 0 < x + 1)).le
  calc
    Gamma (x + 1) * log (Gamma (x + 1)) ≤ Gamma (x + 1) ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (log_le_self hpos) hpos
    _ ≤ (Gamma x ^ 2) ^ 2 := pow_le_pow_left₀ hpos hadd 2
    _ = Gamma x ^ (4 : ℝ) := by norm_num [← pow_mul]
    _ ≤ Gamma x ^ Gamma x := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end MetaMathlibExt
