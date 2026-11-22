/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Negligible

/-!
# Tests for the closure properties of negligible functions

* `NegligibleAdv.of_eventually_le` on a function that is nonzero only at `n = 0`.
* `NegligibleAdv.const_mul` and `NegligibleAdv.mul_of_poly_bound`, with a multiplier that is
  negative at `n = 0`.
* The sign hypothesis of `NegligibleAdv.const_mul` is needed: the constant `-1` is negligible,
  `-1` times it is not.
* `negligible_const_mul` and `negligible_mul_of_poly_bound` on `ℚ`, and
  `negligibleAdv_ratCast_iff`.
* The bridge to Mathlib's `SuperpolynomialDecay`, in both directions.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Negligible

open Cslib.Crypto.Framework Cslib.Complexity.Classes Filter

/-- A real function that is `7` at `n = 0` and `0` elsewhere. -/
def spike (n : ℕ) : ℝ := if n = 0 then 7 else 0

theorem negligibleAdv_spike : NegligibleAdv spike :=
  NegligibleAdv.of_eventually_le fun _ => ⟨1, fun n hn => by
    simp only [spike, show n ≠ 0 by omega, ↓reduceIte]
    positivity⟩

example : NegligibleAdv fun n => 3 * spike n :=
  negligibleAdv_spike.const_mul (by norm_num)

/-- The multiplier is negative at `n = 0`, so its nonnegativity holds only eventually. -/
example : NegligibleAdv fun n => (if n = 0 then -37 else (n : ℝ) ^ 3) * spike n := by
  refine negligibleAdv_spike.mul_of_poly_bound (d := 3) ⟨1, fun n hn => ?_⟩
  simp only [show n ≠ 0 by omega, ↓reduceIte]
  exact ⟨by positivity, le_rfl⟩

/-- A negative constant is negligible, because both predicates are one-sided. -/
theorem negligibleAdv_neg_one : NegligibleAdv fun _ => (-1 : ℝ) :=
  NegligibleAdv.of_eventually_le fun c => ⟨0, fun n _ => by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) ^ c := by positivity
    linarith⟩

/-- Scaling by a negative constant need not preserve negligibility. -/
example : ¬ NegligibleAdv fun _ => (-1 : ℝ) * -1 := by
  simpa using not_negligibleAdv_const (δ := 1) one_pos

/-- A rational function that is `7` at `n = 0` and `0` elsewhere. -/
def spikeQ (n : ℕ) : ℚ := if n = 0 then 7 else 0

theorem negligible_spikeQ : Negligible spikeQ := fun _ => ⟨1, fun n hn => by
  simp only [spikeQ, show n ≠ 0 by omega, ↓reduceIte]
  positivity⟩

example : NegligibleAdv fun n => (spikeQ n : ℝ) := negligibleAdv_ratCast_iff.mpr negligible_spikeQ

example : Negligible fun n => (5 / 2 : ℚ) * spikeQ n :=
  negligible_const_mul negligible_spikeQ (by norm_num)

example : Negligible fun n => (if n = 0 then -37 else (n : ℚ) ^ 2) * spikeQ n := by
  refine negligible_mul_of_poly_bound negligible_spikeQ (d := 2) ⟨1, fun n hn => ?_⟩
  simp only [show n ≠ 0 by omega, ↓reduceIte]
  exact ⟨by positivity, le_rfl⟩

/-- Mathlib's zero function decays superpolynomially, so it is a negligible advantage. -/
example : NegligibleAdv (0 : ℕ → ℝ) :=
  NegligibleAdv.of_superpolynomialDecay (Asymptotics.superpolynomialDecay_zero _ _)

/-- A nonnegative negligible advantage decays superpolynomially. -/
example : Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) spike :=
  (negligibleAdv_iff_superpolynomialDecay (Eventually.of_forall fun n => by
    unfold spike; split_ifs <;> norm_num)).mp negligibleAdv_spike

end Cslib.Crypto.FrameworkTests.Negligible
