/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.LinearityTest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the BLR linearity test

* Boundary checks: a linear function passes with probability `1`, and the zero function is at
  distance `0` from the zero linear function.
* A nonlinear function: Boolean AND on `(ZMod 2)²` passes on exactly `10` of the `16` pairs
  (acceptance probability `5 / 8`), is at distance exactly `1 / 4` from the nearest linear
  function, and `blr_soundness` at its rejection probability `3 / 8` yields a linear function
  within distance `3 / 8`.
-/

@[expose] public section

namespace MathlibExtTest.Complexity.LinearityTest

open MathlibExt.Complexity.LinearityTest

/-- Boundary check: the zero linear function over
`Fin 2 → ZMod 2` passes the BLR test with probability `1`. -/
example : acceptProb (linFun (0 : Fin 2 → ZMod 2)) = 1 :=
  blr_complete _

/-- Boundary check: the zero function disagrees with itself
with probability `0`. -/
example : disagreeProb (0 : (Fin 2 → ZMod 2) → ZMod 2)
    (linFun (0 : Fin 2 → ZMod 2)) = 0 := by
  unfold disagreeProb
  simp

/-- Boolean AND on `(ZMod 2)²`, a nonlinear function. -/
def andFun (x : Fin 2 → ZMod 2) : ZMod 2 :=
  x 0 * x 1

/-- The test accepts AND on exactly `10` of the `16` pairs. -/
theorem card_blrAccepts_andFun : (blrAccepts andFun).card = 10 := by
  decide

/-- The exact acceptance probability of AND is `10 / 16 = 5 / 8`. -/
theorem acceptProb_andFun : acceptProb andFun = 5 / 8 := by
  rw [acceptProb, card_blrAccepts_andFun]
  norm_num [Fintype.card_prod, Fintype.card_fun, ZMod.card]

/-- AND differs from every linear function on at least one of the `4` inputs. -/
theorem one_le_card_disagree_andFun (a : Fin 2 → ZMod 2) :
    1 ≤ (Finset.univ.filter fun x => andFun x ≠ linFun a x).card := by
  revert a
  decide

/-- AND differs from the zero linear function on exactly one input. -/
theorem card_disagree_andFun_zero :
    (Finset.univ.filter fun x => andFun x ≠ linFun 0 x).card = 1 := by
  decide

/-- The distance from AND to the nearest linear function is exactly `1 / 4`. -/
theorem disagreeProb_andFun :
    (∀ a, 1 / 4 ≤ disagreeProb andFun (linFun a)) ∧ disagreeProb andFun (linFun 0) = 1 / 4 := by
  have hcard : (Fintype.card (Fin 2 → ZMod 2) : ℝ) = 4 := by
    norm_num [Fintype.card_fun, ZMod.card]
  refine ⟨fun a => ?_, ?_⟩
  · rw [disagreeProb, hcard]
    have h1 : (1 : ℝ) ≤ (Finset.univ.filter fun x => andFun x ≠ linFun a x).card := by
      exact_mod_cast one_le_card_disagree_andFun a
    linarith
  · rw [disagreeProb, hcard, card_disagree_andFun_zero]
    norm_num

/-- `blr_soundness` at the rejection probability `3 / 8` of AND gives a linear function within
distance `3 / 8`. -/
example : ∃ a, disagreeProb andFun (linFun a) ≤ 3 / 8 :=
  blr_soundness andFun (3 / 8) (by norm_num) (by rw [acceptProb_andFun]; norm_num)

end MathlibExtTest.Complexity.LinearityTest
