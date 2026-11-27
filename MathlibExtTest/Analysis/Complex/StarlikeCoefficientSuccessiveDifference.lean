/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.StarlikeCoefficientSuccessiveDifference
import Mathlib.Tactic.Linarith

/-! # Tests for `MathlibExt.Analysis.Complex.StarlikeCoefficientSuccessiveDifference` -/

open MathlibExt.Analysis.StarlikeCoefficientSuccessiveDifferenceWanted
open Complex (wimanTaylorCoefficient)

namespace MathlibExtTest.StarlikeCoefficientSuccessiveDifference

-- Test section: the hypotheses are satisfiable. The identity map is in the class `S` and is
-- starlike, since `z * 1 / z = 1` has positive real part.
private theorem id_isInClassS : IsInClassS fun z : ℂ ↦ z :=
  ⟨analyticOn_id, rfl, hasDerivAt_id 0, Set.injOn_id _⟩

private theorem id_isStarlike : IsStarlike fun z : ℂ ↦ z := by
  refine ⟨analyticOn_id, fun z _ hz ↦ ?_⟩
  simp [hz]

-- The first Taylor coefficient of a function in the class `S` is `f'(0) = 1`.
private theorem wimanTaylorCoefficient_one {f : ℂ → ℂ} (hS : IsInClassS f) :
    wimanTaylorCoefficient f 1 = 1 := by
  simp [wimanTaylorCoefficient, hS.2.2.1.deriv]

-- Test section: the theorem. Applied to the identity map at `n = 1`.
example : |‖wimanTaylorCoefficient (fun z : ℂ ↦ z) 2‖ -
    ‖wimanTaylorCoefficient (fun z : ℂ ↦ z) 1‖| ≤ 1 :=
  conjecture_holds _ id_isInClassS id_isStarlike 1 le_rfl

-- At `n = 1` it is the bound `|a₂| ≤ 2` for normalized starlike functions.
example (f : ℂ → ℂ) (hS : IsInClassS f) (hst : IsStarlike f) :
    ‖wimanTaylorCoefficient f 2‖ ≤ 2 := by
  have h := conjecture_holds f hS hst 1 le_rfl
  rw [wimanTaylorCoefficient_one hS, norm_one] at h
  linarith [(abs_le.1 h).2]

-- Summing the successive bounds gives `|aₙ| ≤ n` for every `n ≥ 1` (Bieberbach's inequality for
-- starlike functions).
example (f : ℂ → ℂ) (hS : IsInClassS f) (hst : IsStarlike f) (n : ℕ) (hn : 1 ≤ n) :
    ‖wimanTaylorCoefficient f n‖ ≤ n := by
  induction n, hn using Nat.le_induction with
  | base => simp [wimanTaylorCoefficient_one hS]
  | succ n hn ih =>
    have h := conjecture_holds f hS hst n hn
    push_cast
    linarith [(abs_le.1 h).2]

-- The definition `conjecture` holds.
example : conjecture := conjecture_holds

end MathlibExtTest.StarlikeCoefficientSuccessiveDifference
