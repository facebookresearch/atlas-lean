/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.ContinuedFractions.Computation.Basic
import Mathlib.NumberTheory.Real.Irrational
import MathlibExt.NumberTheory.ExtendedContinuantConjugateContinuedFractionNotPurelyPeriodic

/-!
# Tests for the conjugate continued fraction not being purely periodic

The theorem applied to the concrete conjugates `(3 - √2) / 1` and `(-5 - √2) / 3`, and the
corollary that period one is impossible for `(0 - √2) / 1`.
-/

@[expose] public section

namespace MathlibExtTest.NumberTheory.ExtendedContinuantConjugateContinuedFractionNotPurelyPeriodic

open MetaMathlibExt

private theorem not_isSquare_two : ¬ IsSquare (2 : ℤ) := by
  rw [← irrational_sqrt_intCast_iff_of_nonneg (show (0 : ℤ) ≤ 2 by decide)]
  simpa using irrational_sqrt_two

-- The conjugate `(3 - √2) / 1`, with continued fraction `[1; 1, 1, 2, ...]`.
example : ¬ ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
    (GenContFract.IntFractPair.stream
        ((((3 : ℤ) : ℝ) - √((2 : ℤ) : ℝ)) / ((1 : ℤ) : ℝ)) (n + s)).map (·.b) =
      (GenContFract.IntFractPair.stream
        ((((3 : ℤ) : ℝ) - √((2 : ℤ) : ℝ)) / ((1 : ℤ) : ℝ)) n).map (·.b) :=
  conjugate_continuedFraction_not_purelyPeriodic 3 1 2 (by decide) not_isSquare_two (by decide)

-- Period one is impossible for the conjugate `(0 - √2) / 1`.
example : ¬ ∀ n : ℕ,
    (GenContFract.IntFractPair.stream
        ((((0 : ℤ) : ℝ) - √((2 : ℤ) : ℝ)) / ((1 : ℤ) : ℝ)) (n + 1)).map (·.b) =
      (GenContFract.IntFractPair.stream
        ((((0 : ℤ) : ℝ) - √((2 : ℤ) : ℝ)) / ((1 : ℤ) : ℝ)) n).map (·.b) := by
  intro h
  exact conjugate_continuedFraction_not_purelyPeriodic 0 1 2 (by decide) not_isSquare_two
    (by decide) ⟨1, by decide, h⟩

-- The conjugate `(-5 - √2) / 3` is not purely periodic either.
example : ¬ ∃ s : ℕ, 0 < s ∧ ∀ n : ℕ,
    (GenContFract.IntFractPair.stream
        ((((-5 : ℤ) : ℝ) - √((2 : ℤ) : ℝ)) / ((3 : ℤ) : ℝ)) (n + s)).map (·.b) =
      (GenContFract.IntFractPair.stream
        ((((-5 : ℤ) : ℝ) - √((2 : ℤ) : ℝ)) / ((3 : ℤ) : ℝ)) n).map (·.b) :=
  conjugate_continuedFraction_not_purelyPeriodic (-5) 3 2 (by decide) not_isSquare_two (by decide)

end MathlibExtTest.NumberTheory.ExtendedContinuantConjugateContinuedFractionNotPurelyPeriodic
