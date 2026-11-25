/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSum

/-! # Tests for the monic Chebyshev partial sums -/

open MetaMathlibExt Polynomial

-- The empty partial sum contributes one to the generating function.
example : (PowerSeries.mk chebyshevCPartialSum).constantCoeff = 1 := by
  simp [chebyshevCPartialSum]

-- At X = 0 the denominator is 1 + t², so the linear term comes entirely from the numerator.
example :
    (1 + PowerSeries.X ^ 2) * PowerSeries.mk (fun n => (chebyshevCPartialSum n).eval 0) =
      (1 + PowerSeries.X : PowerSeries ℤ) := by
  have h : PowerSeries.map (evalRingHom (0 : ℤ)) (PowerSeries.mk chebyshevCPartialSum) =
      PowerSeries.mk (fun n => (chebyshevCPartialSum n).eval 0) := by
    apply PowerSeries.ext
    intro n
    simp
  simpa [h] using congrArg (PowerSeries.map (evalRingHom (0 : ℤ)))
    chebyshevCPartialSum_generatingFunction

-- At the first admissible index the predecessor is the constant polynomial one.
example : chebyshevCPartialSum 2 = X ^ 2 + X - 1 := by
  rw [chebyshevCPartialSum_recurrence 1 (by decide), chebyshevCPartialSum_one_two.1,
    chebyshevCPartialSum_zero]
  ring
