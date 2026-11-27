/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsSqAddLe

namespace MathlibExtTest.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsSqAddLe

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- For 3 and 2 the Euclidean Bézout pair is (1, -1), attaining the minimum 2.
example (x y : ℤ)
    (hxy : x * ((3 : ℕ) : ℤ) + y * ((2 : ℕ) : ℤ) = ((Nat.gcd 3 2 : ℕ) : ℤ)) :
    (2 : ℤ) ≤ x ^ 2 + y ^ 2 := by
  let r : ℕ → ℕ
    | 0 => 3
    | 1 => 2
    | _ => 1
  let s : ℕ → ℤ
    | 1 => -1
    | _ => 1
  have hseq : IsEuclidSwitchSeq r s 1 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i
      decide
  have hsq : (s 2 : ℤ) ^ 2 + (s 1 : ℤ) ^ 2 = 2 := by decide
  have h := euclid_bezout_coeffs_sq_add_le 3 2 (by decide) (by decide) r s 1
    hseq (by decide) (by decide) x y hxy
  simpa [hsq] using h

end MathlibExtTest.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsSqAddLe
