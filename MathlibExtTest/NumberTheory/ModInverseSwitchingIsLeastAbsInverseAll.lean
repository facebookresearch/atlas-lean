/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsAbsLe

/-!
# Tests for `isLeastAbsInverse_all`

The theorem is proved in `MathlibExt.NumberTheory.ModInverseSwitchingEuclidBezoutCoeffsAbsLe`.
-/

namespace MathlibExtTest.NumberTheory.ModInverseSwitchingIsLeastAbsInverseAll

open MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- The one-step sequence 3, 2, 1 gives the least absolute inverses -1 mod 3 and 1 mod 2.
example : IsLeastAbsInverse (-1 : ℤ) 2 3 ∧ IsLeastAbsInverse (1 : ℤ) 1 2 := by
  let r : ℕ → ℕ := fun i => 3 - i
  let s : ℕ → ℤ := fun i => if i = 1 then -1 else 1
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
  exact ⟨isLeastAbsInverse_all r s 1 hseq 1 (by decide) (by decide),
    isLeastAbsInverse_all r s 1 hseq 2 (by decide) (by decide)⟩

-- Along 8, 3, 2, 1 the inverses 3, -1, 1 are least absolute inverses.
example : IsLeastAbsInverse (3 : ℤ) 3 8 ∧
    IsLeastAbsInverse (-1 : ℤ) 2 3 ∧ IsLeastAbsInverse (1 : ℤ) 1 2 := by
  let r : ℕ → ℕ
    | 0 => 8
    | 1 => 3
    | 2 => 2
    | _ => 1
  let s : ℕ → ℤ
    | 1 => 3
    | 2 => -1
    | _ => 1
  have hseq : IsEuclidSwitchSeq r s 2 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i <;> decide
  exact ⟨isLeastAbsInverse_all r s 2 hseq 1 (by decide) (by decide),
    isLeastAbsInverse_all r s 2 hseq 2 (by decide) (by decide),
    isLeastAbsInverse_all r s 2 hseq 3 (by decide) (by decide)⟩

-- A least absolute inverse is an inverse: 3 * 3 ≡ 1 mod 8.
example : (3 : ℤ) * 3 ≡ 1 [ZMOD 8] := by
  let r : ℕ → ℕ
    | 0 => 8
    | 1 => 3
    | 2 => 2
    | _ => 1
  let s : ℕ → ℤ
    | 1 => 3
    | 2 => -1
    | _ => 1
  have hseq : IsEuclidSwitchSeq r s 2 := by
    refine ⟨by decide, ?_, ?_, rfl, ?_, rfl, ?_⟩
    · intro i hi
      interval_cases i <;> decide
    · intro i hi
      interval_cases i <;> decide
    · intro i hi hj
      interval_cases i
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
    · intro i hi hj
      interval_cases i <;> decide
  exact (isLeastAbsInverse_all r s 2 hseq 1 (by decide) (by decide)).1

end MathlibExtTest.NumberTheory.ModInverseSwitchingIsLeastAbsInverseAll
