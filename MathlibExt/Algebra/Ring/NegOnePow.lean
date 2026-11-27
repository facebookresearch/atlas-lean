/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Ring.NegOnePow

import Mathlib.Tactic.Ring

/-!
# Triangular integer signs

The unit `(-1)^(n*(n+1)/2)` compares the two Hom differential conventions.
Its recurrence holds for positive and negative integer degrees.
-/

@[expose] public section

namespace Int

/-- The integer unit `(-1)^(n*(n+1)/2)`. -/
def triangularSign (n : ℤ) : ℤˣ := (n * (n + 1) / 2).negOnePow

@[simp]
theorem triangularSign_zero : triangularSign 0 = 1 := rfl

@[simp]
theorem triangularSign_one : triangularSign 1 = -1 := rfl

/-- The triangular-number recurrence is valid in the full integer grading. -/
theorem triangularSign_succ (n : ℤ) :
    triangularSign (n + 1) = triangularSign n * (n + 1).negOnePow := by
  have h : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
    calc
      _ = (n * (n + 1) + (n + 1) * 2) / 2 :=
        congrArg (fun z : ℤ => z / 2) (by ring)
      _ = _ := Int.add_mul_ediv_right _ _ (by decide)
  unfold triangularSign
  rw [h, Int.negOnePow_add]

/-- Multiplying by the next-degree sign reverses the recurrence, since it is a unit. -/
theorem triangularSign_succ_mul_negOnePow (n : ℤ) :
    triangularSign (n + 1) * (n + 1).negOnePow = triangularSign n := by
  rw [triangularSign_succ, mul_assoc, Int.units_mul_self, mul_one]

end Int
