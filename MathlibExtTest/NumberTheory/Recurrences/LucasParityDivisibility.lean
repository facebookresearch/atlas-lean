/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasParityDivisibility

namespace MetaMathlibExt

private def positiveParams : LucasSequenceParams := ⟨3, 2, by decide⟩
private def zeroParams : LucasSequenceParams := ⟨0, 2, by decide⟩

example : (3 : ℤ) ∣ 15 := by
  rw [← show lucasU positiveParams 4 = 15 by decide]
  exact (p_dvd_lucasU_two_mul_and_lucasV_of_odd (L := positiveParams)).1 2

example : (3 : ℤ) ∣ 9 := by
  rw [← show lucasV positiveParams 3 = 9 by decide]
  exact (p_dvd_lucasU_two_mul_and_lucasV_of_odd (L := positiveParams)).2 3 (by decide)

example : lucasU zeroParams 4 = 0 :=
  zero_dvd_iff.mp ((p_dvd_lucasU_two_mul_and_lucasV_of_odd (L := zeroParams)).1 2)

example : lucasV zeroParams 3 = 0 :=
  zero_dvd_iff.mp ((p_dvd_lucasU_two_mul_and_lucasV_of_odd (L := zeroParams)).2 3 (by decide))

end MetaMathlibExt
