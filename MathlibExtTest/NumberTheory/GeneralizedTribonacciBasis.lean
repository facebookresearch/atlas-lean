/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTribonacciBasis

namespace MetaMathlibExt

-- At index five, the three distinct coefficients detect a permutation of the seeds.
example (a b c : ℤ) :
    generalizedTribonacci a b c 5 = 2 * a + 3 * b + 4 * c := by
  obtain ⟨u, v, w, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    exists_generalizedTribonacci_basis
  have hu : u 5 = 2 := calc
    u 5 = generalizedTribonacci 1 0 0 5 := by
      simpa only [Int.mul_one, Int.mul_zero, Int.add_zero] using (h 1 0 0 5).symm
    _ = 2 := by decide
  have hv : v 5 = 3 := calc
    v 5 = generalizedTribonacci 0 1 0 5 := by
      simpa only [Int.mul_one, Int.mul_zero, Int.zero_add, Int.add_zero] using (h 0 1 0 5).symm
    _ = 3 := by decide
  have hw : w 5 = 4 := calc
    w 5 = generalizedTribonacci 0 0 1 5 := by
      simpa only [Int.mul_one, Int.mul_zero, Int.zero_add] using (h 0 0 1 5).symm
    _ = 4 := by decide
  rw [h a b c 5, hu, hv, hw]

end MetaMathlibExt
