/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasRootPower

namespace MetaMathlibExt

-- At the first admissible index, the predecessor is zero even for a nonreal root.
example (P : LucasSequenceParams) (hp : P.p = 0) (hq : P.q = 1) :
    Complex.I = Complex.I * lucasU P 1 - lucasU P 0 := by
  have h := lucasU_root_pow P (α := Complex.I) (by simp [hp, hq, Complex.I_sq]) (n := 1) le_rfl
  simpa [hq] using h

-- The repeated root of t² - 2t + 1 gives a constant first difference.
example (P : LucasSequenceParams) (hp : P.p = 2) (hq : P.q = 1) (n : ℕ) :
    (lucasU P (n + 1) : ℂ) - lucasU P n = 1 := by
  have h := lucasU_root_pow P (α := 1) (by norm_num [hp, hq]) (n := n + 1) (Nat.le_add_left 1 n)
  simpa [hq] using h.symm

end MetaMathlibExt
