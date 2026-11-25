/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedEulerianGamma

open MetaMathlibExt

-- The empty permutation contributes one, including when its cycle weight is zero.
example (q t : ℚ) : generalizedEulerianP q t (-1) 1 0 = 1 := by
  have h := (generalizedEulerianP_neg_one q t 0).2.1
  simpa [Finset.univ_unique, cycleQuotientCount_eq, excedanceCount] using h

-- The four-cycle 0 → 1 → 2 → 3 → 0 occurs with a negative integer exponent.
example : (2 : ℤ) - excedanceCount 4 (finRotate 4) = -1 ∧
    doubleExcedanceCount (finRotate 4) = 2 := by decide

-- Of the nine derangements on four points, five contribute to the unsigned sum.
example (t : ℚ) : generalizedEulerianP 1 t (-1) 1 4 = 5 := by
  have h := (generalizedEulerianP_neg_one 1 t 2).2
  have hc : (Finset.univ.filter (fun w : Equiv.Perm (Fin 4) ↦
      Fintype.card (Function.fixedPoints w) = 0 ∧ excedanceCount 4 w = 2 ∧
        doubleExcedanceCount w = 0)).card = 5 := by decide
  simp at hc
  simpa [hc] using h.1.trans h.2
