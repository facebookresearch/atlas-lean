/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.YoungTableaux.HookLengthFormula
import MathlibExtTest.Combinatorics.YoungTableaux.HookLength

open MathlibExt.Combinatorics.YoungTableaux.HookLength
open MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted
open MathlibExtTest.Combinatorics.YoungTableaux.HookLength (lam422)

example : sytCount ⊥ = 1 := by
  simpa [YoungDiagram.card] using sytCount_mul_prod_hookLength ⊥

example : sytCount lam422 = 56 := by
  have hh : ∏ c ∈ lam422.cells, hookLength lam422 c = 720 := by
    simp only [hookLength, YoungDiagram.rowLen_eq_card, YoungDiagram.colLen_eq_card]
    decide
  have h := sytCount_mul_prod_hookLength lam422
  rw [hh, show lam422.card = 8 by decide] at h
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 720) h
