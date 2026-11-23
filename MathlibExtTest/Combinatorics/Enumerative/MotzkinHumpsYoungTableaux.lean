/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MotzkinHumpsYoungTableaux
import Mathlib.Data.Fin.VecNotation

namespace MetaMathlibExt

-- The hook of shape (2, 1, 1) admits a cell in the third row and has row difference one.
example :
    let T : Fin 4 → Fin 4 × Fin 4 := ![(0, 0), (1, 0), (2, 0), (0, 1)]
    IsStandardYoungTableau 4 T ∧ IsInTwoOneHook 4 T ∧ HasFirstTwoRowDifference 4 1 T := by
  decide

-- At the smallest admissible size, the two tableaux of size three give two new humps.
example : (motzkinHumpCount 3 1 : ℤ) - (motzkinHumpCount 2 1 : ℤ) = 2 := by
  have h := sytHookCount_add_eq_humpCount_sub 2 1 (by decide) (by decide)
  simpa [sytHookCount_three_one, sytHookCount_two_one] using h.symm

-- At the upper height bound for length four, four prefixes reach height three.
example : sytHookCount 5 3 + sytHookCount 4 3 = 4 := by
  have h := sytHookCount_add_eq_humpCount_sub 4 2 (by decide) (by decide)
  have dh := sytHookCount_add_eq_humpCount_sub.humpCount_succ 4 2 (by decide) (by decide)
  have hw : sytHookCount_add_eq_humpCount_sub.walkCount 4 0 3 = 4 := by decide
  simp only [show 2 * 2 - 1 = 3 by decide, show 4 + 1 = 5 by decide] at h dh
  rw [hw] at dh
  omega

end MetaMathlibExt
