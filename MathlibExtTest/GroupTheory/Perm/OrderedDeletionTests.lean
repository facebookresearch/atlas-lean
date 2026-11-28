/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.Perm.OrderedDeletion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Sorted deletion and endpoint signs on four letters

Inserting value one before reversal of three letters gives (1,3,2,0). Deleting the first
value recovers that reversal in ascending remaining-value coordinates. Moving the insertion
to the last position changes the sign from +1 to -1 in this odd remaining degree.
-/

noncomputable section

namespace OrderedDeletionTests

open Equiv.Perm

private theorem inserted_four :
    orderedFirst (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2) =
      Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 3 := by
  apply Equiv.ext
  intro i
  fin_cases i
  · simpa [mul_apply, Equiv.swap_apply_def] using
      orderedFirst_zero (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2)
  · simpa [mul_apply, Equiv.swap_apply_def, Fin.succAbove] using
      orderedFirst_succ (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2) (0 : Fin 3)
  · simpa [mul_apply, Equiv.swap_apply_def, Fin.succAbove] using
      orderedFirst_succ (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2) (1 : Fin 3)
  · simpa [mul_apply, Equiv.swap_apply_def, Fin.succAbove] using
      orderedFirst_succ (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2) (2 : Fin 3)

example : (orderedFirstEquiv 3).symm
    (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (1 : Fin 4) 3) =
      ((1 : Fin 4), Equiv.swap (0 : Fin 3) 2) := by
  rw [← inserted_four, ← orderedFirstEquiv_apply]
  exact (orderedFirstEquiv 3).symm_apply_apply _

example : (orderedLast (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2)) (Fin.last 3) = 1 := by
  exact orderedLast_last _ _

example : ((orderedFirst (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2)).sign : ℤ) = 1 ∧
    ((orderedLast (1 : Fin 4) (Equiv.swap (0 : Fin 3) 2)).sign : ℤ) = -1 := by
  constructor <;> norm_num [sign_orderedFirst_int, sign_orderedLast_int]

example : orderedFirst (0 : Fin 1) (1 : Equiv.Perm (Fin 0)) = 1 ∧
    orderedLast (0 : Fin 1) (1 : Equiv.Perm (Fin 0)) = 1 := by
  constructor <;> exact Subsingleton.elim _ _

end OrderedDeletionTests
