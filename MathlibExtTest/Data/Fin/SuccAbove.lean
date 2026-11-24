/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Data.Fin.SuccAbove

/-!
# Tests for the value of `Fin.succAbove`

Public clients exercise `Fin.val_succAbove` by signature, by
its full dependent type, and by concrete evaluation below, at,
and above the skipped index. Only public declarations are used.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExtTest.Data.Fin.SuccAbove

section Signatures

#check @Fin.val_succAbove

end Signatures

section Evaluations

/-- Below the skipped index, `Fin.succAbove` keeps the value. -/
example : ((2 : Fin 3).succAbove (0 : Fin 2)).val = 0 := by
  rw [Fin.val_succAbove]
  decide

/-- At and above the skipped index, `Fin.succAbove` adds one. -/
example : ((0 : Fin 3).succAbove (0 : Fin 2)).val = 1 := by
  rw [Fin.val_succAbove]
  decide

example : ((1 : Fin 4).succAbove (2 : Fin 3)).val = 3 := by
  rw [Fin.val_succAbove]
  decide

/-- The `Fin.succAbove` value formula, with its full type. -/
example : ∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n),
    (p.succAbove i).val =
      if i.val < p.val then i.val else i.val + 1 :=
  fun p i => Fin.val_succAbove p i

end Evaluations

end MathlibExtTest.Data.Fin.SuccAbove
