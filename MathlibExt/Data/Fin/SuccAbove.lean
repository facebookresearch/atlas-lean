/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Data.Fin.SuccPred

/-!
# The value of `Fin.succAbove`

The value-level formula for `Fin.succAbove`: embedding
`i : Fin n` into `Fin (n + 1)` with a hole at `p` leaves the
value unchanged below `p` and adds one at and above `p`.
Mathlib characterises `Fin.succAbove` through
`Fin.succAbove_of_castSucc_lt` and `Fin.succAbove_of_le_castSucc`,
but has no single `Fin.val` formula; `Fin.val_succAbove` is
that formula, in the form consumed by simplicial face
computations (where a face index is reindexed by `succAbove`).
-/

@[expose] public section

namespace Fin

variable {n : ℕ}

/-- Value of `Fin.succAbove` on `Fin.val`: `i.val` below the
hole `p`, and `i.val + 1` at and above it. -/
lemma val_succAbove (p : Fin (n + 1)) (i : Fin n) :
    (p.succAbove i).val =
      if i.val < p.val then i.val else i.val + 1 := by
  by_cases h : i.val < p.val
  · have hlt : i.castSucc < p := by
      rw [Fin.lt_def, Fin.val_castSucc]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
    simp only [Fin.val_castSucc, h, ↓reduceIte]
  · have hle : p ≤ i.castSucc := by
      rw [Fin.le_def, Fin.val_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    simp only [Fin.val_succ, h, ↓reduceIte]

end Fin
