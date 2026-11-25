/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasCompanionSquare

open MetaMathlibExt

example (P : LucasSequenceParams) : lucasV P 0 ^ 2 = 4 := by
  rw [lucasV_sq_eq]
  simp [lucasU]

example (P : LucasSequenceParams) : lucasV P 1 ^ 2 = P.p ^ 2 := by
  rw [lucasV_sq_eq]
  simp [lucasU]

-- Positive q with negative discriminant.
example : lucasV ⟨1, 2, by decide⟩ 4 ^ 2 = 1 := by
  rw [lucasV_sq_eq]
  decide

-- Negative q at an odd index, so the Cassini contribution is negative.
example : lucasV ⟨-2, -3, by decide⟩ 3 ^ 2 = 676 := by
  rw [lucasV_sq_eq]
  decide
