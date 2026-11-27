/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasCompanionIdentity

open MetaMathlibExt

example (P : LucasSequenceParams) : lucasV P 1 = lucasU P 2 := by
  simpa [lucasU] using lucasV_eq_lucasU_succ_sub P (n := 1) (by decide)

example : lucasV ⟨0, 2, by decide⟩ 2 = -4 := by
  rw [lucasV_eq_lucasU_succ_sub _ (by decide)]
  decide
