/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MisereCubeRotationNim

/-! # Tests for misère rotation Nim on a cube -/

open MetaMathlibExt

variable (P : Set (Fin 6 → ℕ))
  (hP : ∀ p, p ∈ P ↔ (∃ q, CubeRotationMove p q) ∧ ∀ q, CubeRotationMove p q → q ∉ P)

-- With just one token the player to move must take the last token.
example : ![0, 0, 0, 0, 0, 1] ∈ P :=
  (cubeRotationNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

-- Equal pair totals of one allow a move leaving a single token.
example : ![0, 0, 0, 1, 1, 1] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeRotationNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- Equal pair totals of two lose both on the all-ones cube and with a mixture of split
-- and concentrated pairs.
example : ![1, 1, 1, 1, 1, 1] ∈ P :=
  (cubeRotationNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

example : ![0, 1, 0, 2, 1, 2] ∈ P :=
  (cubeRotationNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)
