/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MisereCubeFaceNim

/-! # Tests for misère face Nim on a cube -/

open MetaMathlibExt

variable (P : Set (Fin 6 → ℕ))
  (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)

-- No player is forced to take the last token on an already empty cube.
example : ![0, 0, 0, 0, 0, 0] ∉ P := fun hp => (by decide : ¬ _) <|
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- A single token loses, while two tokens on the same face allow a winning move.
example : ![0, 0, 0, 0, 0, 1] ∈ P :=
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

example : ![0, 0, 0, 0, 0, 2] ∉ P := fun hp => (by decide : ¬ _) <|
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- The three nonempty heaps have distinct sizes and zero nim-sum.
example : ![0, 0, 0, 1, 2, 3] ∈ P :=
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)
