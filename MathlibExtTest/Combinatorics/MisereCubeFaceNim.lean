/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MisereCubeFaceNim

open MetaMathlibExt

variable (P : Set (Fin 6 → ℕ))
  (hP : ∀ p, p ∈ P ↔ (∃ q, CubeFaceMove p q) ∧ ∀ q, CubeFaceMove p q → q ∉ P)

-- The terminal position wins, but a single one loses.
example : ![0, 0, 0, 0, 0, 0] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

example : ![0, 0, 0, 0, 0, 1] ∈ P :=
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

-- Three unit heaps lose, while two unit heaps win.
example : ![0, 0, 0, 1, 1, 1] ∈ P :=
  (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

example : ![0, 0, 0, 0, 1, 1] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- A single large heap wins whether the other heaps have zero or one token.
example : ![0, 0, 0, 0, 0, 2] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

example : ![0, 0, 0, 0, 1, 2] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

-- With two large heaps, unequal sizes win and equal sizes lose.
example : ![0, 0, 0, 0, 2, 3] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeFaceNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

example : ![0, 0, 0, 0, 3, 3] ∈ P :=
  (cubeFaceNim_misere_pPositions (P := P) (hP := hP) (p := ![0, 0, 0, 0, 3, 3])
    (hC := by decide) (ha := by decide) (hb := by decide) (hab := by decide)).2 (by decide)
