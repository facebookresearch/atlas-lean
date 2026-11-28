/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MisereCubeVertexNim

open MetaMathlibExt

variable (P : Set (Fin 6 → ℕ))
  (hP : ∀ p, p ∈ P ↔ (∃ q, CubeVertexMove p q) ∧ ∀ q, CubeVertexMove p q → q ∉ P)

-- The empty cube wins under misère play; a singleton loses.
example : ![0, 0, 0, 0, 0, 0] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

example : ![0, 0, 0, 0, 0, 1] ∈ P :=
  (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

-- One opposite unit pair wins, while two or three such pairs lose.
example : ![0, 0, 1, 0, 0, 1] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp

example : ![0, 1, 1, 0, 1, 1] ∈ P :=
  (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

example : ![1, 1, 1, 1, 1, 1] ∈ P :=
  (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

-- An opposite pair of twos loses, but unbalancing it changes the result.
example : ![0, 0, 2, 0, 0, 2] ∈ P :=
  (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).2
    (by decide)

example : ![0, 0, 2, 0, 0, 3] ∉ P :=
  fun hp => (by decide : ¬ _) <|
    (cubeVertexNim_misere_pPositions P hP _ (by decide) (by decide) (by decide) (by decide)).1 hp
