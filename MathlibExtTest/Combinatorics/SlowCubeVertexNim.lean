/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SlowCubeVertexNim

/-! # Tests for slow vertex Nim on a cube -/

open MetaMathlibExt

-- Opposite piles can have unequal sizes in a P-position, including when both sizes are odd.
example :
    let p : Fin 6 → ℕ := ![1, 4, 0, 3, 0, 0]
    ∀ q, CubeVertexMove p q → (∀ k, p k ≤ q k + 1) →
      ¬ ((q 0 + q 3) % 2 = 0 ∧ (q 1 + q 4) % 2 = 0 ∧ (q 2 + q 5) % 2 = 0) := by
  intro p q hm hslow
  exact slowCubeVertexNim_pPositions.1 p q (by decide) ⟨hm, hslow⟩

-- All three pairs need a change, and the empty opposite faces force the choice of vertex.
example :
    let p : Fin 6 → ℕ := ![3, 0, 1, 0, 5, 0]
    ∃ q, (CubeVertexMove p q ∧ ∀ k, p k ≤ q k + 1) ∧
      (q 0 + q 3) % 2 = 0 ∧ (q 1 + q 4) % 2 = 0 ∧ (q 2 + q 5) % 2 = 0 := by
  intro p
  apply slowCubeVertexNim_pPositions.2
  decide
