/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SlowCubeEdgeNim

/-! # Tests for slow edge Nim on a cube -/

open MetaMathlibExt

-- All three opposite-pair totals are odd, with tokens on both faces of the middle pair.
example :
    let p : Fin 6 → ℕ := ![0, 2, 0, 1, 1, 3]
    ∀ q, CubeEdgeMove p q → (∀ k, p k ≤ q k + 1) →
      ¬ ((q 0 + q 3) % 2 = (q 1 + q 4) % 2 ∧ (q 1 + q 4) % 2 = (q 2 + q 5) % 2) := by
  intro p q hm hslow
  exact slowCubeEdgeNim_pPositions.1 p q (by decide) ⟨hm, hslow⟩

-- With one token on each of two adjacent faces, only emptying both restores equal parities.
example :
    let p : Fin 6 → ℕ := ![0, 1, 0, 1, 0, 0]
    ∃ q, (CubeEdgeMove p q ∧ ∀ k, p k ≤ q k + 1) ∧
      (q 0 + q 3) % 2 = (q 1 + q 4) % 2 ∧ (q 1 + q 4) % 2 = (q 2 + q 5) % 2 := by
  intro p
  apply slowCubeEdgeNim_pPositions.2
  decide
