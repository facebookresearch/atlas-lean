/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SlowCubeFaceNim

/-! # Tests for slow face Nim on a cube -/

open MetaMathlibExt

-- Two odd piles give an even total, and every slow move breaks that parity.
example :
    let p : Fin 6 → ℕ := ![1, 0, 0, 3, 0, 0]
    ∀ q, CubeFaceMove p q → (∀ k, p k ≤ q k + 1) → (∑ k, q k) % 2 ≠ 0 := by
  intro p q hm hslow
  exact slowCubeFaceNim_pPositions.1 p q (by decide) ⟨hm, hslow⟩

-- A single token on the last face admits a slow move to an even total.
example :
    let p : Fin 6 → ℕ := ![0, 0, 0, 0, 0, 1]
    ∃ q, (CubeFaceMove p q ∧ ∀ k, p k ≤ q k + 1) ∧ (∑ k, q k) % 2 = 0 := by
  intro p
  apply slowCubeFaceNim_pPositions.2
  decide
