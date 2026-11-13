/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.Knapsack
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: with one item of weight 1 and profit 5,
capacity 1, scaling factor 1, the theorem yields a feasible set
within `1 * 1` of the optimum. -/
example : ∃ S : Finset (Fin 1), (∑ i ∈ S, ((fun _ => 1) : Fin 1 → ℕ) i) ≤ 1 ∧
    optVal ((fun _ => 1) : Fin 1 → ℕ) ((fun _ => 5) : Fin 1 → ℕ) 1 ≤
      (∑ i ∈ S, ((fun _ => 5) : Fin 1 → ℕ) i) + 1 := by
  obtain ⟨S, hW, -, hloss⟩ :=
    knapsack_scaling_loss ((fun _ => 1) : Fin 1 → ℕ) ((fun _ => 5) : Fin 1 → ℕ) 1 1 (by norm_num)
  exact ⟨S, hW, hloss⟩
