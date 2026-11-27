/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleCycleRefinement

open Equiv Equiv.Perm MetaMathlibExt

private def digits : Fin 4 → ℕ := ![2, 1, 3, 3]

private def fourCycle : Perm (Fin 4) := swap 0 1 * swap 0 3 * swap 0 2

-- Holt's example (3312)₄ = 2 · (1323)₄ starts with a repeated digit in one cycle.
example : digits (fourCycle 2) = digits 2 ∧ fourCycle 2 ≠ 2 := by decide

example : ∃ τ : Perm (Fin 4), IsPermutiple 2 4 digits τ ∧
    ∀ (j : Fin 4) (i : ℕ), digits ((τ ^ i) j) = digits j → (τ ^ i) j = j :=
  exists_cyclePreserving_permutiple 2 4 digits fourCycle (by unfold IsPermutiple; decide)

-- The result does not need the paper's strict bounds on the multiplier and base.
example : ∃ τ : Perm (Fin 2), IsPermutiple 0 1 (fun _ => 0) τ ∧
    ∀ (j : Fin 2) (i : ℕ), (τ ^ i) j = j := by
  obtain ⟨τ, hτ, hcycle⟩ := exists_cyclePreserving_permutiple 0 1
    (fun _ : Fin 2 => 0) (swap 0 1) (by unfold IsPermutiple; decide)
  exact ⟨τ, hτ, fun j i => hcycle j i rfl⟩
