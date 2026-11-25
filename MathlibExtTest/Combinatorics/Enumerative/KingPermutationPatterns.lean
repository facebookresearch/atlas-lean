/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import MathlibExt.Combinatorics.Enumerative.KingPermutationPatterns

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

private def king {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = i + 1 → (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (king σ) := by
  unfold king
  infer_instance

example : ¬ ∃ σ : Equiv.Perm (Fin 2), king σ := by decide
example : ¬ ∃ σ : Equiv.Perm (Fin 3), king σ := by decide

-- The one-line permutation 2413, with zero-based values.
private def smallKing : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

example : HasPattern smallKing ![0, 1] ∧ HasPattern smallKing ![1, 0] ∧
    HasPattern smallKing ![0, 2, 1] ∧ HasPattern smallKing ![1, 0, 2] ∧
    HasPattern smallKing ![1, 2, 0] ∧ HasPattern smallKing ![2, 0, 1] :=
  MetaMathlibExt.king_permutation_hasPattern_classical 4 (by decide) smallKing (by decide)
