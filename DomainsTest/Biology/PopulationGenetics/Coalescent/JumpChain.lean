/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Coalescent.JumpChain

/-!
# Tests for restriction of Kingman jump chains

These examples check the one-gene boundary, a full three-gene path, and the initial condition.
-/

open Finset
open MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescent
open MathlibExt.Biology.PopulationGenetics.Coalescent.PartitionCoalescentWanted
open scoped Classical

-- Restriction removes the only merger of a two-gene sample.
example :
    ∑ p : Fin 2 → SamplePartition 2
        with ((List.ofFn p).map (Finpartition.comap Fin.castSucc)).destutter (· ≠ ·) = [⊥],
      pathProb 2 (List.ofFn p) = 1 := by
  rw [sum_pathProb_restrict 1 (by decide) [⊥] rfl]
  simp [pathProb, List.zipWith]

-- Each choice of the intermediate two-block partition has probability one third.
example (q : SamplePartition 3) (hq : #q.parts = 2) :
    ∑ p : Fin 4 → SamplePartition 4
        with ((List.ofFn p).map (Finpartition.comap Fin.castSucc)).destutter (· ≠ ·) = [⊥, q, ⊤],
      pathProb 4 (List.ofFn p) = 1 / 3 := by
  have h₁ : Finpartition.IsPairMerge ⊥ q := ⟨bot_le, by simp [hq]⟩
  have h₂ : Finpartition.IsPairMerge q ⊤ := ⟨le_top, by rw [hq]; decide⟩
  rw [sum_pathProb_restrict 3 (by decide) [⊥, q, ⊤] rfl]
  norm_num [pathProb, List.zipWith, Finpartition.pairMergeMatrix_of_merge (by simp) h₁,
    Finpartition.pairMergeMatrix_of_merge hq.ge h₂, hq, Nat.choose]

-- A path must start at the singleton partition, including when its first state is absorbing.
example : pathProb 2 [] = 0 ∧ pathProb 2 [⊤, ⊤] = 0 := by
  have h : (⊤ : SamplePartition 2) ≠ ⊥ := by decide
  simp [pathProb, h]
