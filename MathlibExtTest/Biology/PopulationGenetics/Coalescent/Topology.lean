/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.Topology

/-!
# Tests for ranked labeled histories under random joining

Counts for small samples (`1, 1, 3, 18, 180` histories for `n = 1, …, 5`), the probability
`1/3` of each history of three genes, the decoding of histories into ancestral partitions
(injective for `n = 3, 4, 5`, ending in the one-block partition), and the boundary cases
`n = 0, 1`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped Nat

namespace MathlibExtTest.Biology.PopulationGenetics.Coalescent.Topology

open MathlibExt.Biology.PopulationGenetics.Coalescent

/-- Small counts: `∏_{k=2}^n C(k, 2)` is `1, 1, 3, 18, 180` for `n = 1, …, 5`. -/
example : Fintype.card (RankedHistory 1) = 1 ∧ Fintype.card (RankedHistory 2) = 1 ∧
    Fintype.card (RankedHistory 3) = 3 ∧ Fintype.card (RankedHistory 4) = 18 ∧
    Fintype.card (RankedHistory 5) = 180 := by
  simp only [card_rankedHistory]
  decide

/-- Edwards' count `n! (n - 1)! / 2^{n-1}` for `n = 6`: `6! 5! / 32 = 2700`. -/
example : Fintype.card (RankedHistory 6) = 2700 ∧ 2700 * 2 ^ 5 = (6 : ℕ).factorial * 5! := by
  refine ⟨?_, by decide⟩
  rw [card_rankedHistory]
  decide

/-- Three genes: each of the three histories has probability `1/3`. -/
example (h : RankedHistory 3) : randomJoining 3 {h} = 1 / 3 := by
  rw [randomJoining_singleton]
  norm_num [Nat.factorial]
  rw [show (4 : ENNReal) = 4 * 1 by ring, show (12 : ENNReal) = 4 * 3 by norm_num,
    ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num), one_div]

/-- Two genes: the unique history has probability one. -/
example (h : RankedHistory 2) : randomJoining 2 {h} = 1 := by
  rw [randomJoining_singleton]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Boundary case `n = 0` (no coalescence): one empty history, of probability one. -/
example (h : RankedHistory 0) : randomJoining 0 {h} = 1 := by
  rw [randomJoining_singleton]
  norm_num

/-- The decoding into ancestral partitions is injective for three genes. -/
example : Function.Injective (partitionsOf (n := 3)) := by
  decide +kernel

/-- The decoding into ancestral partitions is injective for four genes. -/
example : Function.Injective (partitionsOf (n := 4)) := by
  decide +kernel

/-- The decoding into ancestral partitions is injective for five genes (180 histories). -/
example : Function.Injective (partitionsOf (n := 5)) := by
  decide +kernel

/-- Every history of four genes starts from the singletons and ends at one block. -/
example : ∀ h : RankedHistory 4,
    (partitionsOf h).head? = some (univ.image fun j : Fin 4 => {j}) ∧
      (partitionsOf h).getLast? = some {univ} := by
  decide +kernel

end MathlibExtTest.Biology.PopulationGenetics.Coalescent.Topology
