/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Biology.ComputationalBiology.GeneralMarkovFlattening
public import Mathlib.Data.Fintype.Card

/-!
# Tests for edge- and non-edge-flattening rank bounds

* The two-state corollary of `rank_flatten_leafDist_le`: edge flattenings in the two-state
  general Markov model have rank at most two.
* The moved model definitions unfold as stated.
* Corollaries of `exists_card_lt_rank_flatten_nonEdge` (Allman and Rhodes 2006, Theorem 2):
  the two-state specialization, where some complex stochastic parameters give rank larger
  than two, and the successor form, where the rank is at least `κ + 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExtTest.Biology.ComputationalBiology.GeneralMarkovFlattening

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits
open WantedExt.Biology.ComputationalBiology.GeneralMarkovFlatteningWanted

/-- Edge flattenings in the two-state general Markov model have rank at most two. -/
theorem rank_flatten_two_state_le_two {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (r : T.V)
    (π : Fin 2 → ℝ) (M : T.V → T.V → Matrix (Fin 2) (Fin 2) ℝ)
    (hp : IsStochastic T.G r π M) {A : Finset X} (hA : A ∈ edgeSplits T) :
    (flatten A (leafDist T.G (leafOf T) r π M)).rank ≤ 2 := by
  have h := rank_flatten_leafDist_le T r π M hp hA
  simpa using h

/-- The directed-away relation unfolds to adjacency plus a distance step. -/
example {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r a b : V) :
    IsAwayFrom G r a b ↔ G.Adj a b ∧ G.dist r b = G.dist r a + 1 := Iff.rfl

/-- Two-state specialization: some complex stochastic parameters give a non-edge
flattening of rank larger than two. -/
theorem exists_rank_gt_two_fin2 (T : UnrootedBinaryTree (Fin 4))
    (hT : DisplaysQuartet T 0 1 2 3) (A : Finset (Fin 4))
    (hA : A = {0, 2} ∨ A = {0, 3}) :
    ∃ (r : T.V) (π : Fin 2 → ℂ) (M : T.V → T.V → Matrix (Fin 2) (Fin 2) ℂ),
      IsComplexStochastic T.G r π M ∧
        2 < (flatten A (leafDist T.G (leafOf T) r π M)).rank := by
  have hK : 2 ≤ Fintype.card (Fin 2) := by decide
  obtain ⟨r, π, M, hp, hrank⟩ :=
    exists_card_lt_rank_flatten_nonEdge (K := Fin 2) hK T hT A hA
  have hcard : Fintype.card (Fin 2) = 2 := by decide
  rw [hcard] at hrank
  exact ⟨r, π, M, hp, hrank⟩

/-- Successor form: some complex stochastic parameters give a non-edge flattening
of rank at least `κ + 1`. -/
theorem exists_succ_le_rank {K : Type} [Fintype K] [DecidableEq K]
    (hK : 2 ≤ Fintype.card K) (T : UnrootedBinaryTree (Fin 4))
    (hT : DisplaysQuartet T 0 1 2 3) (A : Finset (Fin 4))
    (hA : A = {0, 2} ∨ A = {0, 3}) :
    ∃ (r : T.V) (π : K → ℂ) (M : T.V → T.V → Matrix K K ℂ),
      IsComplexStochastic T.G r π M ∧
        Fintype.card K + 1 ≤ (flatten A (leafDist T.G (leafOf T) r π M)).rank := by
  obtain ⟨r, π, M, hp, hrank⟩ := exists_card_lt_rank_flatten_nonEdge hK T hT A hA
  exact ⟨r, π, M, hp, Nat.succ_le_of_lt hrank⟩

end CSLibExtTest.Biology.ComputationalBiology.GeneralMarkovFlattening
