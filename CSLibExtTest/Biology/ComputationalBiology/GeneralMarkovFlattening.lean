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
# Tests for edge-flattening rank bounds

* The two-state corollary of `rank_flatten_leafDist_le`: edge flattenings in the two-state
  general Markov model have rank at most two.
* The moved model definitions unfold as stated.
-/

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

end CSLibExtTest.Biology.ComputationalBiology.GeneralMarkovFlattening
