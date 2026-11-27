/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.BergeLemma

/-! Non-vacuity tests for augmenting walks and Hopcroft–Karp's Lemma 1. -/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.AugmentingWalkTests

/-- The single edge of the complete graph on two vertices, as a walk. -/
private def edgeWalk : (⊤ : SimpleGraph (Fin 2)).Walk 0 1 :=
  SimpleGraph.Walk.cons (by decide : (⊤ : SimpleGraph (Fin 2)).Adj 0 1) SimpleGraph.Walk.nil

private theorem edgeWalk_isAugmenting : IsAugmentingWalk (∅ : Finset (Sym2 (Fin 2))) edgeWalk :=
  ⟨by decide, by decide, by simp, by simp, by simp [edgeWalk], by simp [edgeWalk]⟩

/-- Augmenting the empty matching along the edge gives a matching with one edge. -/
example : (symmDiff (∅ : Finset (Sym2 (Fin 2))) edgeWalk.edges.toFinset).card = 1 :=
  (edgeWalk_isAugmenting.symmDiff_isMatching (by simp) (by simp)).2.2

/-- The empty matching is not maximum: an augmenting walk exists. -/
example : ¬ ∀ M' : Finset (Sym2 (Fin 2)), (∀ e ∈ M', e ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet) →
    (∀ e₁ ∈ M', ∀ e₂ ∈ M', e₁ ≠ e₂ → ∀ v : Fin 2, v ∈ e₁ → v ∉ e₂) →
      M'.card ≤ (∅ : Finset (Sym2 (Fin 2))).card := by
  rw [berge_iff_not_exists_isAugmentingWalk _ _ (by simp) (by simp), not_not]
  exact ⟨0, 1, edgeWalk, edgeWalk_isAugmenting⟩

end MetaMathlibExt.AugmentingWalkTests
