/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.MatchingCutGirth

@[expose] public section

namespace MathlibExt.Combinatorics.MatchingCutGirthWanted

example : ¬ conjecture := conjecture_refuted

/-- The negative answer in the form stated in the docstring of `conjecture_refuted`: one real
number `d` works for every `g`. -/
example : ∃ d : ℝ, ∀ g : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : Nontrivial V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    (avgDegree G : ℝ) < d ∧ (g : ℕ∞) ≤ G.egirth ∧ ¬ HasMatchingCut G := by
  by_contra h
  refine conjecture_refuted.{0} fun d => ?_
  obtain ⟨g, hg⟩ := Classical.not_forall.mp fun hall => h ⟨d, hall⟩
  refine ⟨g, fun V i₁ i₂ i₃ G i₄ havg hgirth => ?_⟩
  by_contra hcut
  exact hg ⟨V, i₁, i₂, i₃, G, i₄, havg, hgirth, hcut⟩

/-- The complete graph on three vertices has average degree `2`. -/
example : avgDegree (⊤ : SimpleGraph (Fin 3)) = 2 := by
  rw [avgDegree, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  norm_num

/-- The empty graph has average degree `0`. -/
example : avgDegree (⊥ : SimpleGraph (Fin 3)) = 0 := by
  simp [avgDegree]

/-- A disconnected graph has a matching cut, with the empty matching. -/
example : HasMatchingCut (⊥ : SimpleGraph (Fin 2)) :=
  ⟨⊥, fun v hv => by simp at hv, 0, 1, by simp⟩

/-- A graph with a single vertex has no matching cut; this is why `conjecture` only considers
graphs with at least two vertices. -/
example : ¬ HasMatchingCut (⊥ : SimpleGraph (Fin 1)) := by
  rintro ⟨M, -, u, v, h⟩
  exact h (Subsingleton.elim u v ▸ SimpleGraph.Reachable.refl u)

end MathlibExt.Combinatorics.MatchingCutGirthWanted
