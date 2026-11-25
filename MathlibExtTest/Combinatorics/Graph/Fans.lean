/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.Fans

/-!
# Tests for the fan construction

* Zero-fan boundary: every graph is `0`-vertex-connected, so the fan
  theorem yields a `0`-fan and the `0` separator bound.
* Positive example: the complete graph on `Fin 3` is `1`-vertex-connected,
  so every vertex sends a `1`-fan to every set of at least one vertex not
  containing it, and every separator of such a set has size at least one.
-/

namespace MathlibExtTest.Combinatorics.Graph.Fans

open MathlibExt.Combinatorics.Graph.Fans

/-- Every graph is `0`-vertex-connected: the deletion condition is vacuous. -/
private theorem isVertexConnected_zero (G : SimpleGraph (Fin 2)) :
    G.IsVertexConnected 0 := by
  refine SimpleGraph.isVertexConnected_iff.mpr ⟨by decide, fun S hS => ?_⟩
  exact absurd hS (Nat.not_lt_zero _)

/-- The complete graph on `Fin 3` is `1`-vertex-connected. -/
private theorem isVertexConnected_one_completeGraph :
    (⊤ : SimpleGraph (Fin 3)).IsVertexConnected 1 := by
  refine SimpleGraph.isVertexConnected_iff.mpr ⟨by decide, fun S hS => ?_⟩
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hS)
  subst hS0
  have huniv : (↑(∅ : Finset (Fin 3)) : Set (Fin 3))ᶜ = Set.univ := by simp
  rw [huniv]
  exact (SimpleGraph.induceUnivIso _).connected_iff.mpr
    SimpleGraph.connected_top

/-- Zero-fan boundary: a `0`-fan exists from any vertex to the empty set. -/
example (G : SimpleGraph (Fin 2)) (a : Fin 2) :
    Nonempty (Fan G a (↑(∅ : Finset (Fin 2))) 0) :=
  exists_fan_of_isVertexConnected (isVertexConnected_zero G) a ∅ (by simp)
    (by simp)

/-- Zero separator bound: the `0` bound holds for any separator. -/
example (G : SimpleGraph (Fin 2)) (a : Fin 2) (C : Finset (Fin 2))
    (hC : SeparatesVertexFromSet G a (↑(∅ : Finset (Fin 2))) C) :
    0 ≤ C.card :=
  separator_card_ge_of_isVertexConnected (isVertexConnected_zero G) a ∅
    (by simp) (by simp) C hC

/-- Positive example: a `1`-fan from `0` to `{1, 2}` in the complete graph. -/
example : Nonempty (Fan (⊤ : SimpleGraph (Fin 3)) 0
    (↑({1, 2} : Finset (Fin 3))) 1) :=
  exists_fan_of_isVertexConnected isVertexConnected_one_completeGraph 0
    {1, 2} (by decide) (by decide)

/-- Positive separator bound: every separator of `{1, 2}` from `0` is nonempty. -/
example (C : Finset (Fin 3))
    (hC : SeparatesVertexFromSet (⊤ : SimpleGraph (Fin 3)) 0
      (↑({1, 2} : Finset (Fin 3))) C) :
    1 ≤ C.card :=
  separator_card_ge_of_isVertexConnected isVertexConnected_one_completeGraph 0
    {1, 2} (by decide) (by decide) C hC

end MathlibExtTest.Combinatorics.Graph.Fans
