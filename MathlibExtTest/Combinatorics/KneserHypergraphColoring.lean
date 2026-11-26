/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.KneserHypergraphColoring

namespace MathlibExt.Combinatorics.KneserHypergraphColoringErdosProblem780Wanted

open Finset

-- At the threshold, every two-coloring of the pairs on eight vertices has a matching of size three.
example (c : Finset (Fin 8) → Fin 2) :
    ∃ (i : Fin 2) (E : Finset (Finset (Fin 8))), E ⊆ univ.powersetCard 2 ∧
      E.card = 3 ∧ (∀ e ∈ E, c e = i) ∧ (E : Set (Finset (Fin 8))).PairwiseDisjoint id :=
  kneserHypergraphColoring_holds 8 3 2 2 (by decide) (by decide) (by decide) c

-- One vertex below the singleton threshold, splitting four vertices into two pairs avoids a triple.
private def splitColor (s : Finset (Fin 4)) : Fin 2 := if s ⊆ {0, 1} then 0 else 1

example : ∀ E ∈ ((univ : Finset (Fin 4)).powersetCard 1).powersetCard 3,
    ∀ i : Fin 2, ¬ ∀ e ∈ E, splitColor e = i := by decide

-- A matching of size zero exists even when there are no vertices and there are several colors.
example (c : Finset (Fin 0) → Fin 3) :
    ∃ (i : Fin 3) (E : Finset (Finset (Fin 0))), E = ∅ ∧ ∀ e ∈ E, c e = i := by
  obtain ⟨i, E, _, hcard, hc, _⟩ :=
    kneserHypergraphColoring_holds 0 0 1 3 (by decide) (by decide) (by decide) c
  exact ⟨i, E, card_eq_zero.mp hcard, hc⟩

end MathlibExt.Combinatorics.KneserHypergraphColoringErdosProblem780Wanted
