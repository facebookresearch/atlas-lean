/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Matching.GallaiEdmonds
public import MathlibExt.Combinatorics.Matching.MaximumMatching

/-!
# Tests for the Gallai–Edmonds decomposition

* Factor-criticality of subsingleton graphs and the odd-order consequence.
* The `D`/`A`/`C` partition facts (pairwise disjointness) on concrete graphs.
* Deficiency expressed through any maximum matching, and the Tutte–Berge
  bound applied to a concrete matching and vertex set.
-/

namespace MathlibExtTest.Combinatorics.Matching.GallaiEdmonds

open MathlibExt.Combinatorics.Matching
open MathlibExt.Combinatorics.Matching.GallaiEdmonds

/-- A subsingleton graph is factor-critical: deleting the only vertex leaves
the empty graph, which has the empty perfect matching. -/
example : IsFactorCritical (⊥ : SimpleGraph (Fin 1)) :=
  isFactorCritical_of_subsingleton _

/-- Factor-criticality forces odd order, here `Nat.card (Fin 1) = 1`. -/
example : Odd (Nat.card (Fin 1)) :=
  (isFactorCritical_of_subsingleton (⊥ : SimpleGraph (Fin 1))).odd_card

/-- The `D` and `C` sets are disjoint, on the empty graph. -/
example : Disjoint (gallaiD (⊥ : SimpleGraph (Fin 2)))
    (gallaiC (⊥ : SimpleGraph (Fin 2))) :=
  disjoint_gallaiD_gallaiC _

/-- The `D` and `A` sets are disjoint, on the empty graph. -/
example : Disjoint (gallaiD (⊥ : SimpleGraph (Fin 2)))
    (gallaiA (⊥ : SimpleGraph (Fin 2))) :=
  disjoint_gallaiD_gallaiA _

/-- The `A` and `C` sets are disjoint, on the complete graph. -/
example : Disjoint (gallaiA (⊤ : SimpleGraph (Fin 2)))
    (gallaiC (⊤ : SimpleGraph (Fin 2))) :=
  disjoint_gallaiA_gallaiC _

/-- Deficiency through any maximum matching, applied to the maximum matching
whose existence the API provides. -/
example : matchingDeficiency (⊥ : SimpleGraph (Fin 2)) = Nat.card (Fin 2) -
    2 * (Classical.choose
      (exists_maximum_matching (⊥ : SimpleGraph (Fin 2)))).edgeSet.ncard :=
  deficiency_eq_of_isMaximum _ (Classical.choose_spec _)

/-- The Tutte–Berge bound: odd components after deleting `u` are bounded by
the exposed vertices plus `u`, for the empty matching on the empty graph. -/
example (u : Set (Fin 2)) :
    (((⊤ : (⊥ : SimpleGraph (Fin 2)).Subgraph).deleteVerts u).coe).oddComponents.ncard ≤
      ((⊥ : (⊥ : SimpleGraph (Fin 2)).Subgraph).vertsᶜ).ncard + u.ncard := by
  apply tutteBerge_odd_le
  intro v hv
  simp at hv

end MathlibExtTest.Combinatorics.Matching.GallaiEdmonds
