/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.Equivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.CocartesianEquivalence

/-!
# The original degenerate edges lie in both relative edge classes

The actual identity edge represents an equivalence. The relative
equivalence-edge lifting theorems therefore put each original degenerate
one-simplex in both specified slice conditions.
-/

noncomputable section
universe u

open CategoryTheory
open scoped Simplicial

namespace SSet

variable {X B : SSet.{u}} (p : X ⟶ B) [InnerFibration p] [Quasicategory B]

/-- Every original degenerate edge is p-cartesian over a genuine quasicategory base. -/
theorem CartesianEdge.isPCartesian_degenerate (x : X _⦋0⦌) :
    CartesianEdge.IsPCartesian p (yonedaEquiv.symm (X.σ (0 : Fin 1) x)) := by
  apply CartesianEdge.isPCartesian_of_isEquivalence
  have he := (Edge.isEquivalence_iff_of_edge_eq (show
    (Edge.mk' (X.σ (0 : Fin 1) x)).edge = (Edge.id x).edge from rfl)).mpr
      (Edge.isEquivalence_id x)
  exact (Equiv.apply_symm_apply yonedaEquiv (X.σ (0 : Fin 1) x)).symm ▸ he

/-- Every original degenerate edge is p-cocartesian over a genuine quasicategory base. -/
theorem CocartesianEdge.isPCocartesian_degenerate (x : X _⦋0⦌) :
    CocartesianEdge.IsPCocartesian p (yonedaEquiv.symm (X.σ (0 : Fin 1) x)) := by
  apply CocartesianEdge.isPCocartesian_of_isEquivalence
  have he := (Edge.isEquivalence_iff_of_edge_eq (show
    (Edge.mk' (X.σ (0 : Fin 1) x)).edge = (Edge.id x).edge from rfl)).mpr
      (Edge.isEquivalence_id x)
  exact (Equiv.apply_symm_apply yonedaEquiv (X.σ (0 : Fin 1) x)).symm ▸ he

end SSet
