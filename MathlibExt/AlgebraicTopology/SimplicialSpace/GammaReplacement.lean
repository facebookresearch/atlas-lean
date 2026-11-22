/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.GammaCompleteSegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyRowConstancy
import MathlibExt.AlgebraicTopology.SimplicialSpace.RowWeakContainment

/-!
# The original complete Segal replacement of a quasicategory

The previously defined Gamma diagram is complete Segal, its original comparison
is Rezk weak, and its chosen zeroth-row comparison followed by the original
row isomorphism is the identity. This is Joyal–Tierney Proposition 4.10.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet.Rezk

/-- The original comparison in every row is its inverse row-zero isomorphism
followed by the canonical zero-to-that-row map. -/
private theorem gammaReplacement_row_eq (Q : SSet.{u}) (n : ℕ) :
    (SimplicialSpace.rowFunctor n).map
        (SimplicialSpace.ofSimplicialObject.map (gammaUnit.app Q)) =
      gammaZerothRowIso.inv.app Q ≫
        (SimplicialSpace.rowZeroTo n).app
          (SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)) := by
  ext m x
  exact congr($(gammaUnit_app Q m (op ⦋n⦌)) x)

/-- Every original row of eta is categorical weak, including row zero. -/
private theorem gammaReplacement_rowwiseCategoricalEquivalence (Q : SSet.{u})
    [Quasicategory Q] :
    SimplicialSpace.rowwiseCategoricalEquivalences
      (SimplicialSpace.ofSimplicialObject.map (gammaUnit.app Q)) := by
  intro n
  rw [gammaReplacement_row_eq]
  exact categoricalEquivalences.comp_mem _ _
    (categoricalEquivalences.of_isIso (gammaZerothRowIso.inv.app Q))
    (SimplicialSpace.categoricallyConstant_of_completeSegalSpaces _
      (gammaDiagram_completeSegalSpaces Q) n)

/-- Gamma is the complete Segal replacement of a quasicategory, with its
original Rezk-weak comparison and the chosen row-zero identity. -/
theorem gammaDiagram_replacement (Q : SSet.{u}) [Quasicategory Q] :
    SimplicialSpace.completeSegalSpaces
        (SimplicialSpace.ofSimplicialObject.obj (gammaDiagram.obj Q)) ∧
      SimplicialSpace.rezkWeakEquivalences
        (SimplicialSpace.ofSimplicialObject.map (gammaUnit.app Q)) ∧
      (zerothRowAdjunction.unit.app Q ≫ zerothRow.map (gammaUnit.app Q) ≫
        gammaZerothRowIso.hom.app Q = 𝟙 Q) := by
  exact ⟨gammaDiagram_completeSegalSpaces Q,
    SimplicialSpace.rowwiseCategoricalEquivalences_le_rezkWeakEquivalences _
      (gammaReplacement_rowwiseCategoricalEquivalence Q), gammaUnit_row_hom Q⟩

end SSet.Rezk
