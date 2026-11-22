/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientModel
import MathlibExt.AlgebraicTopology.SimplicialSet.CartesianEdge.EquivalenceReflection
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativePrisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Original fibrant coefficients have their exact equivalence marking

The actual transported coefficient model sends its original terminal
arrow to the genuine point-slice model. Its intrinsic Cartesian fibrancy
therefore detects precisely the equivalence edges of the unchanged
coefficient simplicial set. No saturated marking or fibrancy outcome is
supplied as an input; the only hypothesis is actual coefficient-model
fibrancy.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked
attribute [local instance] coefficientMarkedModelCategory

/-- The actual coefficient-model terminal fibration gives intrinsic fibrancy of the SAME coefficient in the original
point slice. -/
theorem coefficientFibrant_point_intrinsic (A : Marked.{u}) (hA : IsFibrant A) :
    cartesianObjects (Δ[0] : SSet.{u}) (coefficientPointEquivalence.functor.obj A) := by
  let _ := cartesianMarkedFibrationStructure (Δ[0] : SSet.{u})
  let _ : (fibrations (Over (max (Δ[0] : SSet.{u})))).RespectsIso := by
    change (cartesianTestingFibrations (Δ[0] : SSet.{u})).RespectsIso
    unfold cartesianTestingFibrations
    infer_instance
  let E := coefficientPointEquivalence.{u}
  have hf : fibrations (Over (max (Δ[0] : SSet.{u})))
      (E.functor.map (terminal.from A)) := (fibration_iff (terminal.from A)).mp hA
  have ht : IsTerminal (E.functor.obj (⊤_ Marked.{u})) :=
    isLimitOfHasTerminalOfPreservesLimit E.functor
  have hp : IsFibrant (E.functor.obj A) :=
    (isFibrant_iff_of_isTerminal (E.functor.map (terminal.from A)) ht).mpr
      ((fibration_iff _).mpr hf)
  exact (cartesianMarkedModel_fibrant_iff (Δ[0] : SSet.{u}) (E.functor.obj A)).mp hp

/-- The unchanged underlying simplicial set of every actual fibrant coefficient is a quasicategory. -/
theorem coefficientFibrant_quasicategory (A : Marked.{u}) (hA : IsFibrant A) :
    Quasicategory A.toSSet := by
  let Y := coefficientPointEquivalence.functor.obj A
  let _ : InnerFibration Y.hom.hom := (coefficientFibrant_point_intrinsic A hA).1.toInnerFibration
  let _ : Quasicategory (max (Δ[0] : SSet.{u})).toSSet := by
    change Quasicategory (Δ[0] : SSet.{u})
    infer_instance
  change Quasicategory Y.left.toSSet
  exact quasicategory_of_innerFibration Y.hom.hom

/-- Every SAME original coefficient edge is marked exactly when it is an actual equivalence in its original
quasicategory. -/
theorem coefficientFibrant_marking_iff (A : Marked.{u}) (hA : IsFibrant A)
    (e : A.toSSet _⦋1⦌) :
    e ∈ A.marking ↔ (Edge.mk' e).IsEquivalence := by
  let Y := coefficientPointEquivalence.functor.obj A
  have hY := coefficientFibrant_point_intrinsic A hA
  let _ : InnerFibration Y.hom.hom := hY.1.toInnerFibration
  let _ : Quasicategory A.toSSet := coefficientFibrant_quasicategory A hA
  let _ : KanComplex (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u})) SSet.stdSimplex.isTerminalObj₀).mpr
      (inferInstance : Fibration (𝟙 (Δ[0] : SSet.{u})))
  let _ : KanComplex (max (Δ[0] : SSet.{u})).toSSet := by
    change KanComplex (Δ[0] : SSet.{u})
    infer_instance
  let _ : Quasicategory (max (Δ[0] : SSet.{u})).toSSet := by
    change Quasicategory (Δ[0] : SSet.{u})
    infer_instance
  constructor
  · intro he
    exact CartesianEdge.isEquivalence_of_map Y.hom.hom (Edge.mk' e)
      ((hY.2 e).mp he) (Edge.isEquivalence_of_kanComplex _)
  · intro he
    apply (hY.2 e).mpr
    exact CartesianEdge.isPCartesian_of_isEquivalence Y.hom.hom _
      (he.of_edge_eq (Equiv.apply_symm_apply yonedaEquiv e).symm)

end SSet.Marked
