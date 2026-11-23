/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.OuterEdgewiseDiagonal
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex
public import MathlibExt.KTheory.Exact.Quillen.QuillenEdgewiseStageNerve

/-!
# Outer-edgewise comparison for weak Waldhausen Stages

The outer-edgewise weak-Stage nerve is canonically isomorphic to the generic
outer-edgewise subdivision of the ordinary weak-Stage nerve.  Its components
are identities, and its naturality is the strict edgewise Stage reindexing
law.  Diagonalizing this isomorphism and then applying the generic
outer-edgewise comparison gives the literal map from the edgewise weak-Stage
diagonal to the ordinary weak-Stage diagonal.

The generic outer-edgewise diagonal theorem makes this map a realization weak
equivalence.  In degree zero the right-block comparison is `δ 0`, so it sends
the pointwise-zero degree-one Stage to the canonical ordinary Stage-zero
vertex; the corresponding realized point is preserved as well.

This file constructs no full Q/S comparison, pointed map, loop-space map,
spectrum map, or global homotopical instance.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory

open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The canonical Waldhausen structure of the original exact category for the outer-edgewise comparison. -/
local instance quillenOuterEdgewiseStageComparisonWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The explicitly constructed outer-edgewise Stage nerve agrees with the
generic outer-edgewise subdivision of the ordinary weak-Stage nerve.  Every
component of this isomorphism is the identity. -/
noncomputable def edgewiseStageWeakNerveIsoOuterEdgewise :
    edgewiseStageWeakNerve C ≅
      SSet.outerEdgewise.obj (stageWeakNerve C) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b f
    rfl)

/-- The forward component of the outer-edgewise Stage carrier isomorphism is
the identity. -/
@[simp]
theorem edgewiseStageWeakNerveIsoOuterEdgewise_hom_app
    (a : SimplexCategoryᵒᵖ) :
    (edgewiseStageWeakNerveIsoOuterEdgewise (C := C)).hom.app a = 𝟙 _ :=
  rfl

/-- The inverse component of the outer-edgewise Stage carrier isomorphism is
the identity. -/
@[simp]
theorem edgewiseStageWeakNerveIsoOuterEdgewise_inv_app
    (a : SimplexCategoryᵒᵖ) :
    (edgewiseStageWeakNerveIsoOuterEdgewise (C := C)).inv.app a = 𝟙 _ :=
  rfl

/-- The literal diagonal comparison from the outer-edgewise weak-Stage
diagonal to the ordinary weak-Stage diagonal. -/
noncomputable def outerEdgewiseStageDiagonalComparison :
    edgewiseStageWeakDiagonal C ⟶ stageWeakDiagonal C :=
  SSet.simplicialDiagonalFunctor.map
      (edgewiseStageWeakNerveIsoOuterEdgewise (C := C)).hom ≫
    SSet.outerEdgewiseDiagonalComparison (stageWeakNerve C)

/-- The Stage comparison is pointwise the nerve map induced by the
right-block inclusion. -/
@[simp]
theorem outerEdgewiseStageDiagonalComparison_app
    (a : SimplexCategoryᵒᵖ) :
    (outerEdgewiseStageDiagonalComparison (C := C)).app a =
      ((stageWeakNerve C).map
        (SimplexCategory.edgewiseRightInclusion.app a.unop).op).app a := by
  rfl

/-- The literal outer-edgewise Stage comparison is a realization weak
equivalence. -/
theorem outerEdgewiseStageDiagonalComparison_mem_realizationWeakEquivalences :
    SSet.realizationWeakEquivalences
      (outerEdgewiseStageDiagonalComparison (C := C)) := by
  unfold outerEdgewiseStageDiagonalComparison
  exact MorphismProperty.RespectsIso.precomp
    SSet.realizationWeakEquivalences
    (SSet.simplicialDiagonalFunctor.map
      (edgewiseStageWeakNerveIsoOuterEdgewise (C := C)).hom)
    (SSet.outerEdgewiseDiagonalComparison (stageWeakNerve C))
    (SSet.outerEdgewiseDiagonalComparison_mem_realizationWeakEquivalences
      (stageWeakNerve C))

/-- Degree-zero vertex of the edgewise weak-Stage diagonal, represented by
the pointwise-zero Stage in degree one. -/
noncomputable def edgewiseStageWeakDiagonalZeroVertex :
    (edgewiseStageWeakDiagonal C).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀
    (⟨⟨zeroDiagram C 1, isStage_zeroDiagram C 1⟩⟩ :
      StageWeakCategory C 1)

/-- The actual right-block degree-zero nerve map retains the canonical zero vertex. -/
@[simp]
theorem outerEdgewiseStageRightBlock_zeroVertex :
    (CategoryTheory.nerveMap
        (reindexStageWeak C (SimplexCategory.δ (0 : Fin 2)))).app
        (Opposite.op (SimplexCategory.mk 0))
        (edgewiseStageWeakDiagonalZeroVertex (C := C)) =
      stageWeakDiagonalZeroVertex C := by
  simp only [edgewiseStageWeakDiagonalZeroVertex,
    stageWeakDiagonalZeroVertex]
  rfl

/-- The right-block comparison sends the pointwise-zero degree-one Stage to
the canonical Stage-zero vertex. -/
theorem outerEdgewiseStageDiagonalComparison_zeroVertex :
    (outerEdgewiseStageDiagonalComparison (C := C)).app
        (Opposite.op (SimplexCategory.mk 0))
        (edgewiseStageWeakDiagonalZeroVertex (C := C)) =
      stageWeakDiagonalZeroVertex C := by
  rw [outerEdgewiseStageDiagonalComparison_app,
    SimplexCategory.edgewiseRightInclusion_app_zero]
  exact outerEdgewiseStageRightBlock_zeroVertex

/-- The realized outer-edgewise zero vertex maps to the realized ordinary
Stage-zero vertex. -/
theorem outerEdgewiseStageDiagonalComparison_realizedZeroVertex :
    SSet.toTop.map (outerEdgewiseStageDiagonalComparison (C := C))
        (SSet.realizedVertex
          (edgewiseStageWeakDiagonalZeroVertex (C := C))) =
      SSet.realizedVertex (stageWeakDiagonalZeroVertex C) := by
  rw [← SSet.realizedVertex_naturality,
    outerEdgewiseStageDiagonalComparison_zeroVertex]

end AlgebraicKTheory

end
