/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeMappingSpaceIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeReedyFibrancy
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFrameHomWeakEquivalences

/-!
# Genuine weak comparison with the original cube Hom complex

The original maximum is a weak map between the proved actual opposite
Reedy fibrant diagrams. Brown's lemma for the genuine Hom-complex
functor therefore proves weak comparison for every supplied Kan Hom
object. The map remains the same whole original maximum precomposition.
-/

noncomputable section
universe u
open CategoryTheory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen CategoryTheory.SimplicialObject.reedyModelCategory

namespace CategoryTheory.CoherentRealization.CubeMappingSpace

/-- The same whole original maximum-induced comparison is a realization weak equivalence for every actual
  Kan Hom object. -/
theorem comparison_weak (H : SSet.{u}) [SSet.KanComplex H] :
    SSet.realizationWeakEquivalences (comparison H) := by
  let _ : IsFibrant RightCubeCosimplicial.diagram.{u}.op := RightCubeReedyFibrancy.cube_isFibrant
  let _ : IsFibrant SSet.stdSimplex.{u}.op := RightCubeReedyFibrancy.standard_isFibrant
  let _ : WeakEquivalence (NatTrans.op RightCubeMaximumNaturality.map.{u}) :=
    RightCubeReedyFibrancy.maximum_weak
  have h : SSet.realizationWeakEquivalences
      ((FrameHom.functor H).map (NatTrans.op RightCubeMaximumNaturality.map)) :=
    (weakEquivalence_iff ((FrameHom.functor H).map
      (NatTrans.op RightCubeMaximumNaturality.map))).mp (FrameHom.map_weakEquivalence H _)
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (FrameHom.standardIso H).inv) h

end CategoryTheory.CoherentRealization.CubeMappingSpace
