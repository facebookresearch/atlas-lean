/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentRootTriangleCompositionCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseMarkRefinementWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor

/-!
# The original root-triangle marking cell is actually coefficient weak

Both original root triangles and every marked parameter were retained
in the actual maximal mapping isomorphism. The same original relative
pullback restriction therefore has all boundary lifts over each actual
quasicategory base. Transport through the original point equivalence
proves the actual coefficient-model trivial cofibration. No marking
saturation or weak-cell outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- The same original root marking cell retains its entire supplied marked base projection. -/
def rootTriangleCompositionCellOver {B : SSet.{u}} (r : rootTriangleCompositionTarget.{u} ⟶ max B) :
    Over.mk (rootTriangleCompositionCell.{u} ≫ r) ⟶ Over.mk r :=
  Over.homMk rootTriangleCompositionCell.{u} rfl

/-- The whole original relative mapping restriction of the root cell into a Cartesian target is an actual
isomorphism. -/
theorem rootTriangleCompositionCellOver_cartesian_isIso {B E : SSet.{u}} [Quasicategory B]
    (r : rootTriangleCompositionTarget.{u} ⟶ max B) (p : E ⟶ B) [InnerFibration p] :
    IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (rootTriangleCompositionCellOver r).op) := by
  let _ : IsIso rootTriangleCompositionCell.{u}.hom := by change IsIso (𝟙 _); infer_instance
  let h₁ : IsIso (mappingComplexPre .maximal rootTriangleCompositionCell.{u} (cartesian p)) :=
    inferInstanceAs (IsIso (rootTriangleCompositionCartesianMappingIso p).hom)
  let h₂ : IsIso (mappingComplexPre .maximal rootTriangleCompositionCell.{u} (max B)) :=
    mappingComplexPre_max_isIso .maximal _ B
  exact @relativeMappingPre_isIso .maximal _ _ _ _ rootTriangleCompositionCell.{u} r _
    (cartesianProjection p) rfl h₁ h₂

/-- Every actual intrinsic Cartesian target gives full original mapping boundary lifts for the same root marking
cell. -/
theorem rootTriangleCompositionCellOver_cartesian_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (r : rootTriangleCompositionTarget.{u} ⟶ max B) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map
      (rootTriangleCompositionCellOver r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cartesianProjection p) :=
    Over.isoMk (cartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  let _ : IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (rootTriangleCompositionCellOver r).op) := rootTriangleCompositionCellOver_cartesian_isIso r p
  have h := modelCategoryQuillen.I.rlp_of_isIso
    ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (rootTriangleCompositionCellOver r).op)
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (rootTriangleCompositionCellOver r) e)).mpr h

/-- The same full original root marking cell is genuinely Cartesian mapping weak over its entire supplied base map. -/
theorem rootTriangleCompositionCellOver_cartesian_weak {B : SSet.{u}} [Quasicategory B]
    (r : rootTriangleCompositionTarget.{u} ⟶ max B) :
    cartesianWeakEquivalences B (rootTriangleCompositionCellOver r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (rootTriangleCompositionCellOver_cartesian_mapping_rlp r Y)

/-- Both original root triangles, inherited marks and new direct-edge mark define an actual original
coefficient-model trivial cofibration. -/
theorem rootTriangleCompositionCell_trivialCofibration :
    trivialCofibrations Marked.{u} rootTriangleCompositionCell.{u} := by
  refine ⟨?_, ?_⟩
  · rw [coefficientMarkedCofibrations_eq]
    exact rootTriangleCompositionCell_mono
  · change cartesianWeakEquivalences (Δ[0] : SSet.{u})
      (coefficientPointEquivalence.functor.map rootTriangleCompositionCell.{u})
    let _ : (cartesianWeakEquivalences (Δ[0] : SSet.{u})).RespectsIso := by
      unfold cartesianWeakEquivalences
      infer_instance
    let r : rootTriangleCompositionTarget.{u} ⟶ max (Δ[0] : SSet.{u}) :=
      (parameterZeroIsTerminal .maximal).from _
    let e : Arrow.mk (coefficientPointEquivalence.functor.map rootTriangleCompositionCell.{u}) ≅
        Arrow.mk (rootTriangleCompositionCellOver r) :=
      Arrow.isoMk
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)
    exact ((cartesianWeakEquivalences (Δ[0] : SSet.{u})).arrow_mk_iso_iff e).mpr
      (rootTriangleCompositionCellOver_cartesian_weak r)

end SSet.Marked.CoherentWeight
