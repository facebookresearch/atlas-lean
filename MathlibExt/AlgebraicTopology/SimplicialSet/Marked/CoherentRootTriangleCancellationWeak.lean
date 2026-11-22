/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentRootTriangleCancellationCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseMarkRefinementWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientTensor

/-!
# The original root-triangle cancellation cell is actually coefficient weak

Both original root triangles, cancellation and every marked parameter were retained
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
def rootTriangleCancellationCellOver {B : SSet.{u}} (r : rootTriangleCancellationTarget.{u} ⟶ max B) :
    Over.mk (rootTriangleCancellationCell.{u} ≫ r) ⟶ Over.mk r :=
  Over.homMk rootTriangleCancellationCell.{u} rfl

/-- The whole original relative mapping restriction of the root cell into a Cartesian target is an actual
isomorphism. -/
theorem rootTriangleCancellationCellOver_cartesian_isIso {B E : SSet.{u}} [Quasicategory B]
    (r : rootTriangleCancellationTarget.{u} ⟶ max B) (p : E ⟶ B) [InnerFibration p] :
    IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (rootTriangleCancellationCellOver r).op) := by
  let _ : IsIso rootTriangleCancellationCell.{u}.hom := by change IsIso (𝟙 _); infer_instance
  let h₁ : IsIso (mappingComplexPre .maximal rootTriangleCancellationCell.{u} (cartesian p)) :=
    inferInstanceAs (IsIso (rootTriangleCancellationCartesianMappingIso p).hom)
  let h₂ : IsIso (mappingComplexPre .maximal rootTriangleCancellationCell.{u} (max B)) :=
    mappingComplexPre_max_isIso .maximal _ B
  exact @relativeMappingPre_isIso .maximal _ _ _ _ rootTriangleCancellationCell.{u} r _
    (cartesianProjection p) rfl h₁ h₂

/-- Every actual intrinsic Cartesian target gives full original mapping boundary lifts for the same root marking
cell. -/
theorem rootTriangleCancellationCellOver_cartesian_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (r : rootTriangleCancellationTarget.{u} ⟶ max B) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map
      (rootTriangleCancellationCellOver r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cartesianProjection p) :=
    Over.isoMk (cartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  let _ : IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (rootTriangleCancellationCellOver r).op) := rootTriangleCancellationCellOver_cartesian_isIso r p
  have h := modelCategoryQuillen.I.rlp_of_isIso
    ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (rootTriangleCancellationCellOver r).op)
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (rootTriangleCancellationCellOver r) e)).mpr h

/-- The same full original root marking cell is genuinely Cartesian mapping weak over its entire supplied base map. -/
theorem rootTriangleCancellationCellOver_cartesian_weak {B : SSet.{u}} [Quasicategory B]
    (r : rootTriangleCancellationTarget.{u} ⟶ max B) :
    cartesianWeakEquivalences B (rootTriangleCancellationCellOver r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _
    (rootTriangleCancellationCellOver_cartesian_mapping_rlp r Y)

/-- Both original root triangles, inherited marks and new first-edge mark define an actual original
coefficient-model trivial cofibration. -/
theorem rootTriangleCancellationCell_trivialCofibration :
    trivialCofibrations Marked.{u} rootTriangleCancellationCell.{u} := by
  refine ⟨?_, ?_⟩
  · rw [coefficientMarkedCofibrations_eq]
    exact rootTriangleCancellationCell_mono
  · change cartesianWeakEquivalences (Δ[0] : SSet.{u})
      (coefficientPointEquivalence.functor.map rootTriangleCancellationCell.{u})
    let _ : (cartesianWeakEquivalences (Δ[0] : SSet.{u})).RespectsIso := by
      unfold cartesianWeakEquivalences
      infer_instance
    let r : rootTriangleCancellationTarget.{u} ⟶ max (Δ[0] : SSet.{u}) :=
      (parameterZeroIsTerminal .maximal).from _
    let e : Arrow.mk (coefficientPointEquivalence.functor.map rootTriangleCancellationCell.{u}) ≅
        Arrow.mk (rootTriangleCancellationCellOver r) :=
      Arrow.isoMk
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (Over.isoMk (Iso.refl _) ((parameterZeroIsTerminal .maximal).hom_ext _ _))
        (by apply Over.OverMorphism.ext; apply Hom.ext; rfl)
    exact ((cartesianWeakEquivalences (Δ[0] : SSet.{u})).arrow_mk_iso_iff e).mpr
      (rootTriangleCancellationCellOver_cartesian_weak r)

end SSet.Marked.CoherentWeight
