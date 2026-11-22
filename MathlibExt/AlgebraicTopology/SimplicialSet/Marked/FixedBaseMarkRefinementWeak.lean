/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CompositionMarkParameterExtension
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.KanMarkParameterExtension
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalTargetSourceIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeSourceIsomorphism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeTargetNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences

/-!
# Actual fixed-base weakness of the original marking refinements

Composition and Kan-source marking extensions retain their complete
underlying parameter maps. Their actual maximal mapping restrictions
are isomorphisms, as are restrictions into the maximal base. The native
relative pullback comparison therefore proves full fixed-base mapping
weakness into each original intrinsic target. Arbitrary supplied Kan
sources are retained; no claim that this whole family is small is made.
-/

noncomputable section
universe u
open CategoryTheory Limits
open scoped Simplicial

namespace SSet.Marked

/-- The original composition marking refinement lies over its actual whole base simplex. -/
def compositionCellOver {B : SSet.{u}} (r : compositionCellTarget.{u} ⟶ max B) :
    Over.mk (compositionCell.{u} ≫ r) ⟶ Over.mk r :=
  Over.homMk compositionCell.{u} rfl

/-- The original Kan-source marking refinement lies over its supplied whole original base map. -/
def kanMarkCellOver {B : SSet.{u}} (K : SSet.{u}) (r : max K ⟶ max B) :
    Over.mk (kanMarkCell K ≫ r) ⟶ Over.mk r :=
  Over.homMk (kanMarkCell K) rfl

/-- The complete relative composition marking restriction into the canonical Cartesian target is an actual
  isomorphism. -/
theorem compositionCellOver_cartesian_isIso {B E : SSet.{u}} [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) (p : E ⟶ B) [InnerFibration p] :
    IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (compositionCellOver r).op) := by
  let _ : IsIso compositionCell.{u}.hom := by change IsIso (𝟙 (Δ[2] : SSet.{u})); infer_instance
  let h₁ : IsIso (mappingComplexPre .maximal compositionCell.{u} (cartesian p)) :=
    inferInstanceAs (IsIso (compositionMarkCartesianMappingIso p).hom)
  let h₂ : IsIso (mappingComplexPre .maximal compositionCell.{u} (max B)) :=
    mappingComplexPre_max_isIso .maximal _ B
  exact @relativeMappingPre_isIso .maximal _ _ _ _ compositionCell.{u} r _
    (cartesianProjection p) rfl h₁ h₂

/-- The same original Kan-source relative marking restriction into the canonical Cartesian target is an
  actual isomorphism. -/
theorem kanMarkCellOver_cartesian_isIso {B E : SSet.{u}} [Quasicategory B]
    (K : SSet.{u}) [KanComplex K] (r : max K ⟶ max B) (p : E ⟶ B) [InnerFibration p] :
    IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (kanMarkCellOver K r).op) := by
  let _ : IsIso (kanMarkCell K).hom := by change IsIso (𝟙 K); infer_instance
  let h₁ : IsIso (mappingComplexPre .maximal (kanMarkCell K) (cartesian p)) :=
    inferInstanceAs (IsIso (kanMarkCartesianMappingIso K p).hom)
  let h₂ : IsIso (mappingComplexPre .maximal (kanMarkCell K) (max B)) :=
    mappingComplexPre_max_isIso .maximal _ B
  exact @relativeMappingPre_isIso .maximal _ _ _ _ (kanMarkCell K) r _
    (cartesianProjection p) rfl h₁ h₂

/-- Each original composition refinement has every full Cartesian relative mapping boundary lift. -/
theorem compositionCellOver_cartesian_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map (compositionCellOver r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cartesianProjection p) :=
    Over.isoMk (cartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  let _ : IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (compositionCellOver r).op) := compositionCellOver_cartesian_isIso r p
  have h := modelCategoryQuillen.I.rlp_of_isIso
    ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map (compositionCellOver r).op)
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (compositionCellOver r) e)).mpr h

/-- Every supplied original Kan-source marking refinement has the full Cartesian relative boundary-right property. -/
theorem kanMarkCellOver_cartesian_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (K : SSet.{u}) [KanComplex K] (r : max K ⟶ max B) (Y : CartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map (kanMarkCellOver K r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cartesianProjection p) :=
    Over.isoMk (cartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  let _ : IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map
      (kanMarkCellOver K r).op) := kanMarkCellOver_cartesian_isIso K r p
  have h := modelCategoryQuillen.I.rlp_of_isIso
    ((overMappingFunctor .maximal (max B) (Over.mk (cartesianProjection p))).map (kanMarkCellOver K r).op)
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (kanMarkCellOver K r) e)).mpr h

/-- The whole original composition marking refinement is Cartesian mapping weak over its actual base simplex. -/
theorem compositionCellOver_cartesian_weak {B : SSet.{u}} [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) : cartesianWeakEquivalences B (compositionCellOver r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (compositionCellOver_cartesian_mapping_rlp r Y)

/-- Each original Kan-source marking refinement is Cartesian mapping weak, without a bound on the supplied
  source size. -/
theorem kanMarkCellOver_cartesian_weak {B : SSet.{u}} [Quasicategory B]
    (K : SSet.{u}) [KanComplex K] (r : max K ⟶ max B) : cartesianWeakEquivalences B (kanMarkCellOver K r) := by
  apply (cartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (kanMarkCellOver_cartesian_mapping_rlp K r Y)

/-- The complete relative composition marking restriction into the canonical Cocartesian target is an actual
  isomorphism. -/
theorem compositionCellOver_cocartesian_isIso {B E : SSet.{u}} [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) (p : E ⟶ B) [InnerFibration p] :
    IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map
      (compositionCellOver r).op) := by
  let _ : IsIso compositionCell.{u}.hom := by change IsIso (𝟙 (Δ[2] : SSet.{u})); infer_instance
  let h₁ : IsIso (mappingComplexPre .maximal compositionCell.{u} (cocartesian p)) :=
    inferInstanceAs (IsIso (compositionMarkCocartesianMappingIso p).hom)
  let h₂ : IsIso (mappingComplexPre .maximal compositionCell.{u} (max B)) :=
    mappingComplexPre_max_isIso .maximal _ B
  exact @relativeMappingPre_isIso .maximal _ _ _ _ compositionCell.{u} r _
    (cocartesianProjection p) rfl h₁ h₂

/-- The same original Kan-source relative marking restriction into the canonical Cocartesian target is an
  actual isomorphism. -/
theorem kanMarkCellOver_cocartesian_isIso {B E : SSet.{u}} [Quasicategory B]
    (K : SSet.{u}) [KanComplex K] (r : max K ⟶ max B) (p : E ⟶ B) [InnerFibration p] :
    IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map
      (kanMarkCellOver K r).op) := by
  let _ : IsIso (kanMarkCell K).hom := by change IsIso (𝟙 K); infer_instance
  let h₁ : IsIso (mappingComplexPre .maximal (kanMarkCell K) (cocartesian p)) :=
    inferInstanceAs (IsIso (kanMarkCocartesianMappingIso K p).hom)
  let h₂ : IsIso (mappingComplexPre .maximal (kanMarkCell K) (max B)) :=
    mappingComplexPre_max_isIso .maximal _ B
  exact @relativeMappingPre_isIso .maximal _ _ _ _ (kanMarkCell K) r _
    (cocartesianProjection p) rfl h₁ h₂

/-- Each original composition refinement has every full Cocartesian relative mapping boundary lift. -/
theorem compositionCellOver_cocartesian_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) (Y : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map (compositionCellOver r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CocartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cocartesianProjection p) :=
    Over.isoMk (cocartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  let _ : IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map
      (compositionCellOver r).op) := compositionCellOver_cocartesian_isIso r p
  have h := modelCategoryQuillen.I.rlp_of_isIso
    ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map (compositionCellOver r).op)
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (compositionCellOver r) e)).mpr h

/-- Every supplied original Kan-source marking refinement has the full Cocartesian relative boundary-right property. -/
theorem kanMarkCellOver_cocartesian_mapping_rlp {B : SSet.{u}} [Quasicategory B]
    (K : SSet.{u}) [KanComplex K] (r : max K ⟶ max B) (Y : CocartesianOver B) :
    modelCategoryQuillen.I.{u}.rlp ((overMappingFunctor .maximal (max B) Y.obj).map (kanMarkCellOver K r).op) := by
  let p : Y.obj.left.toSSet ⟶ B := Y.obj.hom.hom
  let _ : CocartesianFibration p := Y.property.1
  let e : Y.obj ≅ Over.mk (cocartesianProjection p) :=
    Over.isoMk (cocartesianMarkingIso p Y.property.2) (Hom.ext rfl)
  let _ : IsIso ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map
      (kanMarkCellOver K r).op) := kanMarkCellOver_cocartesian_isIso K r p
  have h := modelCategoryQuillen.I.rlp_of_isIso
    ((overMappingFunctor .maximal (max B) (Over.mk (cocartesianProjection p))).map (kanMarkCellOver K r).op)
  exact (modelCategoryQuillen.I.rlp.arrow_iso_iff
    (overMappingRestrictionTargetIso .maximal (kanMarkCellOver K r) e)).mpr h

/-- The whole original composition marking refinement is Cocartesian mapping weak over its actual base simplex. -/
theorem compositionCellOver_cocartesian_weak {B : SSet.{u}} [Quasicategory B]
    (r : compositionCellTarget.{u} ⟶ max B) : cocartesianWeakEquivalences B (compositionCellOver r) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (compositionCellOver_cocartesian_mapping_rlp r Y)

/-- Each original Kan-source marking refinement is Cocartesian mapping weak, without a bound on the supplied
  source size. -/
theorem kanMarkCellOver_cocartesian_weak {B : SSet.{u}} [Quasicategory B]
    (K : SSet.{u}) [KanComplex K] (r : max K ⟶ max B) : cocartesianWeakEquivalences B (kanMarkCellOver K r) := by
  apply (cocartesianWeakEquivalences_iff _).mpr
  intro Y
  exact modelCategoryQuillen.I_rlp_le_realizationWeakEquivalences _ (kanMarkCellOver_cocartesian_mapping_rlp K r Y)

end SSet.Marked
