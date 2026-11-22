/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TrueSpacePowerConsumer
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingEUnitDwyerKan
import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The original E endpoints and categorical homotopy on all CSS tests

The completeness generator is F(0) to E, selecting x0. Its genuine point-unit
Iso gives the first original E point. The collapse and every original point
then follow by two out of three. The actual named Rezk Cartesian model
tensors these trivial cofibrations with any original object.

For every complete target, a literal E homotopy from r to the identity gives
weakness of precomposition by r. This proof uses the two actual endpoint
tests and ordinary composition only; it invokes no Dwyer--Kan recognition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open HomotopicalAlgebra CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner SimplicialSpace.Cartesian

namespace SimplicialSpace.OriginalWalkingETests

/-- The original standard simplicial point is compared with the actual scalar tensor unit. -/
def scalarPointUnitIso : (Δ[0] : SSet.{u}) ≅ (𝟙_ SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso isTerminalTensorUnit

/-- The source of the actual completeness generator is the genuine simplicial-space unit. -/
def completenessSourceUnitIso :
    ofSimplicialObject.obj (SSet.Rezk.representable.{u} 0) ≅ (𝟙_ SimplicialSpace.{u}) :=
  discreteInnerFunctor.mapIso scalarPointUnitIso ≪≫ WalkingEUnit.coherentUnitIso

/-- The actual generator selects precisely the original x0 point after that source Iso. -/
theorem completenessMap_unit_zero :
    completenessSourceUnitIso.{u}.hom ≫ WalkingEUnit.coherentPoint SSet.coherentIso.x₀ =
      ofSimplicialObject.map SSet.Rezk.completenessMap.{u} := by
  let e : discreteInnerFunctor.obj (𝟙_ SSet.{u}) ≅ (𝟙_ SimplicialSpace.{u}) :=
    WalkingEUnit.coherentUnitIso
  let p : (𝟙_ SSet.{u}) ⟶ SSet.coherentIso :=
    (SSet.unitHomEquiv SSet.coherentIso).symm SSet.coherentIso.x₀
  have hp : scalarPointUnitIso.hom ≫ p = SSet.yonedaEquiv.symm SSet.coherentIso.x₀ := by
    apply SSet.yonedaEquiv.injective
    change (SSet.unitHomEquiv SSet.coherentIso)
      ((SSet.unitHomEquiv SSet.coherentIso).symm SSet.coherentIso.x₀) = SSet.coherentIso.x₀
    exact (SSet.unitHomEquiv SSet.coherentIso).apply_symm_apply _
  change (discreteInnerFunctor.map scalarPointUnitIso.hom ≫ e.hom) ≫
      (e.inv ≫ discreteInnerFunctor.map p) =
    discreteInnerFunctor.map (SSet.yonedaEquiv.symm SSet.coherentIso.x₀)
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, hp]

/-- Every complete target directly tests the original completeness generator as weak. -/
theorem completenessMap_rezkWeak :
    rezkWeakEquivalences
      (ofSimplicialObject.map SSet.Rezk.completenessMap.{u}) := by
  intro Z hZ
  exact hZ.2 (Sum.inr PUnit.unit)

/-- The actual x0 unit-point is weak in the genuine all-complete-target class. -/
theorem coherentPoint_zero_rezkWeak :
    rezkWeakEquivalences (WalkingEUnit.coherentPoint.{u} SSet.coherentIso.x₀) := by
  have hi := rezkWeakEquivalences.of_isIso completenessSourceUnitIso.{u}.hom
  apply (rezkWeakEquivalences.precomp_iff _ _ hi).mp
  rw [completenessMap_unit_zero]
  exact completenessMap_rezkWeak

/-- Every original walking-E point has the same literal section-collapse equation. -/
theorem coherentPoint_collapse (e : SSet.coherentIso.{u} _⦋0⦌) :
    WalkingEUnit.coherentPoint e ≫ toUnit WalkingEUnit.coherentSpace =
      𝟙 (𝟙_ SimplicialSpace.{u}) :=
  toUnit_unique _ _

/-- The actual E collapse is derived weak from x0, rather than assumed to be the localizer. -/
theorem coherentCollapse_rezkWeak :
    rezkWeakEquivalences (toUnit WalkingEUnit.coherentSpace.{u}) := by
  apply (rezkWeakEquivalences.precomp_iff _ _ coherentPoint_zero_rezkWeak).mp
  rw [coherentPoint_collapse]
  exact rezkWeakEquivalences.id_mem _

/-- The original second point, and every original E vertex, follows from the same collapse. -/
theorem coherentPoint_rezkWeak (e : SSet.coherentIso.{u} _⦋0⦌) :
    rezkWeakEquivalences (WalkingEUnit.coherentPoint e) := by
  apply (rezkWeakEquivalences.postcomp_iff _ _ coherentCollapse_rezkWeak).mp
  rw [coherentPoint_collapse]
  exact rezkWeakEquivalences.id_mem _

/-- Each actual point is a trivial cofibration in the literal named Rezk model. -/
theorem coherentPoint_trivialCofibration (e : SSet.coherentIso.{u} _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    trivialCofibrations SimplicialSpace.{u} (WalkingEUnit.coherentPoint e) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  rw [RezkModel.modelCategory_trivialCofibrations]
  exact ⟨isTerminalTensorUnit.mono_from _, coherentPoint_rezkWeak e⟩

/-- Both Cartesian projections identify the original E-first endpoint with fixed-left tensoring. -/
theorem spaceEndpoint_eq_leftTensor (X : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    WalkingEUnit.spaceEndpoint X e =
      (ρ_ X).inv ≫ (X ◁ WalkingEUnit.coherentPoint e) ≫
        (β_ X WalkingEUnit.coherentSpace).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, (WalkingEUnit.spaceEndpoint_laws X e).1,
      braiding_hom_fst, whiskerLeft_snd, rightUnitor_inv_snd_assoc]
  · simp only [Category.assoc, (WalkingEUnit.spaceEndpoint_laws X e).2.1,
      braiding_hom_snd, whiskerLeft_fst, rightUnitor_inv_fst]

/-- The genuine Arrow Iso retains both the actual endpoint and the actual tensor map. -/
def spaceEndpointLeftTensorArrowIso (X : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    Arrow.mk (WalkingEUnit.spaceEndpoint X e) ≅
      Arrow.mk (X ◁ WalkingEUnit.coherentPoint e) :=
  Arrow.isoMk' _ _ (ρ_ X).symm (β_ X WalkingEUnit.coherentSpace).symm (by
    rw [spaceEndpoint_eq_leftTensor]
    simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- Tensoring the actual point with any original X gives the original endpoint trivial
cofibration. -/
theorem spaceEndpoint_trivialCofibration (X : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    trivialCofibrations SimplicialSpace.{u} (WalkingEUnit.spaceEndpoint X e) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
    TrueSpacePowerPreparation.actualRezk_closedSymmetricMonoidalModel
  let _ : IsCofibrant X := TrueSpacePowerPreparation.actualRezk_isCofibrant X
  have hQ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant X
  have ht := hQ.preservesTrivialCofibrations
    (WalkingEUnit.coherentPoint e) (coherentPoint_trivialCofibration e)
  exact ((trivialCofibrations SimplicialSpace.{u}).arrow_mk_iso_iff
    (spaceEndpointLeftTensorArrowIso X e)).mpr ht

/-- Every complete target tests both actual E-first endpoint inclusions as scalar weak maps. -/
theorem spaceEndpoint_rezkWeak (X : SimplicialSpace.{u})
    (e : SSet.coherentIso.{u} _⦋0⦌) :
    rezkWeakEquivalences (WalkingEUnit.spaceEndpoint X e) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  have ht := spaceEndpoint_trivialCofibration X e
  rw [RezkModel.modelCategory_trivialCofibrations] at ht
  exact ht.2

/-- The original complete-target test uses exactly the designated inner precomposition functor. -/
def innerTestMap {A B : SimplicialSpace.{u}} (f : A ⟶ B) (Z : SimplicialSpace.{u}) :
    (innerHomFunctor.obj (op B)).obj Z ⟶ (innerHomFunctor.obj (op A)).obj Z :=
  (innerHomFunctor.map f.op).app Z

/-- Inner precomposition reverses the original two morphisms in the actual functor. -/
theorem innerTestMap_comp {A B C : SimplicialSpace.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (Z : SimplicialSpace.{u}) :
    innerTestMap g Z ≫ innerTestMap f Z = innerTestMap (f ≫ g) Z := by
  dsimp only [innerTestMap]
  rw [← NatTrans.comp_app, ← innerHomFunctor.map_comp, ← op_comp]

/-- The literal identity induces the identity on the entire original inner mapping object. -/
theorem innerTestMap_id (X Z : SimplicialSpace.{u}) :
    innerTestMap (𝟙 X) Z = 𝟙 ((innerHomFunctor.obj (op X)).obj Z) := by
  simp only [innerTestMap, op_id, CategoryTheory.Functor.map_id, NatTrans.id_app]

/-- A literal E homotopy from r to identity proves its full inner test weak for every complete Z. -/
theorem categoricalSelfHomotopy_test_weak {X : SimplicialSpace.{u}} (r : X ⟶ X)
    (H : WalkingEUnit.coherentSpace ⊗ X ⟶ X)
    (h0 : WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₀ ≫ H = r)
    (h1 : WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₁ ≫ H = 𝟙 X)
    (Z : SimplicialSpace.{u}) (hZ : completeSegalSpaces Z) :
    SSet.realizationWeakEquivalences (innerTestMap r Z) := by
  have hw0 : SSet.realizationWeakEquivalences
      (innerTestMap (WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₀) Z) :=
    spaceEndpoint_rezkWeak X SSet.coherentIso.x₀ Z hZ
  have hw1 : SSet.realizationWeakEquivalences
      (innerTestMap (WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₁) Z) :=
    spaceEndpoint_rezkWeak X SSet.coherentIso.x₁ Z hZ
  have hid : innerTestMap H Z ≫
      innerTestMap (WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₁) Z = 𝟙 _ := by
    rw [innerTestMap_comp, h1, innerTestMap_id]
  have hwH : SSet.realizationWeakEquivalences (innerTestMap H Z) := by
    apply (SSet.realizationWeakEquivalences.postcomp_iff (innerTestMap H Z)
      (innerTestMap (WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₁) Z) hw1).mp
    rw [hid]
    exact SSet.realizationWeakEquivalences.id_mem _
  rw [← h0, ← innerTestMap_comp]
  exact SSet.realizationWeakEquivalences.comp_mem _ _ hwH hw0

/-- The same original categorical homotopy establishes membership in the genuine all-CSS class. -/
theorem categoricalSelfHomotopy_rezkWeak {X : SimplicialSpace.{u}} (r : X ⟶ X)
    (H : WalkingEUnit.coherentSpace ⊗ X ⟶ X)
    (h0 : WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₀ ≫ H = r)
    (h1 : WalkingEUnit.spaceEndpoint X SSet.coherentIso.x₁ ≫ H = 𝟙 X) :
    rezkWeakEquivalences r :=
  fun Z hZ => categoricalSelfHomotopy_test_weak r H h0 h1 Z hZ

end SimplicialSpace.OriginalWalkingETests
