/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedObjectHornLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerFixedObjectGlobalLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanRetracts

/-!
# Genuine global factorization for the original full-Hom horn class

The actual fixed-label free-horn factorization of the reindexed original
map supplies both full global legs. The left leg is a genuine global
cofibration and DK weak map; the right leg is a fibration on every whole
original Hom. The literal original object map and every Hom composite
are retained. This is the A1 part of Bergner's generating acyclic
cofibrations, not the separate A2 object-equivalence lifting condition.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner.HornFactorization
open FixedObjects

/-- Factor every whole original changing-object map by the actual reindexed free-horn construction. -/
def data {C D : Carrier.{u}} (F : C ⟶ D) :
    MorphismProperty.MapFactorizationData homHornLeft homFibrations F := by
  let fixed := CarrierReindexing.fixedPart F
  let φ := FreeFactorization.horn fixed
  let projection := CarrierReindexing.toTarget D F.obj
  refine {
    Z := φ.Z.val
    i := φ.i.val
    p := φ.p.val ≫ projection
    fac := ?_
    hi := fixedTrivialCofibration_homHornLeft φ.i φ.hi
    hp := ?_ }
  · have h : φ.i.val ≫ φ.p.val = fixed.val :=
      congrArg (fun G : CarrierReindexing.source C ⟶ CarrierReindexing.object D F.obj => G.val) φ.fac
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun G => G ≫ projection) h).trans (CarrierReindexing.factorization F))
  · intro x y
    change Fibration (φ.p.val.map x y ≫ 𝟙 _)
    simpa only [Category.comp_id] using FreeFactorization.horn_p_original fixed x y

/-- The two actual full global legs compose to the SAME original enriched functor. -/
theorem fac {C D : Carrier.{u}} (F : C ⟶ D) : (data F).i ≫ (data F).p = F := (data F).fac

/-- The original left leg retains the actual fixed-label free-horn map. -/
theorem left_original {C D : Carrier.{u}} (F : C ⟶ D) :
    (data F).i = (FreeFactorization.horn (CarrierReindexing.fixedPart F)).i.val := rfl

/-- The original right leg retains the actual fixed-label horn projection and identity-Hom target projection. -/
theorem right_original {C D : Carrier.{u}} (F : C ⟶ D) :
    (data F).p = (FreeFactorization.horn (CarrierReindexing.fixedPart F)).p.val ≫
      CarrierReindexing.toTarget D F.obj := rfl

/-- Every original source object has its identical fixed label in the actual intermediate carrier. -/
theorem left_object {C D : Carrier.{u}} (F : C ⟶ D) (x : C) :
    (data F).i.obj x = vertex (FreeFactorization.horn (CarrierReindexing.fixedPart F)).Z x :=
  map_vertex _ _

/-- The right object map is exactly the SAME original map on its retained fixed label. -/
theorem right_object {C D : Carrier.{u}} (F : C ⟶ D) (x : C) :
    (data F).p.obj (vertex (FreeFactorization.horn (CarrierReindexing.fixedPart F)).Z x) = F.obj x := by
  change F.obj ((FreeFactorization.horn (CarrierReindexing.fixedPart F)).p.val.obj
    (vertex (FreeFactorization.horn (CarrierReindexing.fixedPart F)).Z x)) = F.obj x
  rw [map_vertex]
  rfl

/-- The complete original Hom composite equals the SAME whole input Hom map at every original pair. -/
theorem hom_fac {C D : Carrier.{u}} (F : C ⟶ D) (x y : C) :
    (data F).i.map x y ≫ (data F).p.map ((data F).i.obj x) ((data F).i.obj y) =
      F.map x y ≫ eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b)
        (congrArg (fun G : C ⟶ D => G.obj x) (fac F)).symm
        (congrArg (fun G : C ⟶ D => G.obj y) (fac F)).symm) := by
  exact (EnrichedFunctor.homMap_transport_of_eq (fac F).symm x y).symm

/-- The actual left leg is a genuine global C0 cofibration. -/
theorem left_cofibration {C D : Carrier.{u}} (F : C ⟶ D) : cofibrations (data F).i :=
  fixedCofibration_global _ (FixedObjectModel.trivialCofibrations_le_cofibrations _
    (FreeFactorization.horn (CarrierReindexing.fixedPart F)).hi)

/-- The actual left leg is weak on every original Hom and essentially surjective on the SAME component objects. -/
theorem left_weak {C D : Carrier.{u}} (F : C ⟶ D) : EnrichedDwyerKan.weakEquivalences (data F).i :=
  (EnrichedDwyerKan.fixedWeak_iff _).mpr
    (FixedObjectModel.trivialCofibrations_le_weakEquivalences _
      (FreeFactorization.horn (CarrierReindexing.fixedPart F)).hi)

/-- The original right leg is a fibration on every full original Hom, without a target Kan premise. -/
theorem right_homFibration {C D : Carrier.{u}} (F : C ⟶ D) : homFibrations (data F).p := (data F).hp

instance hasFactorization : MorphismProperty.HasFactorization homHornLeft.{u} homFibrations where
  nonempty_mapFactorizationData F := ⟨data F⟩

/-- The actual full-Hom fibration class is stable under original enriched arrow retracts. -/
instance homFibrations_retracts : homFibrations.{u}.IsStableUnderRetracts := by
  rw [← generatingHomHorns_rlp_eq]
  infer_instance

/-- The actual Hom-horn factorization supplies the full weak factorization system. -/
instance weakFactorizationSystem : MorphismProperty.IsWeakFactorizationSystem homHornLeft.{u} homFibrations :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun _i p hi hp => hi p hp)

/-- Every original global Hom-horn left map is both a genuine C0 cofibration and the SAME original DK weak map. -/
theorem homHornLeft_le_cofibration_inf_weak :
    homHornLeft.{u} ≤ cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  intro C D F hF
  let φ := data F
  let _ : HasLiftingProperty F φ.p := hF φ.p φ.hp
  let h := RetractArrow.ofLeftLiftingProperty φ.fac
  exact ⟨MorphismProperty.of_retract h (left_cofibration F),
    EnrichedDwyerKan.weak_of_retract h (left_weak F)⟩

end CategoryTheory.SimplicialEnrichment.Bergner.HornFactorization
