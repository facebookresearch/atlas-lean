/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerObjectAddition
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerLocalClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFactorizations

/-!
# A genuine global Bergner boundary weak factorization system

For every original varying-object enriched map, first add the full
original target-object family. Then apply the actual original fixed-label
free boundary small-object construction to the reindexed augmentation.
The original global left-lifting transfer proves the composite is a
genuine C0 cofibration. The second leg is literally surjective on objects
and a scalar trivial fibration on EVERY whole original Hom, hence is in
the full original C0 right class. Both legs compose to the same entire
original enriched functor. This constructs the genuine global weak
factorization system, rather than assuming a global model structure.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner.BoundaryFactorization
open FixedObjects

/-- Factor EVERY original changing-object map through the actual object addition and original fixed-label free
boundary construction. -/
def data {C D : Carrier.{u}} (F : C ⟶ D) :
    MorphismProperty.MapFactorizationData cofibrations generatingCofibrations.rlp F := by
  let A : Carrier.{u} := BergnerObjectAddition.object F
  let R : A ⟶ D := BergnerObjectAddition.right F
  let fixed := CarrierReindexing.fixedPart R
  let φ := FreeFactorization.boundary fixed
  let projection := CarrierReindexing.toTarget D R.obj
  have fixed_fac : φ.i.val ≫ φ.p.val = fixed.val :=
    congrArg (fun G : CarrierReindexing.source A ⟶ CarrierReindexing.object D R.obj => G.val) φ.fac
  refine {
    Z := φ.Z.val
    i := BergnerObjectAddition.left F ≫ φ.i.val
    p := φ.p.val ≫ projection
    fac := ?_
    hi := ?_
    hp := ?_ }
  · calc
      (BergnerObjectAddition.left F ≫ φ.i.val) ≫ (φ.p.val ≫ projection) =
          BergnerObjectAddition.left F ≫ ((φ.i.val ≫ φ.p.val) ≫ projection) := by
            simp only [Category.assoc]
      _ = BergnerObjectAddition.left F ≫ (fixed.val ≫ projection) :=
        congrArg (fun G => BergnerObjectAddition.left F ≫ (G ≫ projection)) fixed_fac
      _ = BergnerObjectAddition.left F ≫ R :=
        congrArg (fun G => BergnerObjectAddition.left F ≫ G) (CarrierReindexing.factorization R)
      _ = F := BergnerObjectAddition.fac F
  · exact cofibrations.comp_mem _ _ (BergnerObjectAddition.left_cofibration F)
      (fixedCofibration_global φ.i φ.hi)
  · apply (generatingCofibrations_rlp_original_iff (φ.p.val ≫ projection)).mpr
    constructor
    · intro d
      obtain ⟨a, ha⟩ := BergnerObjectAddition.right_objects_surjective F d
      refine ⟨vertex φ.Z a, ?_⟩
      change R.obj (φ.p.val.obj (vertex φ.Z a)) = d
      rw [map_vertex φ.p a]
      exact ha
    · intro x y
      change Fibration (φ.p.val.map x y ≫ 𝟙 _) ∧
        SSet.realizationWeakEquivalences (φ.p.val.map x y ≫ 𝟙 _)
      simpa only [Category.comp_id] using FreeFactorization.boundary_p_original fixed x y

/-- The actual complete global boundary factorization recovers the SAME original strict enriched functor. -/
theorem fac {C D : Carrier.{u}} (F : C ⟶ D) : (data F).i ≫ (data F).p = F := (data F).fac

/-- Its first full original map is a genuine global C0 cofibration. -/
theorem left_cofibration {C D : Carrier.{u}} (F : C ⟶ D) : cofibrations (data F).i := (data F).hi

/-- Its second full original map lies in the genuine all-arity global C0 right class. -/
theorem right_generator_class {C D : Carrier.{u}} (F : C ⟶ D) :
    generatingCofibrations.rlp (data F).p := (data F).hp

/-- The SAME actual second map is an original local fibration and genuine original enriched Dwyer–Kan weak
equivalence. -/
theorem right_original_classes {C D : Carrier.{u}} (F : C ⟶ D) :
    localFibrations (data F).p ∧ EnrichedDwyerKan.weakEquivalences (data F).p :=
  ⟨generatingCofibrations_right_localFibration _ (data F).hp,
    generatingCofibrations_right_weak _ (data F).hp⟩

/-- The actual second map is literally surjective on the SAME individual original target objects. -/
theorem right_objects_surjective {C D : Carrier.{u}} (F : C ⟶ D) :
    Function.Surjective (data F).p.obj :=
  generatingCofibrations_right_object_surjective _ (data F).hp

/-- Every entire original Hom map of the same actual second leg is a genuine scalar trivial fibration. -/
theorem right_original_homs {C D : Carrier.{u}} (F : C ⟶ D) (x y : (data F).Z) :
    Fibration ((data F).p.map x y) ∧ SSet.realizationWeakEquivalences ((data F).p.map x y) :=
  (generatingCofibrations_rlp_original_iff _).mp (data F).hp |>.2 x y

private theorem map_heq_of_eq {C D : Carrier.{u}} {F G : C ⟶ D} (h : F = G) (x y : C) :
    HEq (F.map x y) (G.map x y) := by
  cases h
  rfl

/-- The whole scalar composite is the SAME original Hom map, with its actual endpoint equality retained. -/
theorem original_hom_fac {C D : Carrier.{u}} (F : C ⟶ D) (x y : C) :
    HEq (((data F).i ≫ (data F).p).map x y) (F.map x y) := map_heq_of_eq (fac F) x y

/-- The whole actual object composite reads each original source object to its SAME original F image. -/
theorem original_obj_fac {C D : Carrier.{u}} (F : C ⟶ D) (x : C) :
    (data F).p.obj ((data F).i.obj x) = F.obj x :=
  congrArg (fun G : C ⟶ D => G.obj x) (fac F)

/-- EVERY original map has the genuinely constructed global cofibration/C0-right factorization. -/
instance hasFactorization : MorphismProperty.HasFactorization cofibrations generatingCofibrations.rlp where
  nonempty_mapFactorizationData F := ⟨data F⟩

/-- The exact original global C0 left and right classes form a genuine complete weak factorization system. -/
instance weakFactorizationSystem :
    MorphismProperty.IsWeakFactorizationSystem cofibrations generatingCofibrations.rlp :=
  MorphismProperty.IsWeakFactorizationSystem.mk' _ _ (fun _i p hi hp => hi p hp)

/-- The genuine global weak factorization system uses the SAME original local-fibration and enriched DK-weak
intersection. -/
theorem weakFactorizationSystem_original :
    MorphismProperty.IsWeakFactorizationSystem cofibrations
      (localFibrations ⊓ EnrichedDwyerKan.weakEquivalences) := by
  rw [← generatingCofibrations_rlp_eq_localFibrations_inf_weak]
  infer_instance

end CategoryTheory.SimplicialEnrichment.Bergner.BoundaryFactorization
