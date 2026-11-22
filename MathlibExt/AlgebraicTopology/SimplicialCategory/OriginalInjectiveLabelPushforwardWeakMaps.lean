/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalInjectiveLabelPushforwardComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.SimplicialDisjointSumWeakMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelCarrierUnitNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanRetracts

/-!
# The SAME original injective label-pushforward preserves all full Hom weak maps

The actual whole comparison commutes with every original source functor.
Its entire conjugated map is the SAME original source map on the old
family and the identity on the actual isolated complement. Thus every
original Hom weak map is preserved, without cofibrancy or fibrancy
premises on either source or target.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.InjectiveLabelFamilies
open FixedObjects
attribute [local instance] SSet.DisjointSum.enrichment

variable {A O : Type u} (a : A → O) (ha : Function.Injective a) {C D : FixedObjects A}

/-- The SAME full original source functor and the identity on every actual unused label. -/
def familyMap (F : C ⟶ D) : family a C ⟶ family a D :=
  SSet.DisjointSum.map F.val (EnrichedFunctor.id SSet.{u} (isolated a).val)

/-- The actual old-family restriction retains the SAME entire original source functor. -/
theorem familyMap_inl (F : C ⟶ D) :
    DisjointCoproduct.inl C.val (isolated a).val ≫ familyMap a F =
      F.val ≫ DisjointCoproduct.inl D.val (isolated a).val :=
  SSet.DisjointSum.inl_desc
    (F.val.comp SSet.{u} (SSet.DisjointSum.inl D.val (isolated a).val))
    ((EnrichedFunctor.id SSet.{u} (isolated a).val).comp SSet.{u}
      (SSet.DisjointSum.inr D.val (isolated a).val))

/-- The actual unused-family restriction retains the SAME entire original inclusion. -/
theorem familyMap_inr (F : C ⟶ D) :
    DisjointCoproduct.inr C.val (isolated a).val ≫ familyMap a F =
      DisjointCoproduct.inr D.val (isolated a).val :=
  (SSet.DisjointSum.inr_desc
    (F.val.comp SSet.{u} (SSet.DisjointSum.inl D.val (isolated a).val))
    ((EnrichedFunctor.id SSet.{u} (isolated a).val).comp SSet.{u}
      (SSet.DisjointSum.inr D.val (isolated a).val))).trans
        (show (𝟙 (isolated a).val) ≫ DisjointCoproduct.inr D.val (isolated a).val =
          DisjointCoproduct.inr D.val (isolated a).val from Category.id_comp _)

/-- The SAME full original family map is DK weak from the actual original fixed Hom weak hypothesis. -/
theorem familyMap_weak (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences A F) :
    EnrichedDwyerKan.weakEquivalences (familyMap a F) := by
  refine ⟨?_, Functor.essSurj_of_surj ?_⟩
  · exact SSet.DisjointSum.map_local_weak F.val (EnrichedFunctor.id SSet.{u} (isolated a).val)
      ((FixedObjectModel.weakEquivalences_original_iff F).mp hF)
      (fun x y => SSet.realizationWeakEquivalences.id_mem (x ⟶[SSet.{u}] y))
  · intro p
    cases p with
    | inl d =>
        obtain ⟨c, hc⟩ := (objects_bijective F).surjective d
        exact ⟨Sum.inl c, congrArg Sum.inl hc⟩
    | inr i => exact ⟨Sum.inr i, rfl⟩

/-- The SAME full original pushforward/family comparison in the actual carrier category. -/
def fullIso (C : FixedObjects A) : (LabelPushforward.object a C).val ≅ family a C :=
  ((Functor.Fiber.fiberInclusion : FixedObjects O ⥤ Carrier.{u}).mapIso
    (pushforwardIso a ha C)) ≪≫ familyIso a ha C

/-- Its actual whole inverse is precisely the original family descender. -/
theorem fullIso_inv (C : FixedObjects A) : (fullIso a ha C).inv = fromFamily a C := by
  change (familyIso a ha C).inv ≫ ((familyIso a ha C).hom ≫ fromFamily a C) = fromFamily a C
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ fromFamily a C) (familyIso a ha C).inv_hom_id).trans (Category.id_comp _))

/-- The SAME actual old and isolated family maps give the entire original source-natural comparison square. -/
theorem familySquare (F : C ⟶ D) :
    (fromFamily a C ≫ (LabelPushforward.map a F).val) ≫ (toObject a ha D).val =
      familyMap a F ≫ (familyIso a ha D).inv := by
  let i := DisjointCoproduct.inl C.val (isolated a).val
  let j := DisjointCoproduct.inr C.val (isolated a).val
  let P := (fromFamily a C ≫ (LabelPushforward.map a F).val) ≫ (toObject a ha D).val
  let Q := familyMap a F ≫ (familyIso a ha D).inv
  have hi : i ≫ P = i ≫ Q := by
    calc
      i ≫ P = ((i ≫ fromFamily a C) ≫ (LabelPushforward.map a F).val) ≫ (toObject a ha D).val := by
        simp only [P, Category.assoc]
      _ = (LabelPushforward.carrierUnit a C ≫ (LabelPushforward.map a F).val) ≫ (toObject a ha D).val :=
        congrArg (fun k => (k ≫ (LabelPushforward.map a F).val) ≫ (toObject a ha D).val)
          (DisjointCoproduct.inl_desc (LabelPushforward.carrierUnit a C)
            (BergnerFixedInitialObjects.desc (complement a)
              (fun o => vertex (LabelPushforward.object a C) o.val)))
      _ = (F.val ≫ LabelPushforward.carrierUnit a D) ≫ (toObject a ha D).val :=
        congrArg (fun k => k ≫ (toObject a ha D).val) (LabelPushforward.carrierUnit_naturality a F)
      _ = F.val ≫ (LabelPushforward.carrierUnit a D ≫ (toObject a ha D).val) := Category.assoc _ _ _
      _ = F.val ≫ inclusion a ha D := congrArg (fun k => F.val ≫ k) (toObject_unit a ha D)
      _ = (F.val ≫ DisjointCoproduct.inl D.val (isolated a).val) ≫ (familyIso a ha D).inv :=
        (Category.assoc _ _ _).symm
      _ = (i ≫ familyMap a F) ≫ (familyIso a ha D).inv :=
        congrArg (fun k => k ≫ (familyIso a ha D).inv) (familyMap_inl a F).symm
      _ = i ≫ Q := Category.assoc _ _ _
  have hj : j ≫ P = j ≫ Q := by
    apply (BergnerFixedInitialObjects.homEquiv (complement a) (object a ha D).val).injective
    funext o
    change (toObject a ha D).val.obj
      ((LabelPushforward.map a F).val.obj ((fromFamily a C).obj (Sum.inr (vertex (isolated a) o)))) =
        familyEquiv a ha D (Sum.inr (vertex (isolated a) o))
    have hs : (fromFamily a C).obj (Sum.inr (vertex (isolated a) o)) =
        vertex (LabelPushforward.object a C) o.val :=
      (fromFamily_vertex a ha C (Sum.inr (vertex (isolated a) o))).trans
        (congrArg (vertex (LabelPushforward.object a C)) (familyEquiv_inr a ha C o))
    exact (congrArg (fun z => (toObject a ha D).val.obj ((LabelPushforward.map a F).val.obj z)) hs).trans
      ((congrArg (toObject a ha D).val.obj (map_vertex (LabelPushforward.map a F) o.val)).trans
        ((map_vertex (toObject a ha D) o.val).trans (familyEquiv_inr a ha D o).symm))
  exact (DisjointCoproduct.desc_unique (i ≫ Q) (j ≫ Q) P hi hj).trans
    (DisjointCoproduct.desc_unique (i ≫ Q) (j ≫ Q) Q rfl rfl).symm

/-- The actual entire conjugated pushforward is the SAME original full map on both families. -/
theorem fullIso_conjugation (F : C ⟶ D) :
    ((fullIso a ha C).inv ≫ (LabelPushforward.map a F).val) ≫ (fullIso a ha D).hom = familyMap a F := by
  change ((fullIso a ha C).inv ≫ (LabelPushforward.map a F).val) ≫
    ((toObject a ha D).val ≫ (familyIso a ha D).hom) = familyMap a F
  rw [fullIso_inv, ← Category.assoc, familySquare]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => familyMap a F ≫ k) (familyIso a ha D).inv_hom_id).trans (Category.comp_id _))

/-- The SAME full original forward comparison is natural at every whole original source map. -/
theorem fullIso_naturality (F : C ⟶ D) :
    (LabelPushforward.map a F).val ≫ (fullIso a ha D).hom =
      (fullIso a ha C).hom ≫ familyMap a F :=
  (Iso.inv_comp_eq (fullIso a ha C)).mp
    ((Category.assoc _ _ _).symm.trans (fullIso_conjugation a ha F))

end CategoryTheory.SimplicialEnrichment.InjectiveLabelFamilies

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
open InjectiveLabelFamilies

/-- The SAME actual injective label-pushforward preserves all original Hom weak maps, without endpoint cofibrancy. -/
theorem map_weak_of_injective {A O : Type u} (a : A → O) (ha : Function.Injective a)
    {C D : FixedObjects A} (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences A F) :
    FixedObjectModel.weakEquivalences O (map a F) := by
  have h : EnrichedDwyerKan.weakEquivalences
      (((fullIso a ha C).inv ≫ (map a F).val) ≫ (fullIso a ha D).hom) :=
    (congrArg (fun k : family a C ⟶ family a D => EnrichedDwyerKan.weakEquivalences k)
      (fullIso_conjugation a ha F)).mpr (familyMap_weak a F hF)
  have h₁ := EnrichedDwyerKan.weakEquivalences.of_postcomp _ _
    (EnrichedDwyerKan.weakEquivalences.of_isIso (fullIso a ha D).hom) h
  exact (EnrichedDwyerKan.fixedWeak_iff (map a F)).mp
    (EnrichedDwyerKan.weakEquivalences.of_precomp _ _
      (EnrichedDwyerKan.weakEquivalences.of_isIso (fullIso a ha C).inv) h₁)

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
