/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierLabelMaps

/-! # Exact full carrier readback through prescribed original labels

An actual enriched functor with a proved equation at every original
label vertex gives a genuine map into the canonical reindexed target.
Every original identity, composition and whole Hom map is transported
only through those endpoint equations. Projection recovers the entire
original functor, including objects outside a literal carrier presentation.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CarrierLabelReadback
open FixedObjects

variable {O : Type u} (C : FixedObjects O) {D : Carrier.{u}}
variable (b : O → D) (F : C.val ⟶ D) (h : ∀ x, F.obj (vertex C x) = b x)

/-- The same entire original Hom map, with only its two proved endpoint transports. -/
def originalHom (x y : O) : hom C x y ⟶ hom (CarrierReindexing.object D b) x y :=
  F.map (vertex C x) (vertex C y) ≫ eqToHom (by rw [h x, h y]; rfl)

private theorem originalHom_identity (x : O) :
    identityMap C x ≫ originalHom C b F h x x =
      identityMap (CarrierReindexing.object D b) x := by
  change eId SSet.{u} (vertex C x) ≫
    (F.map (vertex C x) (vertex C x) ≫ eqToHom _) = eId SSet.{u} (b x)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ eqToHom (by rw [h x])) (F.map_id (vertex C x))).trans
      (identity_eqToHom D (h x)))

private theorem originalHom_composition (x y z : O) :
    compositionMap C x y z ≫ originalHom C b F h x z =
      (originalHom C b F h x y ⊗ₘ originalHom C b F h y z) ≫
        compositionMap (CarrierReindexing.object D b) x y z := by
  have hf := congrArg (fun k => k ≫ eqToHom (by rw [h x, h z]))
    (F.map_comp (vertex C x) (vertex C y) (vertex C z))
  have ht := composition_eqToHom D (h x) (h y) (h z)
  have hh := congrArg (fun k =>
    (F.map (vertex C x) (vertex C y) ⊗ₘ F.map (vertex C y) (vertex C z)) ≫ k) ht
  change eComp SSet.{u} (vertex C x) (vertex C y) (vertex C z) ≫
      (F.map (vertex C x) (vertex C z) ≫ eqToHom _) =
    ((F.map (vertex C x) (vertex C y) ≫ eqToHom _) ⊗ₘ
      (F.map (vertex C y) (vertex C z) ≫ eqToHom _)) ≫ eComp SSet.{u} (b x) (b y) (b z)
  simpa only [Category.assoc, ← tensorHom_comp_tensorHom] using
    (Category.assoc _ _ _).symm.trans (hf.trans ((Category.assoc _ _ _).trans hh))

/-- Construct the genuine fixed-label map from its actual whole functor and original vertex
equations. -/
def map : C ⟶ CarrierReindexing.object D b :=
  ofHomMaps (originalHom C b F h) (originalHom_identity C b F h) (originalHom_composition C b F h)

/-- Each actual source object keeps its own original label in the reindexed target. -/
theorem map_obj (x : C.val) : (map C b F h).val.obj x = label C x := rfl

/-- Every whole original Hom is read back with precisely the prescribed endpoint transports. -/
theorem homMap_map (x y : O) : homMap (map C b F h) x y = originalHom C b F h x y :=
  homMap_ofHomMaps _ _ _ x y

/-- The same entire original carrier functor is recovered by the canonical projection. -/
theorem map_fac : (map C b F h).val ≫ CarrierReindexing.toTarget D b = F := by
  refine EnrichedFunctor.ext SSet.{u}
    (F := (map C b F h).val ≫ CarrierReindexing.toTarget D b) (G := F) (fun x => ?_) ?_
  · change b (label C x) = F.obj x
    have hx := h (label C x)
    rw [vertex_label] at hx
    exact hx.symm
  · intro x y
    obtain ⟨s, hs⟩ := (FixedObjects.verticesEquiv C).surjective x
    obtain ⟨t, ht⟩ := (FixedObjects.verticesEquiv C).surjective y
    change vertex C s = x at hs
    change vertex C t = y at ht
    subst x
    subst y
    let G := map C b F h
    have hsG : G.val.obj (vertex C s) = s := map_vertex G s
    have htG : G.val.obj (vertex C t) = t := map_vertex G t
    let hb : hom (CarrierReindexing.object D b) s t =
        (F.obj (vertex C s) ⟶[SSet.{u}] F.obj (vertex C t)) :=
      congrArg₂ (fun x y : D => (x ⟶[SSet.{u}] y)) (h s).symm (h t).symm
    have hm : originalHom C b F h s t ≫ eqToHom hb =
        F.map (vertex C s) (vertex C t) := by
      unfold originalHom
      erw [Category.assoc, eqToHom_trans]
      simp only [eqToHom_refl, Category.comp_id]
    have he := (congrArg
      (fun k : hom C s t ⟶ hom (CarrierReindexing.object D b) s t => k ≫ eqToHom hb)
      (homMap_map C b F h s t)).trans hm
    unfold FixedObjects.homMap at he
    erw [Category.assoc, eqToHom_trans] at he
    let hp : (G.val.obj (vertex C s) ⟶[SSet.{u}] G.val.obj (vertex C t)) =
        (F.obj (vertex C s) ⟶[SSet.{u}] F.obj (vertex C t)) :=
      congrArg₂ (fun x y : D => (x ⟶[SSet.{u}] y))
        ((congrArg b hsG).trans (h s).symm) ((congrArg b htG).trans (h t).symm)
    change (G.val.map (vertex C s) (vertex C t) ≫ 𝟙 _) ≫ eqToHom hp =
      F.map (vertex C s) (vertex C t)
    simpa only [Category.comp_id] using he

/-- Any fixed-label map retaining that same whole original functor is the actual constructed map. -/
theorem map_unique (G : C ⟶ CarrierReindexing.object D b)
    (hG : G.val ≫ CarrierReindexing.toTarget D b = F) : G = map C b F h :=
  CarrierLabelMaps.projection_injective b (hG.trans (map_fac C b F h).symm)

end CategoryTheory.SimplicialEnrichment.CarrierLabelReadback
