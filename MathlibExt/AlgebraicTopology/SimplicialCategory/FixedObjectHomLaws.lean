/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabels

/-!
# Actual identity and composition on fixed-label Hom maps

The fixed-object Hom evaluation retains the original enriched identities
and composition. These equations follow from the original enriched map
and its exact endpoint equalities, and assemble Hom diagrams without a
supplied colimit or model-law certificate.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- The original identity at the individually supplied fixed object label. -/
abbrev identityMap (C : FixedObjects O) (x : O) : 𝟙_ SSet.{u} ⟶ hom C x x :=
  eId SSet.{u} (vertex C x)

/-- The original enriched composition at three individually supplied labels. -/
abbrev compositionMap (C : FixedObjects O) (x y z : O) :
    hom C x y ⊗ hom C y z ⟶ hom C x z :=
  eComp SSet.{u} (vertex C x) (vertex C y) (vertex C z)

/-- Equality of original vertices transports the entire original enriched identity. -/
theorem identity_eqToHom (C : Carrier.{u}) {a b : C} (h : a = b) :
    eId SSet.{u} a ≫ eqToHom (by rw [h] : (a ⟶[SSet.{u}] a) = (b ⟶[SSet.{u}] b)) =
      eId SSet.{u} b := by
  cases h
  exact Category.comp_id _

/-- Equality of three original vertices transports the entire original enriched composition. -/
theorem composition_eqToHom (C : Carrier.{u}) {a b c a' b' c' : C}
    (ha : a = a') (hb : b = b') (hc : c = c') :
    eComp SSet.{u} a b c ≫ eqToHom (by rw [ha, hc] :
      (a ⟶[SSet.{u}] c) = (a' ⟶[SSet.{u}] c')) =
        (eqToHom (by rw [ha, hb] : (a ⟶[SSet.{u}] b) = (a' ⟶[SSet.{u}] b')) ⊗ₘ
          eqToHom (by rw [hb, hc] : (b ⟶[SSet.{u}] c) = (b' ⟶[SSet.{u}] c'))) ≫
            eComp SSet.{u} a' b' c' := by
  cases ha
  cases hb
  cases hc
  simp

/-- The same original fixed-object map preserves the whole enriched identity. -/
theorem identityMap_homMap {C D : FixedObjects O} (F : C ⟶ D) (x : O) :
    identityMap C x ≫ homMap F x x = identityMap D x := by
  change eId SSet.{u} (vertex C x) ≫
      (F.val.map (vertex C x) (vertex C x) ≫ eqToHom _) = eId SSet.{u} (vertex D x)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ eqToHom _) (F.val.map_id (vertex C x))).trans
      (identity_eqToHom D.val (map_vertex F x)))

/-- The same original fixed-object map preserves the whole enriched binary composition. -/
theorem compositionMap_homMap {C D : FixedObjects O} (F : C ⟶ D) (x y z : O) :
    compositionMap C x y z ≫ homMap F x z =
      (homMap F x y ⊗ₘ homMap F y z) ≫ compositionMap D x y z := by
  have hF := congrArg (fun k => k ≫ eqToHom
      (by rw [map_vertex F x, map_vertex F z]))
    (F.val.map_comp (vertex C x) (vertex C y) (vertex C z))
  have ht := composition_eqToHom D.val (map_vertex F x) (map_vertex F y) (map_vertex F z)
  have hT := congrArg (fun k =>
    (F.val.map (vertex C x) (vertex C y) ⊗ₘ F.val.map (vertex C y) (vertex C z)) ≫ k) ht
  change eComp SSet.{u} (vertex C x) (vertex C y) (vertex C z) ≫
      (F.val.map (vertex C x) (vertex C z) ≫ eqToHom _) =
    ((F.val.map (vertex C x) (vertex C y) ≫ eqToHom _) ⊗ₘ
      (F.val.map (vertex C y) (vertex C z) ≫ eqToHom _)) ≫
        eComp SSet.{u} (vertex D x) (vertex D y) (vertex D z)
  simpa only [Category.assoc, ← tensorHom_comp_tensorHom] using
    (Category.assoc _ _ _).symm.trans (hF.trans
      ((Category.assoc _ _ _).trans hT))

end CategoryTheory.SimplicialEnrichment.FixedObjects
