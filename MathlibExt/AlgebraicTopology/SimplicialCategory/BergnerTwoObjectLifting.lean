/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectGenerators
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Global Bergner two-object lifting recognizes all original Hom lifts

For any changing-object strict enriched map F and any scalar map i,
lifting against the SAME original [1]_i map is equivalent to scalar
lifting against i on EVERY original Hom map of F. Both object images
and both whole enriched lift triangles are retained, including when
the two prescribed objects coincide and when the scalar domain is empty.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.BergnerTwoObject

variable {C D : Carrier.{u}} (F : C ⟶ D) {A B : SSet.{u}} (i : A ⟶ B)

/-- Every original global two-object lifting problem is exactly scalar lifting at EVERY original object pair. -/
theorem hasLiftingProperty_iff :
    HasLiftingProperty (map i) F ↔ ∀ x y : C, HasLiftingProperty i (F.map x y) := by
  constructor
  · intro h x y
    let _ := h
    refine ⟨fun {f g} sq => ?_⟩
    let top : object A ⟶ C := ofMap x y f
    let bottom : object B ⟶ D := ofMap (F.obj x) (F.obj y) g
    have hsq : top ≫ F = map i ≫ bottom := by
      calc
        _ = ofMap (F.obj x) (F.obj y) (f ≫ F.map x y) := ofMap_comp x y f F
        _ = ofMap (F.obj x) (F.obj y) (i ≫ g) := congrArg (ofMap (F.obj x) (F.obj y)) sq.w
        _ = _ := (map_ofMap i (F.obj x) (F.obj y) g).symm
    let big : CommSq top (map i) F bottom := ⟨hsq⟩
    let L := big.lift
    have hs : L.obj (source B) = x :=
      congrArg (fun k : object A ⟶ C => k.obj (source A)) big.fac_left
    have ht : L.obj (target B) = y :=
      congrArg (fun k : object A ⟶ C => k.obj (target A)) big.fac_left
    let l : B ⟶ x ⟶[SSet.{u}] y := (fixedEndpointsEquiv x y) ⟨L, hs, ht⟩
    have hL : ofMap x y l = L :=
      congrArg Subtype.val ((fixedEndpointsEquiv x y).symm_apply_apply ⟨L, hs, ht⟩)
    have hleft : i ≫ l = f := by
      apply ofMap_injective x y
      calc
        _ = map i ≫ ofMap x y l := (map_ofMap i x y l).symm
        _ = map i ≫ L := congrArg (fun k => map i ≫ k) hL
        _ = ofMap x y f := big.fac_left
    have hright : l ≫ F.map x y = g := by
      apply ofMap_injective (F.obj x) (F.obj y)
      calc
        _ = ofMap x y l ≫ F := (ofMap_comp x y l F).symm
        _ = L ≫ F := congrArg (fun k => k ≫ F) hL
        _ = ofMap (F.obj x) (F.obj y) g := big.fac_right
    exact CommSq.HasLift.mk' ⟨l, hleft, hright⟩
  · intro h
    refine ⟨fun {top bottom} big => ?_⟩
    let x := top.obj (source A)
    let y := top.obj (target A)
    let f : A ⟶ x ⟶[SSet.{u}] y := top.map (source A) (target A)
    have hs : bottom.obj (source B) = F.obj x :=
      (congrArg (fun k : object A ⟶ D => k.obj (source A)) big.w).symm
    have ht : bottom.obj (target B) = F.obj y :=
      (congrArg (fun k : object A ⟶ D => k.obj (target A)) big.w).symm
    let g : B ⟶ F.obj x ⟶[SSet.{u}] F.obj y :=
      (fixedEndpointsEquiv (F.obj x) (F.obj y)) ⟨bottom, hs, ht⟩
    have htop : ofMap x y f = top := ofMap_readback top
    have hbottom : ofMap (F.obj x) (F.obj y) g = bottom :=
      congrArg Subtype.val ((fixedEndpointsEquiv (F.obj x) (F.obj y)).symm_apply_apply ⟨bottom, hs, ht⟩)
    have hsq : f ≫ F.map x y = i ≫ g := by
      apply ofMap_injective (F.obj x) (F.obj y)
      calc
        _ = ofMap x y f ≫ F := (ofMap_comp x y f F).symm
        _ = top ≫ F := congrArg (fun k => k ≫ F) htop
        _ = map i ≫ bottom := big.w
        _ = map i ≫ ofMap (F.obj x) (F.obj y) g := congrArg (fun k => map i ≫ k) hbottom.symm
        _ = ofMap (F.obj x) (F.obj y) (i ≫ g) := map_ofMap i (F.obj x) (F.obj y) g
    let _ := h x y
    let sq : CommSq f i (F.map x y) g := ⟨hsq⟩
    let l := ofMap x y sq.lift
    refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
    · exact (map_ofMap i x y sq.lift).trans
        ((congrArg (ofMap x y) sq.fac_left).trans htop)
    · exact (ofMap_comp x y sq.lift F).trans
        ((congrArg (ofMap (F.obj x) (F.obj y)) sq.fac_right).trans hbottom)

/-- The full right class of the actual scalar-generator images retains every original Hom map. -/
theorem mappedGenerators_rlp_iff (P : MorphismProperty SSet.{u}) :
    (P.map functor).rlp F ↔ ∀ x y : C, P.rlp (F.map x y) := by
  constructor
  · intro h x y A B i hi
    exact (hasLiftingProperty_iff F i).mp
      (h _ (MorphismProperty.map_mem_map P functor i hi)) x y
  · intro h A B i hi
    obtain ⟨X, Y, j, hj, ⟨e⟩⟩ := hi
    have hl : HasLiftingProperty (map j) F :=
      (hasLiftingProperty_iff F j).mpr (fun x y => h x y j hj)
    let _ : HasLiftingProperty (functor.map j) F := hl
    exact HasLiftingProperty.of_arrow_iso_left e F

end CategoryTheory.SimplicialEnrichment.BergnerTwoObject
