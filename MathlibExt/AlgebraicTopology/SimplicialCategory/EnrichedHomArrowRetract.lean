/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomEqualityTransport
import MathlibExt.CategoryTheory.Enriched.HomEqualityTransport
import Mathlib.CategoryTheory.Retract

/-!
# Actual original Hom arrows retain changing-object retracts

The full original enriched arrow retract gives the actual object
equations in both rows. Only those equations transport the endpoints
of every original scalar Hom map. The whole original functor equations
then prove both complete scalar squares and both retract identities.
No model, fibrancy or weak-map outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment

variable {A B C D : Carrier.{u}} {F : A ⟶ B} {G : C ⟶ D}

private theorem comp_obj {X Y Z : Carrier.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).obj x = g.obj (f.obj x) := rfl

private theorem identity_obj (X : Carrier.{u}) (x : X) : (𝟙 X : X ⟶ X).obj x = x := rfl

private theorem identity_map (X : Carrier.{u}) (x y : X) :
    (𝟙 X : X ⟶ X).map x y = 𝟙 (x ⟶[SSet.{u}] y) := rfl

/-- The SAME original source pair gives an actual retract of the full original Hom arrow
through the original
changing-object retract. -/
def originalHomArrowRetract (h : RetractArrow F G) (x y : A) :
    RetractArrow (F.map x y) (G.map (h.i.left.obj x) (h.i.left.obj y)) := by
  let S := h.i.left
  let T := h.i.right
  let R := h.r.left
  let Q := h.r.right
  have wholeTarget : S ≫ (G ≫ Q) = F := by
    change h.i.left ≫ (G ≫ h.r.right) = F
    rw [← Category.assoc, h.i_w, Category.assoc, h.retract_right, Category.comp_id]
  have hx : R.obj (S.obj x) = x := congrArg (fun K : A ⟶ A => K.obj x) h.retract_left
  have hy : R.obj (S.obj y) = y := congrArg (fun K : A ⟶ A => K.obj y) h.retract_left
  have ix : T.obj (F.obj x) = G.obj (S.obj x) := congrArg (fun K : A ⟶ D => K.obj x) h.i_w.symm
  have iy : T.obj (F.obj y) = G.obj (S.obj y) := congrArg (fun K : A ⟶ D => K.obj y) h.i_w.symm
  have tx : Q.obj (G.obj (S.obj x)) = F.obj x := congrArg (fun K : A ⟶ B => K.obj x) wholeTarget
  have ty : Q.obj (G.obj (S.obj y)) = F.obj y := congrArg (fun K : A ⟶ B => K.obj y) wholeTarget
  have ex : Q.obj (T.obj (F.obj x)) = F.obj x := congrArg (fun K : B ⟶ B =>
    K.obj (F.obj x)) h.retract_right
  have ey : Q.obj (T.obj (F.obj y)) = F.obj y := congrArg (fun K : B ⟶ B =>
    K.obj (F.obj y)) h.retract_right
  let sourceEq : (R.obj (S.obj x) ⟶[SSet.{u}] R.obj (S.obj y)) = (x ⟶[SSet.{u}] y) :=
    congrArg₂ (fun a b : A => (a ⟶[SSet.{u}] b)) hx hy
  let injectionEq : (T.obj (F.obj x) ⟶[SSet.{u}] T.obj (F.obj y)) =
      (G.obj (S.obj x) ⟶[SSet.{u}] G.obj (S.obj y)) :=
    congrArg₂ (fun a b : D => (a ⟶[SSet.{u}] b)) ix iy
  let targetEq : (Q.obj (G.obj (S.obj x)) ⟶[SSet.{u}] Q.obj (G.obj (S.obj y))) =
      (F.obj x ⟶[SSet.{u}] F.obj y) :=
    congrArg₂ (fun a b : B => (a ⟶[SSet.{u}] b)) tx ty
  let endEq : (Q.obj (T.obj (F.obj x)) ⟶[SSet.{u}] Q.obj (T.obj (F.obj y))) =
      (F.obj x ⟶[SSet.{u}] F.obj y) :=
    congrArg₂ (fun a b : B => (a ⟶[SSet.{u}] b)) ex ey
  let si := S.map x y
  let sr := R.map (S.obj x) (S.obj y) ≫ eqToHom sourceEq
  let ti := T.map (F.obj x) (F.obj y) ≫ eqToHom injectionEq
  let tr := Q.map (G.obj (S.obj x)) (G.obj (S.obj y)) ≫ eqToHom targetEq
  have injectionSquare : si ≫ G.map (S.obj x) (S.obj y) = F.map x y ≫ ti := by
    have hh := EnrichedFunctor.homMap_transport_of_eq h.i_w.symm x y
    simpa only [comp_map, comp_obj, Category.assoc] using hh.symm
  have sourceRetract : si ≫ sr = 𝟙 (x ⟶[SSet.{u}] y) := by
    have hh := EnrichedFunctor.homMap_transport_of_eq h.retract_left x y
    simpa only [comp_map, comp_obj, identity_obj, identity_map, Category.assoc] using hh
  have targetRetract : ti ≫ tr = 𝟙 (F.obj x ⟶[SSet.{u}] F.obj y) := by
    have move := (EnrichedHomEqualityTransport.functor_map Q ix iy).symm
    dsimp only [EnrichedHomEqualityTransport.hom] at move
    have hh := EnrichedFunctor.homMap_transport_of_eq h.retract_right (F.obj x) (F.obj y)
    change (T.map (F.obj x) (F.obj y) ≫ eqToHom injectionEq) ≫
      (Q.map (G.obj (S.obj x)) (G.obj (S.obj y)) ≫ eqToHom targetEq) = _
    rw [Category.assoc, ← Category.assoc (eqToHom injectionEq), move]
    simpa only [comp_map, comp_obj, identity_obj, identity_map, Category.assoc,
      eqToHom_trans] using hh
  have retractionSquare : sr ≫ F.map x y = G.map (S.obj x) (S.obj y) ≫ tr := by
    have move := (EnrichedHomEqualityTransport.functor_map F hx hy).symm
    dsimp only [EnrichedHomEqualityTransport.hom] at move
    have hh := EnrichedFunctor.homMap_transport_of_eq h.r_w (S.obj x) (S.obj y)
    let middleEq : (F.obj (R.obj (S.obj x)) ⟶[SSet.{u}] F.obj (R.obj (S.obj y))) =
        (Q.obj (G.obj (S.obj x)) ⟶[SSet.{u}] Q.obj (G.obj (S.obj y))) :=
      congrArg₂ (fun a b : B => (a ⟶[SSet.{u}] b))
        (congrArg (fun K : C ⟶ B => K.obj (S.obj x)) h.r_w)
        (congrArg (fun K : C ⟶ B => K.obj (S.obj y)) h.r_w)
    have join : eqToHom middleEq ≫ eqToHom targetEq =
        eqToHom (congrArg₂ (fun a b : B => (a ⟶[SSet.{u}] b))
          (congrArg F.obj hx) (congrArg F.obj hy)) := by
      rw [eqToHom_trans]
    have after := congrArg
      (fun k : (S.obj x ⟶[SSet.{u}] S.obj y) ⟶
        (Q.obj (G.obj (S.obj x)) ⟶[SSet.{u}] Q.obj (G.obj (S.obj y))) => k ≫ eqToHom targetEq) hh
    change (R.map (S.obj x) (S.obj y) ≫ F.map (R.obj (S.obj x)) (R.obj (S.obj y)) ≫
      eqToHom middleEq) ≫ eqToHom targetEq =
      (G.map (S.obj x) (S.obj y) ≫ Q.map (G.obj (S.obj x)) (G.obj (S.obj y))) ≫
        eqToHom targetEq at after
    rw [Category.assoc, Category.assoc, join] at after
    change (R.map (S.obj x) (S.obj y) ≫ eqToHom sourceEq) ≫ F.map x y =
      G.map (S.obj x) (S.obj y) ≫ (Q.map (G.obj (S.obj x)) (G.obj (S.obj y)) ≫ eqToHom targetEq)
    rw [Category.assoc, move]
    exact after
  refine {
    i := Arrow.homMk si ti injectionSquare
    r := Arrow.homMk sr tr retractionSquare
    retract := ?_ }
  apply Arrow.hom_ext
  · exact sourceRetract
  · exact targetRetract

end CategoryTheory.SimplicialEnrichment
