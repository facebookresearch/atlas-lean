/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementSupport
import MathlibExt.CategoryTheory.Subfunctor.PreimagePullback

/-!
# Original subpresheaf lifts and pullbacks

A literal subfunctor of the canonical product-site carrier realizes to an
original simplicial space. Range containment gives an original lift into that
realization. Preimage subfunctors realize the literal categorical pullback,
with both original projections, cardinal bounds, and the canonical Arrow map
retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace

/-- Inclusion of one original realized subpresheaf into another. -/
def originalSubpresheafMapOfLE {X : SimplicialSpace.{u}}
    {U V : Subfunctor (toPresheaf.obj X)} (h : U ≤ V) :
    originalSubpresheafObject U ⟶ originalSubpresheafObject V :=
  equivalencePresheaf.inverse.map (Subfunctor.homOfLe h)

instance originalSubpresheafMapOfLE_mono {X : SimplicialSpace.{u}}
    {U V : Subfunctor (toPresheaf.obj X)} (h : U ≤ V) :
    Mono (originalSubpresheafMapOfLE h) := by
  let _ : equivalencePresheaf.inverse.PreservesMonomorphisms := inferInstance
  change Mono (equivalencePresheaf.inverse.map (Subfunctor.homOfLe h))
  infer_instance

@[reassoc (attr := simp)]
theorem originalSubpresheafMapOfLE_inclusion {X : SimplicialSpace.{u}}
    {U V : Subfunctor (toPresheaf.obj X)} (h : U ≤ V) :
    originalSubpresheafMapOfLE h ≫ originalSubpresheafInclusion V =
      originalSubpresheafInclusion U := by
  change equivalencePresheaf.inverse.map (Subfunctor.homOfLe h) ≫
      (equivalencePresheaf.inverse.map V.ι ≫
        (equivalencePresheaf.unitIso.app X).inv) =
    equivalencePresheaf.inverse.map U.ι ≫
      (equivalencePresheaf.unitIso.app X).inv
  rw [← Category.assoc, ← equivalencePresheaf.inverse.map_comp,
    Subfunctor.homOfLe_ι]

/-- An original map whose canonical presheaf range lies in U lifts to the
original inverse-equivalence realization of U. -/
def originalSubpresheafLift {A Y : SimplicialSpace.{u}} (f : A ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y))
    (hf : Subfunctor.range (toPresheaf.map f) ≤ U) :
    A ⟶ originalSubpresheafObject U :=
  (equivalencePresheaf.unitIso.app A).hom ≫
    equivalencePresheaf.inverse.map
      (Subfunctor.lift (toPresheaf.map f) hf)

@[reassoc (attr := simp)]
theorem originalSubpresheafLift_inclusion {A Y : SimplicialSpace.{u}}
    (f : A ⟶ Y) (U : Subfunctor (toPresheaf.obj Y))
    (hf : Subfunctor.range (toPresheaf.map f) ≤ U) :
    originalSubpresheafLift f U hf ≫ originalSubpresheafInclusion U = f := by
  change ((equivalencePresheaf.unitIso.app A).hom ≫
      equivalencePresheaf.inverse.map
        (Subfunctor.lift (toPresheaf.map f) hf)) ≫
      (equivalencePresheaf.inverse.map U.ι ≫
        (equivalencePresheaf.unitIso.app Y).inv) = f
  have hmap : equivalencePresheaf.inverse.map
        (Subfunctor.lift (toPresheaf.map f) hf) ≫
      equivalencePresheaf.inverse.map U.ι =
        equivalencePresheaf.inverse.map (toPresheaf.map f) := by
    rw [← equivalencePresheaf.inverse.map_comp, Subfunctor.lift_ι]
  have hunit : (equivalencePresheaf.unitIso.app A).hom ≫
      equivalencePresheaf.inverse.map (toPresheaf.map f) =
        f ≫ (equivalencePresheaf.unitIso.app Y).hom := by
    change equivalencePresheaf.unitIso.hom.app A ≫
        equivalencePresheaf.inverse.map (equivalencePresheaf.functor.map f) =
      f ≫ equivalencePresheaf.unitIso.hom.app Y
    exact (equivalencePresheaf.unitIso.hom.naturality f).symm
  calc
    _ = (equivalencePresheaf.unitIso.app A).hom ≫
          (equivalencePresheaf.inverse.map
            (Subfunctor.lift (toPresheaf.map f) hf) ≫
              equivalencePresheaf.inverse.map U.ι) ≫
            (equivalencePresheaf.unitIso.app Y).inv := by simp only [Category.assoc]
    _ = (equivalencePresheaf.unitIso.app A).hom ≫
          equivalencePresheaf.inverse.map (toPresheaf.map f) ≫
            (equivalencePresheaf.unitIso.app Y).inv := by rw [hmap]
    _ = (f ≫ (equivalencePresheaf.unitIso.app Y).hom) ≫
          (equivalencePresheaf.unitIso.app Y).inv := by
            have hh := congrArg
              (fun k => k ≫ (equivalencePresheaf.unitIso.app Y).inv)
              hunit
            simpa only [Category.assoc] using hh
    _ = f := by simp

/-- The literal preimage of U under an original map, on the canonical
product-site carrier. -/
def originalSubpresheafPreimage {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) : Subfunctor (toPresheaf.obj X) :=
  U.preimage (toPresheaf.map f)

/-- The original map from the realized preimage to the realized target
subpresheaf. -/
def originalSubpresheafPreimageMap {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) :
    originalSubpresheafObject (originalSubpresheafPreimage f U) ⟶
      originalSubpresheafObject U :=
  equivalencePresheaf.inverse.map
    (U.fromPreimage (toPresheaf.map f))

@[reassoc]
theorem originalSubpresheafPreimage_square {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (U : Subfunctor (toPresheaf.obj Y)) :
    originalSubpresheafInclusion (originalSubpresheafPreimage f U) ≫ f =
      originalSubpresheafPreimageMap f U ≫ originalSubpresheafInclusion U := by
  change (equivalencePresheaf.inverse.map
      (U.preimage (toPresheaf.map f)).ι ≫
        (equivalencePresheaf.unitIso.app X).inv) ≫ f =
    equivalencePresheaf.inverse.map
        (U.fromPreimage (toPresheaf.map f)) ≫
      (equivalencePresheaf.inverse.map U.ι ≫
        (equivalencePresheaf.unitIso.app Y).inv)
  have hunit : (equivalencePresheaf.unitIso.app X).inv ≫ f =
      equivalencePresheaf.inverse.map (toPresheaf.map f) ≫
        (equivalencePresheaf.unitIso.app Y).inv := by
    change equivalencePresheaf.unitIso.inv.app X ≫ f =
      equivalencePresheaf.inverse.map (equivalencePresheaf.functor.map f) ≫
        equivalencePresheaf.unitIso.inv.app Y
    exact (equivalencePresheaf.unitIso.inv.naturality f).symm
  calc
    _ = equivalencePresheaf.inverse.map
          (U.preimage (toPresheaf.map f)).ι ≫
        (equivalencePresheaf.inverse.map (toPresheaf.map f) ≫
          (equivalencePresheaf.unitIso.app Y).inv) := by
            have hh := congrArg
              (fun k => equivalencePresheaf.inverse.map
                (U.preimage (toPresheaf.map f)).ι ≫ k)
              hunit
            simpa only [Category.assoc] using hh
    _ = equivalencePresheaf.inverse.map
          ((U.preimage (toPresheaf.map f)).ι ≫ toPresheaf.map f) ≫
        (equivalencePresheaf.unitIso.app Y).inv := by
          rw [equivalencePresheaf.inverse.map_comp, Category.assoc]
    _ = equivalencePresheaf.inverse.map
          (U.fromPreimage (toPresheaf.map f) ≫ U.ι) ≫
        (equivalencePresheaf.unitIso.app Y).inv := by
          rw [Subfunctor.fromPreimage_ι]
    _ = _ := by rw [equivalencePresheaf.inverse.map_comp, Category.assoc]

/-- The original realized preimage square is a pullback. -/
theorem originalSubpresheafPreimage_isPullback {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (U : Subfunctor (toPresheaf.obj Y)) :
    IsPullback
      (originalSubpresheafInclusion (originalSubpresheafPreimage f U))
      (originalSubpresheafPreimageMap f U) f
      (originalSubpresheafInclusion U) := by
  let h := U.preimage_isPullback (toPresheaf.map f)
  have hm := h.map equivalencePresheaf.inverse
  exact hm.of_iso (Iso.refl _)
    (equivalencePresheaf.unitIso.app X).symm (Iso.refl _)
    (equivalencePresheaf.unitIso.app Y).symm rfl rfl
    (equivalencePresheaf.unitIso.inv.naturality f) rfl

instance originalSubpresheafPreimageMap_mono {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) [Mono f] (U : Subfunctor (toPresheaf.obj Y)) :
    Mono (originalSubpresheafPreimageMap f U) :=
  (originalSubpresheafPreimage_isPullback f U).mono_snd_of_mono

/-- The realized preimage is canonically the selected categorical pullback. -/
noncomputable def originalSubpresheafPreimageIsoPullback
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) :
    originalSubpresheafObject (originalSubpresheafPreimage f U) ≅
      pullback f (originalSubpresheafInclusion U) :=
  (originalSubpresheafPreimage_isPullback f U).isoPullback

@[reassoc (attr := simp)]
theorem originalSubpresheafPreimageIsoPullback_hom_fst
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) :
    (originalSubpresheafPreimageIsoPullback f U).hom ≫
        pullback.fst f (originalSubpresheafInclusion U) =
      originalSubpresheafInclusion (originalSubpresheafPreimage f U) :=
  (originalSubpresheafPreimage_isPullback f U).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem originalSubpresheafPreimageIsoPullback_hom_snd
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) :
    (originalSubpresheafPreimageIsoPullback f U).hom ≫
        pullback.snd f (originalSubpresheafInclusion U) =
      originalSubpresheafPreimageMap f U :=
  (originalSubpresheafPreimage_isPullback f U).isoPullback_hom_snd

/-- The raw total points of the realized preimage identify with those of the
selected categorical pullback. -/
def originalSubpresheafPreimageTotalPointsEquivPullback
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) :
    (Functor.uncurry.obj
      (originalSubpresheafObject (originalSubpresheafPreimage f U)).diagram).Elements ≃
    (Functor.uncurry.obj
      (pullback f (originalSubpresheafInclusion U)).diagram).Elements :=
  Functor.Elements.equivOfIso
    (Functor.uncurry.mapIso
      (SimplicialSpace.forget.mapIso
        (originalSubpresheafPreimageIsoPullback f U)))

/-- Under a monic original map, the native and realized preimage remain within
any supplied bound on U. -/
theorem originalSubpresheafPreimage_mk_elements_le
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) [Mono f]
    (U : Subfunctor (toPresheaf.obj Y)) (γ : Cardinal.{u})
    (hU : Cardinal.mk U.toFunctor.Elements ≤ γ) :
    Cardinal.mk (originalSubpresheafPreimage f U).toFunctor.Elements ≤ γ ∧
      Cardinal.mk (Functor.uncurry.obj
        (originalSubpresheafObject (originalSubpresheafPreimage f U)).diagram).Elements ≤ γ := by
  let _ : toPresheaf.{u}.PreservesMonomorphisms := inferInstance
  have hpre : Cardinal.mk (originalSubpresheafPreimage f U).toFunctor.Elements ≤ γ :=
    (U.mk_elements_preimage_le (toPresheaf.map f)).trans hU
  exact ⟨hpre,
    originalSubpresheaf_mk_elements_le (originalSubpresheafPreimage f U) γ hpre⟩

/-- Under a monic original map, the selected categorical pullback has at most
the supplied number of raw total points. -/
theorem originalSubpresheafPullback_mk_elements_le
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) [Mono f]
    (U : Subfunctor (toPresheaf.obj Y)) (γ : Cardinal.{u})
    (hU : Cardinal.mk U.toFunctor.Elements ≤ γ) :
    Cardinal.mk (Functor.uncurry.obj
      (pullback f (originalSubpresheafInclusion U)).diagram).Elements ≤ γ := by
  rw [← (originalSubpresheafPreimageTotalPointsEquivPullback f U).cardinal_eq]
  exact (originalSubpresheafPreimage_mk_elements_le f U γ hU).2

instance originalSubpresheafPullbackProjection_mono
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) [Mono f]
    (U : Subfunctor (toPresheaf.obj Y)) :
    Mono (pullback.snd f (originalSubpresheafInclusion U)) := inferInstance

/-- The literal pullback projection maps to the original arrow, retaining both
canonical pullback components. -/
def originalSubpresheafPullbackArrow {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (U : Subfunctor (toPresheaf.obj Y)) :
    Arrow.mk (pullback.snd f (originalSubpresheafInclusion U)) ⟶ Arrow.mk f :=
  Arrow.homMk (pullback.fst f (originalSubpresheafInclusion U))
    (originalSubpresheafInclusion U) pullback.condition

@[simp]
theorem originalSubpresheafPullbackArrow_left {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (U : Subfunctor (toPresheaf.obj Y)) :
    (originalSubpresheafPullbackArrow f U).left =
      pullback.fst f (originalSubpresheafInclusion U) := rfl

@[simp]
theorem originalSubpresheafPullbackArrow_right {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (U : Subfunctor (toPresheaf.obj Y)) :
    (originalSubpresheafPullbackArrow f U).right =
      originalSubpresheafInclusion U := rfl

end SimplicialSpace
