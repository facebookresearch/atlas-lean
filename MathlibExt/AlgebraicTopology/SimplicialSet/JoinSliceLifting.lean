/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction
public import MathlibExt.CategoryTheory.LiftingProperties.LeibnizMate
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Pushout join and slice lifting correspondences

This file formalizes both orientations of Joyal's Lemma 3.14. Restriction of
structured join division along `i : K₀ ⟶ K` is conjugate to the natural map
from pushout along `i` after joining by `K₀` to joining by `K`. The general
Leibniz mate theorem then identifies structured pushout-join squares with
slice-restriction squares, including their diagonal fillers and lifting
properties.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace SSet

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace sliceUnder
/-- Restriction of under-slices along a map of fixed left join factors. -/
def restrictionNatTrans {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    joinLeftDivision K ⟶ Under.map i ⋙ joinLeftDivision K₀ where
  app P := restrict P.right P.hom i
  naturality P Q q := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (join.map i).app (stdSimplex.obj n.unop) ≫ (g.1 ≫ q.right) =
      ((join.map i).app (stdSimplex.obj n.unop) ≫ g.1) ≫ q.right
    rw [Category.assoc]
end sliceUnder

/-- Join by `K₀`, followed by pushout of the structured source along `K₀ ⟶ K`. -/
noncomputable def joinUnderRestrictionLeft {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    SSet.{u} ⥤ Under K := joinUnder K₀ ⋙ Under.pushout i

/-- The composite adjunction for pushed-out structured left joins. -/
noncomputable def joinUnderRestrictionAdjunction {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) :
    joinUnderRestrictionLeft i ⊣ Under.map i ⋙ joinLeftDivision K₀ :=
  (joinUnderAdjunction K₀).comp (Under.mapPushoutAdj i)

/-- The natural map from pushed-out left joins to left join by the target. -/
noncomputable def joinUnderRestrictionNatTrans {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) : joinUnderRestrictionLeft i ⟶ joinUnder K where
  app A := Under.homMk
    (pushout.desc ((join.map i).app A) (joinInl K A) (by
      change joinInl K₀ A ≫ (join.map i).app A = i ≫ joinInl K A
      exact (map_comp_joinInl i A).symm))
    (by
      change pushout.inr (joinInl K₀ A) i ≫
        pushout.desc ((join.map i).app A) (joinInl K A) _ = joinInl K A
      exact pushout.inr_desc _ _ _)
  naturality A B a := by
    apply StructuredArrow.hom_ext
    change
      pushout.desc
          ((join.obj K₀).map a ≫ pushout.inl (joinInl K₀ B) i)
          (pushout.inr (joinInl K₀ B) i) _ ≫
        pushout.desc ((join.map i).app B) (joinInl K B) _ =
      pushout.desc ((join.map i).app A) (joinInl K A) _ ≫
        (join.obj K).map a
    apply (IsPushout.of_hasPushout (joinInl K₀ A) i).hom_ext
    · change
        (pushout.inl (joinInl K₀ A) i ≫
            pushout.desc
              ((join.obj K₀).map a ≫ pushout.inl (joinInl K₀ B) i)
              (pushout.inr (joinInl K₀ B) i) _) ≫
              pushout.desc ((join.map i).app B) (joinInl K B) _ =
          (pushout.inl (joinInl K₀ A) i ≫
            pushout.desc ((join.map i).app A) (joinInl K A) _) ≫
              (join.obj K).map a
      rw [pushout.inl_desc, Category.assoc, pushout.inl_desc,
        pushout.inl_desc]
      exact (join.map i).naturality a
    · change
        (pushout.inr (joinInl K₀ A) i ≫
            pushout.desc
              ((join.obj K₀).map a ≫ pushout.inl (joinInl K₀ B) i)
              (pushout.inr (joinInl K₀ B) i) _) ≫
              pushout.desc ((join.map i).app B) (joinInl K B) _ =
          (pushout.inr (joinInl K₀ A) i ≫
            pushout.desc ((join.map i).app A) (joinInl K A) _) ≫
              (join.obj K).map a
      rw [pushout.inr_desc, pushout.inr_desc, pushout.inr_desc,
        joinInl_comp_map]

lemma joinUnderRestrictionNatTrans_is_mate {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) :
    conjugateEquiv (joinUnderAdjunction K)
        (joinUnderRestrictionAdjunction i)
        (joinUnderRestrictionNatTrans i) =
      sliceUnder.restrictionNatTrans i := by
  apply NatTrans.ext
  funext P
  rw [conjugateEquiv_apply_app]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  simp [joinUnderRestrictionAdjunction, joinUnderAdjunction,
    joinUnderRestrictionLeft, joinUnderRestrictionNatTrans,
    sliceUnder.restrictionNatTrans, joinUnderHomEquiv,
    joinLeftDivision, sliceUnder.mapUnder, sliceUnder.lift,
    Under.map, joinUnder]
  rw [sliceUnder.evaluation_wholeMap]

end SSet

namespace SSet

/-- The raw pushout join of `i` and `a`, with fixed factor on the left. -/
noncomputable def joinUnderPushoutObjObj
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    join.PushoutObjObj i a :=
  Functor.PushoutObjObj.ofHasPushout join i a

/-- The underlying component of `joinUnderRestrictionNatTrans`. -/
noncomputable def joinUnderRestrictionAlphaMap {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) (A : SSet.{u}) :
    pushout (joinInl K₀ A) i ⟶ K ⋆ A :=
  pushout.desc ((join.map i).app A) (joinInl K A)
    ((map_comp_joinInl i A).symm)

lemma joinUnderRestrictionAlphaMap_eq {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) (A : SSet.{u}) :
    ((joinUnderRestrictionNatTrans i).app A).right =
      joinUnderRestrictionAlphaMap i A :=
  rfl

/-- The underlying map between the two structured pushout objects induced by `a`. -/
noncomputable def joinUnderRestrictionBaseMap
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    pushout (joinInl K₀ A) i ⟶ pushout (joinInl K₀ B) i :=
  pushout.desc
    ((join.obj K₀).map a ≫ pushout.inl (joinInl K₀ B) i)
    (pushout.inr (joinInl K₀ B) i) (by
      rw [← Category.assoc, joinInl_comp_map, pushout.condition])

lemma joinUnderRestrictionBaseMap_eq
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    ((joinUnderRestrictionLeft i).map a).right =
      joinUnderRestrictionBaseMap i a :=
  rfl

/-- The second coprojection into the structured pushout-join source. -/
noncomputable def joinUnderPushoutDesc
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    pushout (joinInl K₀ B) i ⟶ (joinUnderPushoutObjObj i a).pt :=
  pushout.desc (joinUnderPushoutObjObj i a).inr
    (joinInl K A ≫ (joinUnderPushoutObjObj i a).inl) (by
      symm
      rw [← Category.assoc, map_comp_joinInl, Category.assoc,
        (joinUnderPushoutObjObj i a).isPushout.w,
        ← Category.assoc, joinInl_comp_map])

/-- The source object in `Under K` of the structured pushout join. -/
noncomputable def joinUnderPushoutSource
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) : Under K :=
  Under.mk (joinInl K A ≫ (joinUnderPushoutObjObj i a).inl)

/-- The first coprojection into the structured pushout-join source. -/
noncomputable def joinUnderPushoutInl
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinUnder K).obj A ⟶ joinUnderPushoutSource i a :=
  Under.homMk (joinUnderPushoutObjObj i a).inl rfl

/-- The second structured coprojection into the pushout-join source. -/
noncomputable def joinUnderPushoutInr
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinUnderRestrictionLeft i).obj B ⟶ joinUnderPushoutSource i a :=
  Under.homMk (joinUnderPushoutDesc i a) (by
    exact pushout.inr_desc _ _ _)

/-- The structured pushout join in `Under K`; its right field is the raw pushout join. -/
noncomputable def joinUnderPushoutMap
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    joinUnderPushoutSource i a ⟶ (joinUnder K).obj B :=
  Under.homMk (joinUnderPushoutObjObj i a).ι (by
    change (joinInl K A ≫ (joinUnderPushoutObjObj i a).inl) ≫
      (joinUnderPushoutObjObj i a).ι = joinInl K B
    rw [Category.assoc, (joinUnderPushoutObjObj i a).inl_ι,
      joinInl_comp_map])

@[simp]
lemma joinUnderPushoutMap_right
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinUnderPushoutMap i a).right = (joinUnderPushoutObjObj i a).ι := rfl

lemma joinUnderRestrictionBaseSquare
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    IsPushout ((join.obj K₀).map a)
      (pushout.inl (joinInl K₀ A) i)
      (pushout.inl (joinInl K₀ B) i)
      (joinUnderRestrictionBaseMap i a) := by
  let hA := IsPushout.of_hasPushout (joinInl K₀ A) i
  let hB := IsPushout.of_hasPushout (joinInl K₀ B) i
  have hcomp : joinInl K₀ A ≫ (join.obj K₀).map a = joinInl K₀ B :=
    joinInl_comp_map K₀ a
  have hinr : pushout.inr (joinInl K₀ A) i ≫
      joinUnderRestrictionBaseMap i a = pushout.inr (joinInl K₀ B) i :=
    pushout.inr_desc _ _ _
  have houter : IsPushout
      (joinInl K₀ A ≫ (join.obj K₀).map a) i
      (pushout.inl (joinInl K₀ B) i)
      (pushout.inr (joinInl K₀ A) i ≫ joinUnderRestrictionBaseMap i a) :=
    hB.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      hcomp.symm (by simp) (by simp) hinr.symm
  exact houter.of_left (pushout.inl_desc _ _ _).symm hA

lemma joinUnderPushoutSquareUnderlying
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    IsPushout (joinUnderRestrictionAlphaMap i A) (joinUnderRestrictionBaseMap i a)
      (joinUnderPushoutObjObj i a).inl (joinUnderPushoutDesc i a) := by
  have hleft := (joinUnderRestrictionBaseSquare i a).flip
  have htop : pushout.inl (joinInl K₀ A) i ≫ joinUnderRestrictionAlphaMap i A =
      (join.map i).app A := pushout.inl_desc _ _ _
  have hbot : pushout.inl (joinInl K₀ B) i ≫ joinUnderPushoutDesc i a =
      (joinUnderPushoutObjObj i a).inr := pushout.inl_desc _ _ _
  have houter : IsPushout
      (pushout.inl (joinInl K₀ A) i ≫ joinUnderRestrictionAlphaMap i A)
      ((join.obj K₀).map a)
      (joinUnderPushoutObjObj i a).inl
      (pushout.inl (joinInl K₀ B) i ≫ joinUnderPushoutDesc i a) :=
    (joinUnderPushoutObjObj i a).isPushout.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      htop.symm (by simp) (by simp) hbot.symm
  have hinlAlpha : pushout.inl (joinInl K₀ A) i ≫
      joinUnderRestrictionAlphaMap i A = (join.map i).app A :=
    pushout.inl_desc _ _ _
  have hinrAlpha : pushout.inr (joinInl K₀ A) i ≫
      joinUnderRestrictionAlphaMap i A = joinInl K A :=
    pushout.inr_desc _ _ _
  have hinlBase : pushout.inl (joinInl K₀ A) i ≫
      joinUnderRestrictionBaseMap i a =
        (join.obj K₀).map a ≫ pushout.inl (joinInl K₀ B) i :=
    pushout.inl_desc _ _ _
  have hinrBase : pushout.inr (joinInl K₀ A) i ≫
      joinUnderRestrictionBaseMap i a = pushout.inr (joinInl K₀ B) i :=
    pushout.inr_desc _ _ _
  have hinlCorner : pushout.inl (joinInl K₀ B) i ≫
      joinUnderPushoutDesc i a = (joinUnderPushoutObjObj i a).inr :=
    pushout.inl_desc _ _ _
  have hinrCorner : pushout.inr (joinInl K₀ B) i ≫
      joinUnderPushoutDesc i a =
        joinInl K A ≫ (joinUnderPushoutObjObj i a).inl :=
    pushout.inr_desc _ _ _
  apply houter.of_left
  · apply (IsPushout.of_hasPushout (joinInl K₀ A) i).hom_ext
    · calc
        pushout.inl (joinInl K₀ A) i ≫
            (joinUnderRestrictionAlphaMap i A ≫ (joinUnderPushoutObjObj i a).inl) =
          (join.map i).app A ≫ (joinUnderPushoutObjObj i a).inl := by
            rw [← Category.assoc, hinlAlpha]
        _ = (join.obj K₀).map a ≫ (joinUnderPushoutObjObj i a).inr :=
          (joinUnderPushoutObjObj i a).isPushout.w
        _ = pushout.inl (joinInl K₀ A) i ≫
            (joinUnderRestrictionBaseMap i a ≫ joinUnderPushoutDesc i a) := by
          rw [← Category.assoc, hinlBase, Category.assoc, hinlCorner]
    · calc
        pushout.inr (joinInl K₀ A) i ≫
            (joinUnderRestrictionAlphaMap i A ≫ (joinUnderPushoutObjObj i a).inl) =
          joinInl K A ≫ (joinUnderPushoutObjObj i a).inl := by
            rw [← Category.assoc, hinrAlpha]
        _ = pushout.inr (joinInl K₀ A) i ≫
            (joinUnderRestrictionBaseMap i a ≫ joinUnderPushoutDesc i a) := by
          rw [← Category.assoc, hinrBase]
          exact hinrCorner.symm
  · exact hleft

lemma joinUnderPushoutSquare
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    IsPushout ((joinUnderRestrictionNatTrans i).app A)
      ((joinUnderRestrictionLeft i).map a)
      (joinUnderPushoutInl i a) (joinUnderPushoutInr i a) := by
  apply IsPushout.of_map (Under.forget K)
  · apply StructuredArrow.hom_ext
    change ((joinUnderRestrictionNatTrans i).app A).right ≫
        (joinUnderPushoutInl i a).right =
      ((joinUnderRestrictionLeft i).map a).right ≫
        (joinUnderPushoutInr i a).right
    rw [joinUnderRestrictionAlphaMap_eq, joinUnderRestrictionBaseMap_eq]
    exact (joinUnderPushoutSquareUnderlying i a).w
  · change IsPushout ((joinUnderRestrictionNatTrans i).app A).right
      ((joinUnderRestrictionLeft i).map a).right
      (joinUnderPushoutInl i a).right (joinUnderPushoutInr i a).right
    rw [joinUnderRestrictionAlphaMap_eq, joinUnderRestrictionBaseMap_eq]
    exact joinUnderPushoutSquareUnderlying i a

/-- The pushout-corner packet presenting `joinUnderPushoutMap` for the mate theorem. -/
noncomputable def joinUnderMatePushoutObjObj
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (parallelPair (joinUnderRestrictionNatTrans i)
      (joinUnderRestrictionNatTrans i)).PushoutObjObj
        WalkingParallelPairHom.left a where
  pt := joinUnderPushoutSource i a
  inl := joinUnderPushoutInl i a
  inr := joinUnderPushoutInr i a
  isPushout := joinUnderPushoutSquare i a
  ι := joinUnderPushoutMap i a
  inl_ι := by
    apply StructuredArrow.hom_ext
    exact (joinUnderPushoutObjObj i a).inl_ι
  inr_ι := by
    apply StructuredArrow.hom_ext
    have hinlCorner : pushout.inl (joinInl K₀ B) i ≫
        joinUnderPushoutDesc i a = (joinUnderPushoutObjObj i a).inr :=
      pushout.inl_desc _ _ _
    have hinrCorner : pushout.inr (joinInl K₀ B) i ≫
        joinUnderPushoutDesc i a =
          joinInl K A ≫ (joinUnderPushoutObjObj i a).inl :=
      pushout.inr_desc _ _ _
    have hinlAlpha : pushout.inl (joinInl K₀ B) i ≫
        joinUnderRestrictionAlphaMap i B = (join.map i).app B :=
      pushout.inl_desc _ _ _
    have hinrAlpha : pushout.inr (joinInl K₀ B) i ≫
        joinUnderRestrictionAlphaMap i B = joinInl K B :=
      pushout.inr_desc _ _ _
    apply (IsPushout.of_hasPushout (joinInl K₀ B) i).hom_ext
    · calc
        pushout.inl (joinInl K₀ B) i ≫
            (joinUnderPushoutDesc i a ≫ (joinUnderPushoutObjObj i a).ι) =
          (joinUnderPushoutObjObj i a).inr ≫
            (joinUnderPushoutObjObj i a).ι := by
              rw [← Category.assoc, hinlCorner]
        _ = (join.map i).app B := (joinUnderPushoutObjObj i a).inr_ι
        _ = pushout.inl (joinInl K₀ B) i ≫ joinUnderRestrictionAlphaMap i B :=
          hinlAlpha.symm
    · calc
        pushout.inr (joinInl K₀ B) i ≫
            (joinUnderPushoutDesc i a ≫ (joinUnderPushoutObjObj i a).ι) =
          (joinInl K A ≫ (joinUnderPushoutObjObj i a).inl) ≫
            (joinUnderPushoutObjObj i a).ι := by
              rw [← Category.assoc, hinrCorner]
        _ = joinInl K B := by
          rw [Category.assoc, (joinUnderPushoutObjObj i a).inl_ι,
            joinInl_comp_map]
        _ = pushout.inr (joinInl K₀ B) i ≫ joinUnderRestrictionAlphaMap i B :=
          hinrAlpha.symm

end SSet

namespace SSet

/-- The conjugate right mate of `joinUnderRestrictionNatTrans`. -/
noncomputable def joinUnderMateBeta {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    joinLeftDivision K ⟶ Under.map i ⋙ joinLeftDivision K₀ :=
  conjugateEquiv (joinUnderAdjunction K)
    (joinUnderRestrictionAdjunction i)
    (joinUnderRestrictionNatTrans i)

lemma joinUnderMateBeta_eq_restriction {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) :
    joinUnderMateBeta i = sliceUnder.restrictionNatTrans i :=
  joinUnderRestrictionNatTrans_is_mate i

/-- The under-slice restriction comparison associated to a morphism in `Under K`. -/
noncomputable def sliceUnder.restrictionComparisonOfHom
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    (joinLeftDivision K).obj P ⟶
      pullback
        ((joinLeftDivision K₀).map ((Under.map i).map p))
        ((joinUnderMateBeta i).app Q) :=
  pullback.lift ((joinUnderMateBeta i).app P)
    ((joinLeftDivision K).map p)
    ((joinUnderMateBeta i).naturality p).symm

@[reassoc (attr := simp)]
lemma sliceUnder.restrictionComparisonOfHom_fst
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    sliceUnder.restrictionComparisonOfHom i p ≫
        pullback.fst
          ((joinLeftDivision K₀).map ((Under.map i).map p))
          ((joinUnderMateBeta i).app Q) =
      (joinUnderMateBeta i).app P :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceUnder.restrictionComparisonOfHom_snd
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    sliceUnder.restrictionComparisonOfHom i p ≫
        pullback.snd
          ((joinLeftDivision K₀).map ((Under.map i).map p))
          ((joinUnderMateBeta i).app Q) =
      (joinLeftDivision K).map p :=
  pullback.lift_snd _ _ _

/-- The pullback-corner packet presenting the under-slice restriction comparison. -/
noncomputable def sliceUnder.restrictionPullbackObjObjOfHom
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    (walkingParallelPairOp.leftOp ⋙
      parallelPair (joinUnderMateBeta i) (joinUnderMateBeta i)).PullbackObjObj
        WalkingParallelPairHom.left p where
  pt := pullback
    ((joinLeftDivision K₀).map ((Under.map i).map p))
    ((joinUnderMateBeta i).app Q)
  fst := pullback.fst _ _
  snd := pullback.snd _ _
  isPullback := IsPullback.of_hasPullback _ _
  π := sliceUnder.restrictionComparisonOfHom i p
  π_fst := pullback.lift_fst _ _ _
  π_snd := pullback.lift_snd _ _ _

/-- The square equivalence between a structured pushout join and an under-slice comparison. -/
noncomputable def sliceUnder.restrictionArrowHomEquivOfHom
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    {P Q : Under K} (p : P ⟶ Q) :
    (Arrow.mk (joinUnderPushoutMap i a) ⟶ Arrow.mk p) ≃
      (Arrow.mk a ⟶ Arrow.mk (sliceUnder.restrictionComparisonOfHom i p)) :=
  Adjunction.leibnizMateArrowHomEquivOf
    (joinUnderRestrictionAdjunction i) (joinUnderAdjunction K)
    (joinUnderRestrictionNatTrans i) a p
    (joinUnderMatePushoutObjObj i a)
    (sliceUnder.restrictionPullbackObjObjOfHom i p)

/-- The equivalence of diagonal fillers for the under-oriented restriction square. -/
noncomputable def sliceUnder.restrictionLiftStructEquivOfHom
    {K₀ K A B : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {P Q : Under K} {p : P ⟶ Q}
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (sliceUnder.restrictionArrowHomEquivOfHom i a p sq) :=
  Adjunction.leibnizMateLiftStructEquivOf
    (joinUnderRestrictionAdjunction i) (joinUnderAdjunction K)
    (joinUnderRestrictionNatTrans i)
    (joinUnderMatePushoutObjObj i a)
    (sliceUnder.restrictionPullbackObjObjOfHom i p) sq

theorem sliceUnder.hasLiftingProperty_restrictionComparisonOfHom_iff
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    {P Q : Under K} (p : P ⟶ Q) :
    HasLiftingProperty (joinUnderPushoutMap i a) p ↔
      HasLiftingProperty a (sliceUnder.restrictionComparisonOfHom i p) :=
  Adjunction.leibnizMate_hasLiftingProperty_iff_of
    (joinUnderRestrictionAdjunction i) (joinUnderAdjunction K)
    (joinUnderRestrictionNatTrans i)
    (joinUnderMatePushoutObjObj i a)
    (sliceUnder.restrictionPullbackObjObjOfHom i p)

end SSet

namespace SSet

namespace sliceOver

/-- Restriction of over-slices along a map of fixed right join factors. -/
def restrictionNatTrans {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    joinRightDivision K ⟶ Under.map i ⋙ joinRightDivision K₀ where
  app P := restrict P.right P.hom i
  naturality P Q q := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    apply Subtype.ext
    change (join.obj (stdSimplex.obj n.unop)).map i ≫ (g.1 ≫ q.right) =
      ((join.obj (stdSimplex.obj n.unop)).map i ≫ g.1) ≫ q.right
    rw [Category.assoc]

end sliceOver

/-- Join on the right by `K₀`, followed by pushout of the structured source along `K₀ ⟶ K`. -/
noncomputable def joinOverRestrictionLeft {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    SSet.{u} ⥤ Under K := joinOver K₀ ⋙ Under.pushout i

/-- The composite adjunction for pushed-out structured right joins. -/
noncomputable def joinOverRestrictionAdjunction {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) :
    joinOverRestrictionLeft i ⊣ Under.map i ⋙ joinRightDivision K₀ :=
  (joinOverAdjunction K₀).comp (Under.mapPushoutAdj i)

/-- The underlying component of the natural map from pushed-out right joins to right join by `K`. -/
noncomputable def joinOverRestrictionAlphaMap {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) (A : SSet.{u}) :
    pushout (joinInr A K₀) i ⟶ A ⋆ K :=
  pushout.desc ((join.obj A).map i) (joinInr A K)
    ((map_comp_joinInr i A).symm)

/-- The underlying map between pushed-out structured right joins induced by a simplicial map. -/
noncomputable def joinOverRestrictionBaseMap
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    pushout (joinInr A K₀) i ⟶ pushout (joinInr B K₀) i :=
  pushout.desc
    ((join.map a).app K₀ ≫ pushout.inl (joinInr B K₀) i)
    (pushout.inr (joinInr B K₀) i) (by
      rw [← Category.assoc, joinInr_comp_map, pushout.condition])

/-- The natural map from pushed-out right joins to right join by the target. -/
noncomputable def joinOverRestrictionNatTrans {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) : joinOverRestrictionLeft i ⟶ joinOver K where
  app A := Under.homMk (joinOverRestrictionAlphaMap i A)
    (by
      change pushout.inr (joinInr A K₀) i ≫
        joinOverRestrictionAlphaMap i A = joinInr A K
      exact pushout.inr_desc _ _ _)
  naturality A B a := by
    apply StructuredArrow.hom_ext
    change joinOverRestrictionBaseMap i a ≫ joinOverRestrictionAlphaMap i B =
      joinOverRestrictionAlphaMap i A ≫ (join.map a).app K
    have hbaseInl : pushout.inl (joinInr A K₀) i ≫
        joinOverRestrictionBaseMap i a =
      (join.map a).app K₀ ≫ pushout.inl (joinInr B K₀) i :=
      pushout.inl_desc _ _ _
    have hbaseInr : pushout.inr (joinInr A K₀) i ≫
        joinOverRestrictionBaseMap i a = pushout.inr (joinInr B K₀) i :=
      pushout.inr_desc _ _ _
    have halphaAInl : pushout.inl (joinInr A K₀) i ≫
        joinOverRestrictionAlphaMap i A = (join.obj A).map i :=
      pushout.inl_desc _ _ _
    have halphaAInr : pushout.inr (joinInr A K₀) i ≫
        joinOverRestrictionAlphaMap i A = joinInr A K :=
      pushout.inr_desc _ _ _
    have halphaBInl : pushout.inl (joinInr B K₀) i ≫
        joinOverRestrictionAlphaMap i B = (join.obj B).map i :=
      pushout.inl_desc _ _ _
    have halphaBInr : pushout.inr (joinInr B K₀) i ≫
        joinOverRestrictionAlphaMap i B = joinInr B K :=
      pushout.inr_desc _ _ _
    apply (IsPushout.of_hasPushout (joinInr A K₀) i).hom_ext
    · rw [← Category.assoc, hbaseInl, Category.assoc, halphaBInl,
        ← (join.map a).naturality i, ← Category.assoc, halphaAInl]
    · rw [← Category.assoc, hbaseInr, halphaBInr,
        ← Category.assoc, halphaAInr, joinInr_comp_map]

private lemma joinOverRestrictionNatTrans_app_right
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) (A : SSet.{u}) :
    ((joinOverRestrictionNatTrans i).app A).right =
      joinOverRestrictionAlphaMap i A :=
  rfl

@[simp] private lemma joinRightDivision_obj (K : SSet.{u})
    (P : Under K) :
    (joinRightDivision K).obj P = sliceOver P.right P.hom :=
  rfl

private lemma joinOverAdjunction_counit_app_right
    (K : SSet.{u}) (P : Under K) :
    ((joinOverAdjunction K).counit.app P).right =
      sliceOver.evaluation P.right P.hom := by
  change ((joinOverHomEquiv K (sliceOver P.right P.hom) P).symm
    (𝟙 (sliceOver P.right P.hom))).right = _
  rw [joinOverHomEquiv_symm_right, sliceOver.homEquiv_apply]
  simp
  all_goals rfl

private lemma joinOverRestrictionNatTrans_comp_counit_right
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) (P : Under K) :
    (((joinOverRestrictionNatTrans i).app
        ((joinRightDivision K).obj P) ≫
      (joinOverAdjunction K).counit.app P).right) =
      joinOverRestrictionAlphaMap i (sliceOver P.right P.hom) ≫
        sliceOver.evaluation P.right P.hom := by
  rw [Under.comp_right, joinOverRestrictionNatTrans_app_right,
    joinOverAdjunction_counit_app_right]
  rfl

private lemma sliceOver_restrict_eq_homEquiv_symm_evaluation
    {K₀ K X : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) :
    sliceOver.restrict X f i =
      (sliceOver.homEquiv X (i ≫ f) (sliceOver X f)).symm
        ⟨(join.obj (sliceOver X f)).map i ≫ sliceOver.evaluation X f, by
          rw [← Category.assoc, ← map_comp_joinInr, Category.assoc,
            sliceOver.joinInr_evaluation]⟩ := by
  rw [sliceOver.homEquiv_symm_apply]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  apply Subtype.ext
  change (join.obj (stdSimplex.obj n.unop)).map i ≫ g.1 =
    (join.map (yonedaEquiv.symm g)).app K₀ ≫
      ((join.obj (sliceOver X f)).map i ≫ sliceOver.evaluation X f)
  calc
    (join.obj (stdSimplex.obj n.unop)).map i ≫ g.1 =
        (join.obj (stdSimplex.obj n.unop)).map i ≫
          ((join.map (yonedaEquiv.symm g)).app K ≫
            sliceOver.evaluation X f) := by
              rw [sliceOver.evaluation_wholeMap]
    _ = ((join.obj (stdSimplex.obj n.unop)).map i ≫
          (join.map (yonedaEquiv.symm g)).app K) ≫
            sliceOver.evaluation X f := (Category.assoc _ _ _).symm
    _ = ((join.map (yonedaEquiv.symm g)).app K₀ ≫
          (join.obj (sliceOver X f)).map i) ≫
            sliceOver.evaluation X f := by
              rw [(join.map (yonedaEquiv.symm g)).naturality i]
    _ = (join.map (yonedaEquiv.symm g)).app K₀ ≫
          ((join.obj (sliceOver X f)).map i ≫
            sliceOver.evaluation X f) := Category.assoc _ _ _

lemma joinOverRestrictionNatTrans_is_mate {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) :
    conjugateEquiv (joinOverAdjunction K)
        (joinOverRestrictionAdjunction i)
        (joinOverRestrictionNatTrans i) =
      sliceOver.restrictionNatTrans i := by
  apply NatTrans.ext
  funext P
  have h := Adjunction.homEquiv_comp_conjugateEquiv
    (joinOverRestrictionAdjunction i) (joinOverAdjunction K)
    (joinOverRestrictionNatTrans i)
    ((joinOverAdjunction K).counit.app P)
  have hc :
      ((joinOverAdjunction K).homEquiv
        ((joinRightDivision K).obj P) P)
          ((joinOverAdjunction K).counit.app P) =
        𝟙 ((joinRightDivision K).obj P) := by
    apply ((joinOverAdjunction K).homEquiv
      ((joinRightDivision K).obj P) P).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
      (joinOver K).map_id, Category.id_comp]
  have h' :
      ((joinOverRestrictionAdjunction i).homEquiv
        ((joinRightDivision K).obj P) P)
          ((joinOverRestrictionNatTrans i).app
              ((joinRightDivision K).obj P) ≫
            (joinOverAdjunction K).counit.app P) =
        (conjugateEquiv (joinOverAdjunction K)
          (joinOverRestrictionAdjunction i)
          (joinOverRestrictionNatTrans i)).app P := by
    simpa only [Functor.id_obj, hc, Category.id_comp] using h
  rw [← h']
  rw [show (joinOverRestrictionAdjunction i).homEquiv = _ from
    Adjunction.comp_homEquiv (joinOverAdjunction K₀)
      (Under.mapPushoutAdj i)]
  change
    (joinOverAdjunction K₀).homEquiv
        ((joinRightDivision K).obj P) ((Under.map i).obj P)
        ((Under.mapPushoutAdj i).homEquiv
          ((joinOver K₀).obj ((joinRightDivision K).obj P)) P
          ((joinOverRestrictionNatTrans i).app
              ((joinRightDivision K).obj P) ≫
            (joinOverAdjunction K).counit.app P)) =
      (sliceOver.restrictionNatTrans i).app P
  simp only [joinRightDivision_obj,
    sliceOver.restrictionNatTrans]
  simp only [joinOverAdjunction, Under.map_obj_right, Under.map_obj_hom]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change joinOverHomEquiv K₀ (sliceOver P.right P.hom)
      ((Under.map i).obj P) _ = _
  rw [sliceOver_restrict_eq_homEquiv_symm_evaluation]
  rw [joinOverHomEquiv_apply]
  simp only [Under.map_obj_right, Under.map_obj_hom]
  congr 1
  apply Subtype.ext
  simp only [Under.mapPushoutAdj]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change pushout.inl (joinInr (sliceOver P.right P.hom) K₀) i ≫
      (((joinOverRestrictionNatTrans i).app
          (sliceOver P.right P.hom) ≫
        (joinOverAdjunction K).counit.app P).right) = _
  change pushout.inl (joinInr (sliceOver P.right P.hom) K₀) i ≫
      (((joinOverRestrictionNatTrans i).app
          ((joinRightDivision K).obj P) ≫
        (joinOverAdjunction K).counit.app P).right) = _
  rw [joinOverRestrictionNatTrans_comp_counit_right]
  rw [← Category.assoc]
  rw [show pushout.inl (joinInr (sliceOver P.right P.hom) K₀) i ≫
      joinOverRestrictionAlphaMap i (sliceOver P.right P.hom) =
        (join.obj (sliceOver P.right P.hom)).map i from
      pushout.inl_desc _ _ _]

/-- The raw pushout join of `a` and `i`, with the varying factor on the left. -/
noncomputable def joinOverPushoutObjObj
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    join.PushoutObjObj a i :=
  Functor.PushoutObjObj.ofHasPushout join a i

lemma joinOverRestrictionAlphaMap_eq {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) (A : SSet.{u}) :
    ((joinOverRestrictionNatTrans i).app A).right =
      joinOverRestrictionAlphaMap i A :=
  rfl

lemma joinOverRestrictionBaseMap_eq
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    ((joinOverRestrictionLeft i).map a).right =
      joinOverRestrictionBaseMap i a :=
  rfl

/-- The second coprojection into the structured right pushout-join source. -/
noncomputable def joinOverPushoutDesc
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    pushout (joinInr B K₀) i ⟶ (joinOverPushoutObjObj i a).pt :=
  pushout.desc (joinOverPushoutObjObj i a).inl
    (joinInr A K ≫ (joinOverPushoutObjObj i a).inr) (by
      calc
        joinInr B K₀ ≫ (joinOverPushoutObjObj i a).inl =
            (joinInr A K₀ ≫ (join.map a).app K₀) ≫
              (joinOverPushoutObjObj i a).inl := by rw [joinInr_comp_map]
        _ = joinInr A K₀ ≫ ((join.map a).app K₀ ≫
              (joinOverPushoutObjObj i a).inl) := Category.assoc _ _ _
        _ = joinInr A K₀ ≫ ((join.obj A).map i ≫
              (joinOverPushoutObjObj i a).inr) := by
                rw [(joinOverPushoutObjObj i a).isPushout.w]
        _ = (joinInr A K₀ ≫ (join.obj A).map i) ≫
              (joinOverPushoutObjObj i a).inr := (Category.assoc _ _ _).symm
        _ = (i ≫ joinInr A K) ≫ (joinOverPushoutObjObj i a).inr := by
              rw [map_comp_joinInr]
        _ = i ≫ (joinInr A K ≫ (joinOverPushoutObjObj i a).inr) :=
              Category.assoc _ _ _)

/-- The source object in `Under K` of the structured right pushout join. -/
noncomputable def joinOverPushoutSource
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) : Under K :=
  Under.mk (joinInr A K ≫ (joinOverPushoutObjObj i a).inr)

/-- The coprojection from `A ⋆ K` into the structured right pushout-join source. -/
noncomputable def joinOverPushoutInl
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinOver K).obj A ⟶ joinOverPushoutSource i a :=
  Under.homMk (joinOverPushoutObjObj i a).inr rfl

/-- The coprojection from the pushed-out `B ⋆ K₀` into the structured right pushout-join source. -/
noncomputable def joinOverPushoutInr
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinOverRestrictionLeft i).obj B ⟶ joinOverPushoutSource i a :=
  Under.homMk (joinOverPushoutDesc i a) (by
    exact pushout.inr_desc _ _ _)

/-- The structured right pushout join; its right field is the raw pushout join. -/
noncomputable def joinOverPushoutMap
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    joinOverPushoutSource i a ⟶ (joinOver K).obj B :=
  Under.homMk (joinOverPushoutObjObj i a).ι (by
    change (joinInr A K ≫ (joinOverPushoutObjObj i a).inr) ≫
      (joinOverPushoutObjObj i a).ι = joinInr B K
    rw [Category.assoc, (joinOverPushoutObjObj i a).inr_ι,
      joinInr_comp_map])

@[simp]
lemma joinOverPushoutMap_right
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (joinOverPushoutMap i a).right = (joinOverPushoutObjObj i a).ι := rfl

lemma joinOverRestrictionBaseSquare
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    IsPushout ((join.map a).app K₀)
      (pushout.inl (joinInr A K₀) i)
      (pushout.inl (joinInr B K₀) i)
      (joinOverRestrictionBaseMap i a) := by
  let hA := IsPushout.of_hasPushout (joinInr A K₀) i
  let hB := IsPushout.of_hasPushout (joinInr B K₀) i
  have hcomp : joinInr A K₀ ≫ (join.map a).app K₀ = joinInr B K₀ :=
    joinInr_comp_map a K₀
  have hinr : pushout.inr (joinInr A K₀) i ≫
      joinOverRestrictionBaseMap i a = pushout.inr (joinInr B K₀) i :=
    pushout.inr_desc _ _ _
  have houter : IsPushout
      (joinInr A K₀ ≫ (join.map a).app K₀) i
      (pushout.inl (joinInr B K₀) i)
      (pushout.inr (joinInr A K₀) i ≫ joinOverRestrictionBaseMap i a) :=
    hB.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      hcomp.symm (by simp) (by simp) hinr.symm
  exact houter.of_left (pushout.inl_desc _ _ _).symm hA

lemma joinOverPushoutSquareUnderlying
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    IsPushout (joinOverRestrictionAlphaMap i A) (joinOverRestrictionBaseMap i a)
      (joinOverPushoutObjObj i a).inr (joinOverPushoutDesc i a) := by
  have hleft := (joinOverRestrictionBaseSquare i a).flip
  have htop : pushout.inl (joinInr A K₀) i ≫ joinOverRestrictionAlphaMap i A =
      (join.obj A).map i := pushout.inl_desc _ _ _
  have hbot : pushout.inl (joinInr B K₀) i ≫ joinOverPushoutDesc i a =
      (joinOverPushoutObjObj i a).inl := pushout.inl_desc _ _ _
  have houter : IsPushout
      (pushout.inl (joinInr A K₀) i ≫ joinOverRestrictionAlphaMap i A)
      ((join.map a).app K₀)
      (joinOverPushoutObjObj i a).inr
      (pushout.inl (joinInr B K₀) i ≫ joinOverPushoutDesc i a) :=
    (joinOverPushoutObjObj i a).isPushout.flip.of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      htop.symm (by simp) (by simp) hbot.symm
  have hinlAlpha : pushout.inl (joinInr A K₀) i ≫
      joinOverRestrictionAlphaMap i A = (join.obj A).map i :=
    pushout.inl_desc _ _ _
  have hinrAlpha : pushout.inr (joinInr A K₀) i ≫
      joinOverRestrictionAlphaMap i A = joinInr A K :=
    pushout.inr_desc _ _ _
  have hinlBase : pushout.inl (joinInr A K₀) i ≫
      joinOverRestrictionBaseMap i a =
        (join.map a).app K₀ ≫ pushout.inl (joinInr B K₀) i :=
    pushout.inl_desc _ _ _
  have hinrBase : pushout.inr (joinInr A K₀) i ≫
      joinOverRestrictionBaseMap i a = pushout.inr (joinInr B K₀) i :=
    pushout.inr_desc _ _ _
  have hinlCorner : pushout.inl (joinInr B K₀) i ≫
      joinOverPushoutDesc i a = (joinOverPushoutObjObj i a).inl :=
    pushout.inl_desc _ _ _
  have hinrCorner : pushout.inr (joinInr B K₀) i ≫
      joinOverPushoutDesc i a =
        joinInr A K ≫ (joinOverPushoutObjObj i a).inr :=
    pushout.inr_desc _ _ _
  apply houter.of_left
  · apply (IsPushout.of_hasPushout (joinInr A K₀) i).hom_ext
    · calc
        pushout.inl (joinInr A K₀) i ≫
            (joinOverRestrictionAlphaMap i A ≫ (joinOverPushoutObjObj i a).inr) =
          (join.obj A).map i ≫ (joinOverPushoutObjObj i a).inr := by
            rw [← Category.assoc, hinlAlpha]
        _ = (join.map a).app K₀ ≫ (joinOverPushoutObjObj i a).inl :=
          (joinOverPushoutObjObj i a).isPushout.w.symm
        _ = pushout.inl (joinInr A K₀) i ≫
            (joinOverRestrictionBaseMap i a ≫ joinOverPushoutDesc i a) := by
          rw [← Category.assoc, hinlBase, Category.assoc, hinlCorner]
    · calc
        pushout.inr (joinInr A K₀) i ≫
            (joinOverRestrictionAlphaMap i A ≫ (joinOverPushoutObjObj i a).inr) =
          joinInr A K ≫ (joinOverPushoutObjObj i a).inr := by
            rw [← Category.assoc, hinrAlpha]
        _ = pushout.inr (joinInr A K₀) i ≫
            (joinOverRestrictionBaseMap i a ≫ joinOverPushoutDesc i a) := by
          rw [← Category.assoc, hinrBase]
          exact hinrCorner.symm
  · exact hleft

lemma joinOverPushoutSquare
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    IsPushout ((joinOverRestrictionNatTrans i).app A)
      ((joinOverRestrictionLeft i).map a)
      (joinOverPushoutInl i a) (joinOverPushoutInr i a) := by
  apply IsPushout.of_map (Under.forget K)
  · apply StructuredArrow.hom_ext
    change ((joinOverRestrictionNatTrans i).app A).right ≫
        (joinOverPushoutInl i a).right =
      ((joinOverRestrictionLeft i).map a).right ≫
        (joinOverPushoutInr i a).right
    rw [joinOverRestrictionAlphaMap_eq, joinOverRestrictionBaseMap_eq]
    exact (joinOverPushoutSquareUnderlying i a).w
  · change IsPushout ((joinOverRestrictionNatTrans i).app A).right
      ((joinOverRestrictionLeft i).map a).right
      (joinOverPushoutInl i a).right (joinOverPushoutInr i a).right
    rw [joinOverRestrictionAlphaMap_eq, joinOverRestrictionBaseMap_eq]
    exact joinOverPushoutSquareUnderlying i a

/-- The pushout-corner packet presenting `joinOverPushoutMap` for the mate theorem. -/
noncomputable def joinOverMatePushoutObjObj
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B) :
    (parallelPair (joinOverRestrictionNatTrans i)
      (joinOverRestrictionNatTrans i)).PushoutObjObj
        WalkingParallelPairHom.left a where
  pt := joinOverPushoutSource i a
  inl := joinOverPushoutInl i a
  inr := joinOverPushoutInr i a
  isPushout := joinOverPushoutSquare i a
  ι := joinOverPushoutMap i a
  inl_ι := by
    apply StructuredArrow.hom_ext
    exact (joinOverPushoutObjObj i a).inr_ι
  inr_ι := by
    apply StructuredArrow.hom_ext
    have hinlCorner : pushout.inl (joinInr B K₀) i ≫
        joinOverPushoutDesc i a = (joinOverPushoutObjObj i a).inl :=
      pushout.inl_desc _ _ _
    have hinrCorner : pushout.inr (joinInr B K₀) i ≫
        joinOverPushoutDesc i a =
          joinInr A K ≫ (joinOverPushoutObjObj i a).inr :=
      pushout.inr_desc _ _ _
    have hinlAlpha : pushout.inl (joinInr B K₀) i ≫
        joinOverRestrictionAlphaMap i B = (join.obj B).map i :=
      pushout.inl_desc _ _ _
    have hinrAlpha : pushout.inr (joinInr B K₀) i ≫
        joinOverRestrictionAlphaMap i B = joinInr B K :=
      pushout.inr_desc _ _ _
    apply (IsPushout.of_hasPushout (joinInr B K₀) i).hom_ext
    · calc
        pushout.inl (joinInr B K₀) i ≫
            (joinOverPushoutDesc i a ≫ (joinOverPushoutObjObj i a).ι) =
          (joinOverPushoutObjObj i a).inl ≫
            (joinOverPushoutObjObj i a).ι := by
              rw [← Category.assoc, hinlCorner]
        _ = (join.obj B).map i := (joinOverPushoutObjObj i a).inl_ι
        _ = pushout.inl (joinInr B K₀) i ≫ joinOverRestrictionAlphaMap i B :=
          hinlAlpha.symm
    · calc
        pushout.inr (joinInr B K₀) i ≫
            (joinOverPushoutDesc i a ≫ (joinOverPushoutObjObj i a).ι) =
          (joinInr A K ≫ (joinOverPushoutObjObj i a).inr) ≫
            (joinOverPushoutObjObj i a).ι := by
              rw [← Category.assoc, hinrCorner]
        _ = joinInr B K := by
          rw [Category.assoc, (joinOverPushoutObjObj i a).inr_ι,
            joinInr_comp_map]
        _ = pushout.inr (joinInr B K₀) i ≫ joinOverRestrictionAlphaMap i B :=
          hinrAlpha.symm


/-- The conjugate right mate of `joinOverRestrictionNatTrans`. -/
noncomputable def joinOverMateBeta {K₀ K : SSet.{u}} (i : K₀ ⟶ K) :
    joinRightDivision K ⟶ Under.map i ⋙ joinRightDivision K₀ :=
  conjugateEquiv (joinOverAdjunction K)
    (joinOverRestrictionAdjunction i)
    (joinOverRestrictionNatTrans i)

lemma joinOverMateBeta_eq_restriction {K₀ K : SSet.{u}}
    (i : K₀ ⟶ K) :
    joinOverMateBeta i = sliceOver.restrictionNatTrans i :=
  joinOverRestrictionNatTrans_is_mate i

/-- The over-slice restriction comparison associated to a morphism in `Under K`. -/
noncomputable def sliceOver.restrictionComparisonOfHom
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    (joinRightDivision K).obj P ⟶
      pullback
        ((joinRightDivision K₀).map ((Under.map i).map p))
        ((joinOverMateBeta i).app Q) :=
  pullback.lift ((joinOverMateBeta i).app P)
    ((joinRightDivision K).map p)
    ((joinOverMateBeta i).naturality p).symm

@[reassoc (attr := simp)]
lemma sliceOver.restrictionComparisonOfHom_fst
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    sliceOver.restrictionComparisonOfHom i p ≫
        pullback.fst
          ((joinRightDivision K₀).map ((Under.map i).map p))
          ((joinOverMateBeta i).app Q) =
      (joinOverMateBeta i).app P :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sliceOver.restrictionComparisonOfHom_snd
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    sliceOver.restrictionComparisonOfHom i p ≫
        pullback.snd
          ((joinRightDivision K₀).map ((Under.map i).map p))
          ((joinOverMateBeta i).app Q) =
      (joinRightDivision K).map p :=
  pullback.lift_snd _ _ _

/-- The pullback-corner packet presenting the over-slice restriction comparison. -/
noncomputable def sliceOver.restrictionPullbackObjObjOfHom
    {K₀ K : SSet.{u}} (i : K₀ ⟶ K) {P Q : Under K} (p : P ⟶ Q) :
    (walkingParallelPairOp.leftOp ⋙
      parallelPair (joinOverMateBeta i) (joinOverMateBeta i)).PullbackObjObj
        WalkingParallelPairHom.left p where
  pt := pullback
    ((joinRightDivision K₀).map ((Under.map i).map p))
    ((joinOverMateBeta i).app Q)
  fst := pullback.fst _ _
  snd := pullback.snd _ _
  isPullback := IsPullback.of_hasPullback _ _
  π := sliceOver.restrictionComparisonOfHom i p
  π_fst := pullback.lift_fst _ _ _
  π_snd := pullback.lift_snd _ _ _

/-- The square equivalence between a structured pushout join and an over-slice comparison. -/
noncomputable def sliceOver.restrictionArrowHomEquivOfHom
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    {P Q : Under K} (p : P ⟶ Q) :
    (Arrow.mk (joinOverPushoutMap i a) ⟶ Arrow.mk p) ≃
      (Arrow.mk a ⟶ Arrow.mk (sliceOver.restrictionComparisonOfHom i p)) :=
  Adjunction.leibnizMateArrowHomEquivOf
    (joinOverRestrictionAdjunction i) (joinOverAdjunction K)
    (joinOverRestrictionNatTrans i) a p
    (joinOverMatePushoutObjObj i a)
    (sliceOver.restrictionPullbackObjObjOfHom i p)

/-- The equivalence of diagonal fillers for the over-oriented restriction square. -/
noncomputable def sliceOver.restrictionLiftStructEquivOfHom
    {K₀ K A B : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {P Q : Under K} {p : P ⟶ Q}
    (sq : Arrow.mk (joinOverPushoutMap i a) ⟶ Arrow.mk p) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct (sliceOver.restrictionArrowHomEquivOfHom i a p sq) :=
  Adjunction.leibnizMateLiftStructEquivOf
    (joinOverRestrictionAdjunction i) (joinOverAdjunction K)
    (joinOverRestrictionNatTrans i)
    (joinOverMatePushoutObjObj i a)
    (sliceOver.restrictionPullbackObjObjOfHom i p) sq

theorem sliceOver.hasLiftingProperty_restrictionComparisonOfHom_iff
    {K₀ K A B : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    {P Q : Under K} (p : P ⟶ Q) :
    HasLiftingProperty (joinOverPushoutMap i a) p ↔
      HasLiftingProperty a (sliceOver.restrictionComparisonOfHom i p) :=
  Adjunction.leibnizMate_hasLiftingProperty_iff_of
    (joinOverRestrictionAdjunction i) (joinOverAdjunction K)
    (joinOverRestrictionNatTrans i)
    (joinOverMatePushoutObjObj i a)
    (sliceOver.restrictionPullbackObjObjOfHom i p)


namespace sliceUnder

/-- The concrete under-slice restriction comparison attached to
`K₀ ⟶ K ⟶ X ⟶ S`, using Mathlib's pullback factor order. -/
noncomputable def restrictionComparison {K₀ K X S : SSet.{u}}
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    sliceUnder X f ⟶
      pullback (map X (i ≫ f) q) (restrict S (f ≫ q) i) :=
  pullback.lift (restrict X f i) (map X f q) (restrict_map X f i q)

@[reassoc (attr := simp)]
lemma restrictionComparison_fst {K₀ K X S : SSet.{u}}
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    restrictionComparison i f q ≫
        pullback.fst (map X (i ≫ f) q) (restrict S (f ≫ q) i) =
      restrict X f i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma restrictionComparison_snd {K₀ K X S : SSet.{u}}
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    restrictionComparison i f q ≫
        pullback.snd (map X (i ≫ f) q) (restrict S (f ≫ q) i) =
      map X f q :=
  pullback.lift_snd _ _ _

end sliceUnder

namespace sliceOver

/-- The concrete over-slice restriction comparison attached to
`K₀ ⟶ K ⟶ X ⟶ S`, using Mathlib's pullback factor order. -/
noncomputable def restrictionComparison {K₀ K X S : SSet.{u}}
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    sliceOver X f ⟶
      pullback (map X (i ≫ f) q) (restrict S (f ≫ q) i) :=
  pullback.lift (restrict X f i) (map X f q) (restrict_map X f i q)

@[reassoc (attr := simp)]
lemma restrictionComparison_fst {K₀ K X S : SSet.{u}}
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    restrictionComparison i f q ≫
        pullback.fst (map X (i ≫ f) q) (restrict S (f ≫ q) i) =
      restrict X f i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma restrictionComparison_snd {K₀ K X S : SSet.{u}}
    (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    restrictionComparison i f q ≫
        pullback.snd (map X (i ≫ f) q) (restrict S (f ≫ q) i) =
      map X f q :=
  pullback.lift_snd _ _ _

end sliceOver



private lemma pullbackCongrHom_hom_fst_eq
    {C : Type*} [Category C] {X Y Z : C}
    {f : X ⟶ Z} {g g' : Y ⟶ Z} (h : g = g')
    [HasPullback f g] [HasPullback f g'] :
    (pullback.congrHom rfl h).hom ≫ pullback.fst f g' =
      pullback.fst f g := by
  subst g'
  simp

private lemma pullbackCongrHom_hom_snd_eq
    {C : Type*} [Category C] {X Y Z : C}
    {f : X ⟶ Z} {g g' : Y ⟶ Z} (h : g = g')
    [HasPullback f g] [HasPullback f g'] :
    (pullback.congrHom rfl h).hom ≫ pullback.snd f g' =
      pullback.snd f g := by
  subst g'
  simp

private lemma pullbackLift_comp_congrHom_of_eq
    {C : Type*} [Category C] {X Y Z W : C}
    {f : X ⟶ Z} {g g' : Y ⟶ Z} (hg : g = g')
    {a a' : W ⟶ X} (ha : a = a') {b b' : W ⟶ Y} (hb : b = b')
    [HasPullback f g] [HasPullback f g']
    (w : a ≫ f = b ≫ g) (w' : a' ≫ f = b' ≫ g') :
    pullback.lift a b w ≫ (pullback.congrHom rfl hg).hom =
      pullback.lift a' b' w' := by
  subst g'
  subst a'
  subst b'
  simp


@[simp]
lemma sliceUnder.restrictionDivisionMap_eq_map
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    (joinLeftDivision K₀).map ((Under.map i).map
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) =
      sliceUnder.map X (i ≫ f) q := by
  rfl

@[simp]
lemma sliceOver.restrictionDivisionMap_eq_map
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    (joinRightDivision K₀).map ((Under.map i).map
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) =
      sliceOver.map X (i ≫ f) q := by
  rfl

@[simp]
lemma sliceUnder.divisionMap_eq_map
    {K X S : SSet.{u}} (f : K ⟶ X) (q : X ⟶ S) :
    (joinLeftDivision K).map
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) =
      sliceUnder.map X f q := by
  rfl

@[simp]
lemma sliceOver.divisionMap_eq_map
    {K X S : SSet.{u}} (f : K ⟶ X) (q : X ⟶ S) :
    (joinRightDivision K).map
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) =
      sliceOver.map X f q := by
  rfl

@[simp]
lemma sliceUnder.joinUnderMateBeta_app_eq_restrict
    {K₀ K X : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) :
    (joinUnderMateBeta i).app (Under.mk f) = sliceUnder.restrict X f i := by
  rw [joinUnderMateBeta_eq_restriction]
  rfl

@[simp]
lemma sliceOver.joinOverMateBeta_app_eq_restrict
    {K₀ K X : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) :
    (joinOverMateBeta i).app (Under.mk f) = sliceOver.restrict X f i := by
  rw [joinOverMateBeta_eq_restriction]
  rfl

/-- The canonical isomorphism from the mate pullback to the concrete under-slice pullback. -/
noncomputable def sliceUnder.restrictionConcretePullbackIso
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    pullback (sliceUnder.map X (i ≫ f) q)
        ((joinUnderMateBeta i).app (Under.mk (f ≫ q))) ≅
      pullback (sliceUnder.map X (i ≫ f) q)
        (sliceUnder.restrict S (f ≫ q) i) :=
  pullback.congrHom rfl (by
    rw [joinUnderMateBeta_eq_restriction]
    rfl)

/-- The canonical isomorphism from the mate pullback to the concrete over-slice pullback. -/
noncomputable def sliceOver.restrictionConcretePullbackIso
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    pullback (sliceOver.map X (i ≫ f) q)
        ((joinOverMateBeta i).app (Under.mk (f ≫ q))) ≅
      pullback (sliceOver.map X (i ≫ f) q)
        (sliceOver.restrict S (f ≫ q) i) :=
  pullback.congrHom rfl (by
    rw [joinOverMateBeta_eq_restriction]
    rfl)

@[reassoc (attr := simp)]
lemma sliceUnder.restrictionConcretePullbackIso_hom_fst
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    (sliceUnder.restrictionConcretePullbackIso i f q).hom ≫
        pullback.fst (sliceUnder.map X (i ≫ f) q)
          (sliceUnder.restrict S (f ≫ q) i) =
      pullback.fst
        ((joinLeftDivision K₀).map ((Under.map i).map
          (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))))
        ((joinUnderMateBeta i).app (Under.mk (f ≫ q))) := by
  unfold sliceUnder.restrictionConcretePullbackIso
  exact pullbackCongrHom_hom_fst_eq _


@[reassoc (attr := simp)]
lemma sliceUnder.restrictionConcretePullbackIso_hom_snd
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    (sliceUnder.restrictionConcretePullbackIso i f q).hom ≫
        pullback.snd (sliceUnder.map X (i ≫ f) q)
          (sliceUnder.restrict S (f ≫ q) i) =
      pullback.snd
        ((joinLeftDivision K₀).map ((Under.map i).map
          (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))))
        ((joinUnderMateBeta i).app (Under.mk (f ≫ q))) := by
  unfold sliceUnder.restrictionConcretePullbackIso
  exact pullbackCongrHom_hom_snd_eq _


@[reassoc (attr := simp)]
lemma sliceOver.restrictionConcretePullbackIso_hom_fst
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    (sliceOver.restrictionConcretePullbackIso i f q).hom ≫
        pullback.fst (sliceOver.map X (i ≫ f) q)
          (sliceOver.restrict S (f ≫ q) i) =
      pullback.fst
        ((joinRightDivision K₀).map ((Under.map i).map
          (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))))
        ((joinOverMateBeta i).app (Under.mk (f ≫ q))) := by
  unfold sliceOver.restrictionConcretePullbackIso
  exact pullbackCongrHom_hom_fst_eq _


@[reassoc (attr := simp)]
lemma sliceOver.restrictionConcretePullbackIso_hom_snd
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    (sliceOver.restrictionConcretePullbackIso i f q).hom ≫
        pullback.snd (sliceOver.map X (i ≫ f) q)
          (sliceOver.restrict S (f ≫ q) i) =
      pullback.snd
        ((joinRightDivision K₀).map ((Under.map i).map
          (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))))
        ((joinOverMateBeta i).app (Under.mk (f ≫ q))) := by
  unfold sliceOver.restrictionConcretePullbackIso
  exact pullbackCongrHom_hom_snd_eq _


lemma sliceUnder.restrictionComparisonOfHom_comp_concretePullbackIso_hom
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    sliceUnder.restrictionComparisonOfHom i
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) ≫
        (sliceUnder.restrictionConcretePullbackIso i f q).hom =
      sliceUnder.restrictionComparison i f q := by
  unfold sliceUnder.restrictionComparisonOfHom
  unfold sliceUnder.restrictionComparison
  unfold sliceUnder.restrictionConcretePullbackIso
  refine pullbackLift_comp_congrHom_of_eq ?_ ?_ rfl _ _
  · rw [joinUnderMateBeta_eq_restriction]
    rfl

lemma sliceOver.restrictionComparisonOfHom_comp_concretePullbackIso_hom
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    sliceOver.restrictionComparisonOfHom i
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) ≫
        (sliceOver.restrictionConcretePullbackIso i f q).hom =
      sliceOver.restrictionComparison i f q := by
  unfold sliceOver.restrictionComparisonOfHom
  unfold sliceOver.restrictionComparison
  unfold sliceOver.restrictionConcretePullbackIso
  refine pullbackLift_comp_congrHom_of_eq ?_ ?_ rfl _ _
  · rw [joinOverMateBeta_eq_restriction]
    rfl

/-- The under-slice mate comparison and concrete comparison are isomorphic as arrows. -/
noncomputable def sliceUnder.restrictionComparisonArrowIso
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    Arrow.mk (sliceUnder.restrictionComparisonOfHom i
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) ≅
      Arrow.mk (sliceUnder.restrictionComparison i f q) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    (sliceUnder.restrictionConcretePullbackIso i f q) (by
      exact (sliceUnder.restrictionComparisonOfHom_comp_concretePullbackIso_hom
        i f q).symm)

/-- The over-slice mate comparison and concrete comparison are isomorphic as arrows. -/
noncomputable def sliceOver.restrictionComparisonArrowIso
    {K₀ K X S : SSet.{u}} (i : K₀ ⟶ K) (f : K ⟶ X) (q : X ⟶ S) :
    Arrow.mk (sliceOver.restrictionComparisonOfHom i
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) ≅
      Arrow.mk (sliceOver.restrictionComparison i f q) :=
  Arrow.isoMk' _ _ (Iso.refl _)
    (sliceOver.restrictionConcretePullbackIso i f q) (by
      exact (sliceOver.restrictionComparisonOfHom_comp_concretePullbackIso_hom
        i f q).symm)

/-- The concrete under-slice square equivalence of Joyal’s Lemma 3.14. -/
noncomputable def sliceUnder.restrictionArrowHomEquiv
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    (Arrow.mk (joinUnderPushoutMap i a) ⟶
        Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) ≃
      (Arrow.mk a ⟶ Arrow.mk (sliceUnder.restrictionComparison i f q)) :=
  (sliceUnder.restrictionArrowHomEquivOfHom i a
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))).trans
    (Iso.homCongr (Iso.refl _)
      (sliceUnder.restrictionComparisonArrowIso i f q))

/-- The concrete over-slice square equivalence dual to Joyal’s Lemma 3.14. -/
noncomputable def sliceOver.restrictionArrowHomEquiv
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    (Arrow.mk (joinOverPushoutMap i a) ⟶
        Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) ≃
      (Arrow.mk a ⟶ Arrow.mk (sliceOver.restrictionComparison i f q)) :=
  (sliceOver.restrictionArrowHomEquivOfHom i a
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))).trans
    (Iso.homCongr (Iso.refl _)
      (sliceOver.restrictionComparisonArrowIso i f q))

@[simp]
lemma sliceUnder.restrictionArrowHomEquiv_apply
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S)
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) :
    sliceUnder.restrictionArrowHomEquiv i a f q sq =
      sliceUnder.restrictionArrowHomEquivOfHom i a
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) sq ≫
          (sliceUnder.restrictionComparisonArrowIso i f q).hom := by
  rfl

@[simp]
lemma sliceOver.restrictionArrowHomEquiv_apply
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S)
    (sq : Arrow.mk (joinOverPushoutMap i a) ⟶
      Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) :
    sliceOver.restrictionArrowHomEquiv i a f q sq =
      sliceOver.restrictionArrowHomEquivOfHom i a
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) sq ≫
          (sliceOver.restrictionComparisonArrowIso i f q).hom := by
  rfl

/-- The concrete under-slice equivalence of diagonal fillers. -/
noncomputable def sliceUnder.restrictionLiftStructEquiv
    {K₀ K A B X S : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {f : K ⟶ X} {q : X ⟶ S}
    (sq : Arrow.mk (joinUnderPushoutMap i a) ⟶
      Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct
        (sliceUnder.restrictionArrowHomEquiv i a f q sq) :=
  (sliceUnder.restrictionLiftStructEquivOfHom sq).trans
    (Arrow.liftStructPostcompIsoEquiv
      (sliceUnder.restrictionArrowHomEquivOfHom i a
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) sq)
      (sliceUnder.restrictionComparisonArrowIso i f q))

/-- The concrete over-slice equivalence of diagonal fillers. -/
noncomputable def sliceOver.restrictionLiftStructEquiv
    {K₀ K A B X S : SSet.{u}} {i : K₀ ⟶ K} {a : A ⟶ B}
    {f : K ⟶ X} {q : X ⟶ S}
    (sq : Arrow.mk (joinOverPushoutMap i a) ⟶
      Arrow.mk (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))) :
    Arrow.LiftStruct sq ≃
      Arrow.LiftStruct
        (sliceOver.restrictionArrowHomEquiv i a f q sq) :=
  (sliceOver.restrictionLiftStructEquivOfHom sq).trans
    (Arrow.liftStructPostcompIsoEquiv
      (sliceOver.restrictionArrowHomEquivOfHom i a
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) sq)
      (sliceOver.restrictionComparisonArrowIso i f q))

theorem sliceUnder.hasLiftingProperty_restrictionComparison_iff
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    HasLiftingProperty (joinUnderPushoutMap i a)
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) ↔
      HasLiftingProperty a (sliceUnder.restrictionComparison i f q) :=
  (sliceUnder.hasLiftingProperty_restrictionComparisonOfHom_iff i a
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))).trans
    (HasLiftingProperty.iff_of_arrow_iso_right a
      (sliceUnder.restrictionComparisonArrowIso i f q))

theorem sliceOver.hasLiftingProperty_restrictionComparison_iff
    {K₀ K A B X S : SSet.{u}} (i : K₀ ⟶ K) (a : A ⟶ B)
    (f : K ⟶ X) (q : X ⟶ S) :
    HasLiftingProperty (joinOverPushoutMap i a)
        (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q)) ↔
      HasLiftingProperty a (sliceOver.restrictionComparison i f q) :=
  (sliceOver.hasLiftingProperty_restrictionComparisonOfHom_iff i a
      (Under.homMk q rfl : Under.mk f ⟶ Under.mk (f ≫ q))).trans
    (HasLiftingProperty.iff_of_arrow_iso_right a
      (sliceOver.restrictionComparisonArrowIso i f q))

end SSet
