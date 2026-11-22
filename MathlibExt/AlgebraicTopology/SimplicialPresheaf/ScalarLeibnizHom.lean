/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarTensorHomIso
import Mathlib.CategoryTheory.Adjunction.ParametrizedLimits
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomPullback

/-!
# The whole original scalar Leibniz Hom comparison
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open scoped Simplicial MonoidalClosed

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D]

/-- The actual canonical pushout product of the two original arrows. -/
abbrev scalarPushoutObjObj {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) : scalarTensor.PushoutObjObj s j :=
  Functor.PushoutObjObj.ofHasPushout scalarTensor s j

variable [Small.{u} D] [LocallySmall.{u} D]

/-- The actual canonical scalar pullback of the original restriction map. -/
abbrev scalarLeibnizPullback {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    MonoidalClosed.internalHom.PullbackObjObj j (innerHomPre s Z) :=
  Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom j (innerHomPre s Z)

/-- Its comparison is the original native internal-Hom pullback map. -/
theorem scalarLeibnizPullback_π {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizPullback s j Z).π = SSet.ihomToPullback j (innerHomPre s Z) := rfl

private theorem mappingPreservesPullbacks (Z : SimplicialPresheaf.{u} D) :
    PreservesLimitsOfShape WalkingCospan (innerHomFunctor.flip.obj Z) := by
  let _ : ∀ K : SSet.{u}, PreservesColimitsOfShape WalkingCospanᵒᵖ
      ((scalarTensor (D := D)).flip.obj K) := fun K => by
    change PreservesColimitsOfShape WalkingCospanᵒᵖ (scalarTensorFixed (D := D) K)
    let _ : (scalarTensorFixed (D := D) K).IsLeftAdjoint :=
      (scalarTensorCotensorAdjunction K).isLeftAdjoint
    infer_instance
  exact scalarTensorHomAdjunction₂.preservesLimitsOfShape_flip_obj WalkingCospan Z

/-- The mapping end sends the canonical pushout to its genuine pullback. -/
theorem scalarMappedPushout_isPullback {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    IsPullback (innerHomPre (scalarPushoutObjObj s j).inl Z)
      (innerHomPre (scalarPushoutObjObj s j).inr Z)
      (innerHomPre ((scalarTensor.map s).app K) Z)
      (innerHomPre ((scalarTensor.obj A).map j) Z) := by
  let _ := mappingPreservesPullbacks Z
  exact ((scalarPushoutObjObj s j).isPushout.op.flip).map (innerHomFunctor.flip.obj Z)

/-- Both original pushout inclusions are transported by the constructed scalar comparison. -/
theorem scalarTransportedPullback_isPullback {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    IsPullback
      (innerHomPre (scalarPushoutObjObj s j).inl Z ≫ (scalarTensorHomIso K B).hom.app Z)
      (innerHomPre (scalarPushoutObjObj s j).inr Z ≫ (scalarTensorHomIso L A).hom.app Z)
      ((ihom K).map (innerHomPre s Z)) ((pre j).app (innerHom A Z)) := by
  exact (scalarMappedPushout_isPullback s j Z).of_iso
    (Iso.refl _) ((scalarTensorHomIso K B).app Z)
    ((scalarTensorHomIso L A).app Z) ((scalarTensorHomIso K A).app Z)
    (by simp) (by simp)
    (scalarTensorHomIso_naturality_source K s Z)
    (scalarTensorHomIso_naturality_scalar j A Z)

/-- The whole mapping end of the canonical pushout is the canonical scalar pullback. -/
def scalarLeibnizPointIso {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    innerHom (scalarPushoutObjObj s j).pt Z ≅ (scalarLeibnizPullback s j Z).pt :=
  (scalarTransportedPullback_isPullback s j Z).isoIsPullback _ _
    (scalarLeibnizPullback s j Z).isPullback

/-- The forward comparison retains the original left pushout inclusion. -/
@[reassoc]
theorem scalarLeibnizPointIso_hom_fst {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizPointIso s j Z).hom ≫ (scalarLeibnizPullback s j Z).fst =
      innerHomPre (scalarPushoutObjObj s j).inl Z ≫ (scalarTensorHomIso K B).hom.app Z :=
  IsPullback.isoIsPullback_hom_fst _ _ (scalarTransportedPullback_isPullback s j Z)
    (scalarLeibnizPullback s j Z).isPullback

/-- The forward comparison retains the original right pushout inclusion. -/
@[reassoc]
theorem scalarLeibnizPointIso_hom_snd {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizPointIso s j Z).hom ≫ (scalarLeibnizPullback s j Z).snd =
      innerHomPre (scalarPushoutObjObj s j).inr Z ≫ (scalarTensorHomIso L A).hom.app Z :=
  IsPullback.isoIsPullback_hom_snd _ _ (scalarTransportedPullback_isPullback s j Z)
    (scalarLeibnizPullback s j Z).isPullback

/-- The inverse comparison retains the same original left restriction. -/
@[reassoc]
theorem scalarLeibnizPointIso_inv_fst {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizPointIso s j Z).inv ≫ innerHomPre (scalarPushoutObjObj s j).inl Z =
      (scalarLeibnizPullback s j Z).fst ≫ (scalarTensorHomIso K B).inv.app Z := by
  apply (Iso.eq_comp_inv ((scalarTensorHomIso K B).app Z)).2
  exact (Category.assoc _ _ _).trans
    (IsPullback.isoIsPullback_inv_fst _ _ (scalarTransportedPullback_isPullback s j Z)
      (scalarLeibnizPullback s j Z).isPullback)

/-- The inverse comparison retains the same original right restriction. -/
@[reassoc]
theorem scalarLeibnizPointIso_inv_snd {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizPointIso s j Z).inv ≫ innerHomPre (scalarPushoutObjObj s j).inr Z =
      (scalarLeibnizPullback s j Z).snd ≫ (scalarTensorHomIso L A).inv.app Z := by
  apply (Iso.eq_comp_inv ((scalarTensorHomIso L A).app Z)).2
  exact (Category.assoc _ _ _).trans
    (IsPullback.isoIsPullback_inv_snd _ _ (scalarTransportedPullback_isPullback s j Z)
      (scalarLeibnizPullback s j Z).isPullback)

/-- The whole original Arrow square follows from both original pushout legs. -/
theorem scalarLeibnizHomIso_square {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarTensorHomIso L B).hom.app Z ≫ (scalarLeibnizPullback s j Z).π =
      innerHomPre (scalarPushoutObjObj s j).ι Z ≫ (scalarLeibnizPointIso s j Z).hom := by
  let bLB : innerHom ((scalarTensor.obj B).obj L) Z ≅ (ihom L).obj (innerHom B Z) :=
    (scalarTensorHomIso L B).app Z
  let bKB : innerHom ((scalarTensor.obj B).obj K) Z ≅ (ihom K).obj (innerHom B Z) :=
    (scalarTensorHomIso K B).app Z
  let bLA : innerHom ((scalarTensor.obj A).obj L) Z ≅ (ihom L).obj (innerHom A Z) :=
    (scalarTensorHomIso L A).app Z
  change bLB.hom ≫ (scalarLeibnizPullback s j Z).π =
    innerHomPre (scalarPushoutObjObj s j).ι Z ≫ (scalarLeibnizPointIso s j Z).hom
  apply (scalarLeibnizPullback s j Z).hom_ext
  · have hinl := (innerHomPre_comp (scalarPushoutObjObj s j).ι
      (scalarPushoutObjObj s j).inl Z).trans
        (congrArg (fun f => innerHomPre f Z) (scalarPushoutObjObj s j).inl_ι)
    have hleft : (bLB.hom ≫ (scalarLeibnizPullback s j Z).π) ≫
        (scalarLeibnizPullback s j Z).fst = bLB.hom ≫ (pre j).app (innerHom B Z) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f => bLB.hom ≫ f) (scalarLeibnizPullback s j Z).π_fst)
    have hright : (innerHomPre (scalarPushoutObjObj s j).ι Z ≫
        (scalarLeibnizPointIso s j Z).hom) ≫ (scalarLeibnizPullback s j Z).fst =
        innerHomPre ((scalarTensor.obj B).map j) Z ≫ bKB.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => innerHomPre (scalarPushoutObjObj s j).ι Z ≫ f)
          (scalarLeibnizPointIso_hom_fst s j Z)).trans
          (((Category.assoc _ _ _).symm).trans
            (congrArg (fun f => f ≫ bKB.hom) hinl)))
    exact hleft.trans ((scalarTensorHomIso_naturality_scalar j B Z).symm.trans hright.symm)
  · have hinr := (innerHomPre_comp (scalarPushoutObjObj s j).ι
      (scalarPushoutObjObj s j).inr Z).trans
        (congrArg (fun f => innerHomPre f Z) (scalarPushoutObjObj s j).inr_ι)
    have hleft : (bLB.hom ≫ (scalarLeibnizPullback s j Z).π) ≫
        (scalarLeibnizPullback s j Z).snd = bLB.hom ≫ (ihom L).map (innerHomPre s Z) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun f => bLB.hom ≫ f) (scalarLeibnizPullback s j Z).π_snd)
    have hright : (innerHomPre (scalarPushoutObjObj s j).ι Z ≫
        (scalarLeibnizPointIso s j Z).hom) ≫ (scalarLeibnizPullback s j Z).snd =
        innerHomPre ((scalarTensor.map s).app L) Z ≫ bLA.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f => innerHomPre (scalarPushoutObjObj s j).ι Z ≫ f)
          (scalarLeibnizPointIso_hom_snd s j Z)).trans
          (((Category.assoc _ _ _).symm).trans
            (congrArg (fun f => f ≫ bLA.hom) hinr)))
    exact hleft.trans ((scalarTensorHomIso_naturality_source L s Z).symm.trans hright.symm)

/-- The actual whole Arrow isomorphism, with its original source and target components. -/
def scalarLeibnizHomIso {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    Arrow.mk (innerHomPre (scalarPushoutObjObj s j).ι Z) ≅
      Arrow.mk (SSet.ihomToPullback j (innerHomPre s Z)) :=
  Arrow.isoMk ((scalarTensorHomIso L B).app Z) (scalarLeibnizPointIso s j Z)
    (scalarLeibnizHomIso_square s j Z)

/-- The original Arrow source is exactly the constructed scalar comparison. -/
theorem scalarLeibnizHomIso_hom_left {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizHomIso s j Z).hom.left = (scalarTensorHomIso L B).hom.app Z := rfl

/-- Its inverse uses the same original scalar inverse. -/
theorem scalarLeibnizHomIso_inv_left {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizHomIso s j Z).inv.left = (scalarTensorHomIso L B).inv.app Z := rfl

/-- Both complete Arrow composites are the identities on the original arrows. -/
theorem scalarLeibnizHomIso_inverse_ids {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizHomIso s j Z).hom ≫ (scalarLeibnizHomIso s j Z).inv = 𝟙 _ ∧
      (scalarLeibnizHomIso s j Z).inv ≫ (scalarLeibnizHomIso s j Z).hom = 𝟙 _ :=
  ⟨(scalarLeibnizHomIso s j Z).hom_inv_id, (scalarLeibnizHomIso s j Z).inv_hom_id⟩

/-- Every forward left projection retains its actual original site end projection. -/
theorem scalarLeibnizPointIso_end_fst {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) (R : SSet.{u})
    (b : R ⟶ innerHom (scalarPushoutObjObj s j).pt Z) (d : Dᵒᵖ) :
    uncurry (b ≫ (scalarLeibnizPointIso s j Z).hom ≫ (scalarLeibnizPullback s j Z).fst) ≫
        innerHomπ B Z d =
      curry ((α_ (B.obj d) K R).inv ≫
        ((scalarTensorHomEquiv ((scalarTensor.obj B).obj K) R Z).symm
          (b ≫ innerHomPre (scalarPushoutObjObj s j).inl Z)).app d) := by
  have hp := (Category.assoc b (scalarLeibnizPointIso s j Z).hom
      (scalarLeibnizPullback s j Z).fst).trans
    ((congrArg (fun f => b ≫ f) (scalarLeibnizPointIso_hom_fst s j Z)).trans
      (Category.assoc _ _ _).symm)
  exact (congrArg (fun f => uncurry f ≫ innerHomπ B Z d) hp).trans
    (scalarTensorHomIso_end_π K B Z R
      (b ≫ innerHomPre (scalarPushoutObjObj s j).inl Z) d)

/-- Every forward right projection retains its actual original site end projection. -/
theorem scalarLeibnizPointIso_end_snd {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D) (R : SSet.{u})
    (b : R ⟶ innerHom (scalarPushoutObjObj s j).pt Z) (d : Dᵒᵖ) :
    uncurry (b ≫ (scalarLeibnizPointIso s j Z).hom ≫ (scalarLeibnizPullback s j Z).snd) ≫
        innerHomπ A Z d =
      curry ((α_ (A.obj d) L R).inv ≫
        ((scalarTensorHomEquiv ((scalarTensor.obj A).obj L) R Z).symm
          (b ≫ innerHomPre (scalarPushoutObjObj s j).inr Z)).app d) := by
  have hp := (Category.assoc b (scalarLeibnizPointIso s j Z).hom
      (scalarLeibnizPullback s j Z).snd).trans
    ((congrArg (fun f => b ≫ f) (scalarLeibnizPointIso_hom_snd s j Z)).trans
      (Category.assoc _ _ _).symm)
  exact (congrArg (fun f => uncurry f ≫ innerHomπ A Z d) hp).trans
    (scalarTensorHomIso_end_π L A Z R
      (b ≫ innerHomPre (scalarPushoutObjObj s j).inr Z) d)

/-- The inverse left restriction retains all scalar parameters and actual end projections. -/
theorem scalarLeibnizPointIso_inv_end_fst {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D)
    (R : SSet.{u}) (c : R ⟶ (scalarLeibnizPullback s j Z).pt) (d : Dᵒᵖ) :
    uncurry (c ≫ (scalarLeibnizPointIso s j Z).inv ≫
      innerHomPre (scalarPushoutObjObj s j).inl Z ≫
        innerHomπ ((scalarTensor.obj B).obj K) Z d) =
      (α_ (B.obj d) K R).hom ≫
        ((scalarTensorHomEquiv B (K ⊗ R) Z).symm
          (uncurry (c ≫ (scalarLeibnizPullback s j Z).fst))).app d := by
  have hp := (Category.assoc c (scalarLeibnizPointIso s j Z).inv
      (innerHomPre (scalarPushoutObjObj s j).inl Z)).trans
    ((congrArg (fun f => c ≫ f) (scalarLeibnizPointIso_inv_fst s j Z)).trans
      (Category.assoc _ _ _).symm)
  exact (congrArg (fun f => uncurry (f ≫
    innerHomπ ((scalarTensor.obj B).obj K) Z d)) hp).trans
      (scalarTensorHomIso_inv_end_π K B Z R
        (c ≫ (scalarLeibnizPullback s j Z).fst) d)

/-- The inverse right restriction retains those same original parameters and projections. -/
theorem scalarLeibnizPointIso_inv_end_snd {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L) (Z : SimplicialPresheaf.{u} D)
    (R : SSet.{u}) (c : R ⟶ (scalarLeibnizPullback s j Z).pt) (d : Dᵒᵖ) :
    uncurry (c ≫ (scalarLeibnizPointIso s j Z).inv ≫
      innerHomPre (scalarPushoutObjObj s j).inr Z ≫
        innerHomπ ((scalarTensor.obj A).obj L) Z d) =
      (α_ (A.obj d) L R).hom ≫
        ((scalarTensorHomEquiv A (L ⊗ R) Z).symm
          (uncurry (c ≫ (scalarLeibnizPullback s j Z).snd))).app d := by
  have hp := (Category.assoc c (scalarLeibnizPointIso s j Z).inv
      (innerHomPre (scalarPushoutObjObj s j).inr Z)).trans
    ((congrArg (fun f => c ≫ f) (scalarLeibnizPointIso_inv_snd s j Z)).trans
      (Category.assoc _ _ _).symm)
  exact (congrArg (fun f => uncurry (f ≫
    innerHomπ ((scalarTensor.obj A).obj L) Z d)) hp).trans
      (scalarTensorHomIso_inv_end_π L A Z R
        (c ≫ (scalarLeibnizPullback s j Z).snd) d)

/-- The restriction square induced by an original target transformation. -/
def scalarRestrictionTargetMap {A B : SimplicialPresheaf.{u} D} (s : A ⟶ B)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    Arrow.mk (innerHomPre s Z) ⟶ Arrow.mk (innerHomPre s Z') :=
  Arrow.homMk (innerHomPost B g) (innerHomPost A g) (innerHom_exchange s g).symm

/-- The corresponding actual native scalar pullback square. -/
def scalarLeibnizTargetMap {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    Arrow.mk (scalarLeibnizPullback s j Z).π ⟶
      Arrow.mk (scalarLeibnizPullback s j Z').π :=
  Functor.PullbackObjObj.mapArrowRight (G := MonoidalClosed.internalHom)
    (f₁ := Arrow.mk j) (f₃ := Arrow.mk (innerHomPre s Z))
    (f₃' := Arrow.mk (innerHomPre s Z')) (scalarLeibnizPullback s j Z)
      (scalarLeibnizPullback s j Z') (scalarRestrictionTargetMap s g)

/-- Its first projection is the original target transformation on H(B,Z). -/
@[reassoc]
theorem scalarLeibnizTargetMap_fst {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    (scalarLeibnizTargetMap s j g).right ≫ (scalarLeibnizPullback s j Z').fst =
      (scalarLeibnizPullback s j Z).fst ≫ (ihom K).map (innerHomPost B g) := by
  simp only [scalarLeibnizTargetMap, Functor.PullbackObjObj.mapArrowRight_right,
    IsPullback.lift_fst, scalarRestrictionTargetMap, Arrow.homMk_left]
  rfl

/-- Its second projection is the original target transformation on H(A,Z). -/
@[reassoc]
theorem scalarLeibnizTargetMap_snd {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    (scalarLeibnizTargetMap s j g).right ≫ (scalarLeibnizPullback s j Z').snd =
      (scalarLeibnizPullback s j Z).snd ≫ (ihom L).map (innerHomPost A g) := by
  simp only [scalarLeibnizTargetMap, Functor.PullbackObjObj.mapArrowRight_right,
    IsPullback.lift_snd, scalarRestrictionTargetMap, Arrow.homMk_right]
  rfl

/-- The original target transformation acts on the whole mapped pushout arrow. -/
def scalarLeibnizInputTargetMap {A B : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
    (s : A ⟶ B) (j : K ⟶ L) {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    Arrow.mk (innerHomPre (scalarPushoutObjObj s j).ι Z) ⟶
      Arrow.mk (innerHomPre (scalarPushoutObjObj s j).ι Z') :=
  Arrow.homMk (innerHomPost ((scalarTensor.obj B).obj L) g)
    (innerHomPost (scalarPushoutObjObj s j).pt g)
    (innerHom_exchange (scalarPushoutObjObj s j).ι g).symm

/-- The whole point comparison is natural in every original target map. -/
theorem scalarLeibnizPointIso_naturality_target {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    innerHomPost (scalarPushoutObjObj s j).pt g ≫ (scalarLeibnizPointIso s j Z').hom =
      (scalarLeibnizPointIso s j Z).hom ≫ (scalarLeibnizTargetMap s j g).right := by
  apply (scalarLeibnizPullback s j Z').hom_ext
  · have hh : innerHomPost (scalarPushoutObjObj s j).pt g ≫
        (innerHomPre (scalarPushoutObjObj s j).inl Z' ≫ (scalarTensorHomIso K B).hom.app Z') =
        (innerHomPre (scalarPushoutObjObj s j).inl Z ≫ (scalarTensorHomIso K B).hom.app Z) ≫
          (ihom K).map (innerHomPost B g) :=
      ((Category.assoc _ _ _).symm).trans
        ((congrArg (fun f => f ≫ (scalarTensorHomIso K B).hom.app Z')
          (innerHom_exchange (scalarPushoutObjObj s j).inl g).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => innerHomPre (scalarPushoutObjObj s j).inl Z ≫ f)
              (scalarTensorHomIso_naturality_target K B g)).trans
              (Category.assoc _ _ _).symm)))
    have hl := (Category.assoc _ _ _).trans
      ((congrArg (fun f => innerHomPost (scalarPushoutObjObj s j).pt g ≫ f)
        (scalarLeibnizPointIso_hom_fst s j Z')).trans hh)
    have hr := (Category.assoc _ _ _).trans
      ((congrArg (fun f => (scalarLeibnizPointIso s j Z).hom ≫ f)
        (scalarLeibnizTargetMap_fst s j g)).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun f => f ≫ (ihom K).map (innerHomPost B g))
            (scalarLeibnizPointIso_hom_fst s j Z))))
    exact hl.trans hr.symm
  · have hh : innerHomPost (scalarPushoutObjObj s j).pt g ≫
        (innerHomPre (scalarPushoutObjObj s j).inr Z' ≫ (scalarTensorHomIso L A).hom.app Z') =
        (innerHomPre (scalarPushoutObjObj s j).inr Z ≫ (scalarTensorHomIso L A).hom.app Z) ≫
          (ihom L).map (innerHomPost A g) :=
      ((Category.assoc _ _ _).symm).trans
        ((congrArg (fun f => f ≫ (scalarTensorHomIso L A).hom.app Z')
          (innerHom_exchange (scalarPushoutObjObj s j).inr g).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => innerHomPre (scalarPushoutObjObj s j).inr Z ≫ f)
              (scalarTensorHomIso_naturality_target L A g)).trans
              (Category.assoc _ _ _).symm)))
    have hl := (Category.assoc _ _ _).trans
      ((congrArg (fun f => innerHomPost (scalarPushoutObjObj s j).pt g ≫ f)
        (scalarLeibnizPointIso_hom_snd s j Z')).trans hh)
    have hr := (Category.assoc _ _ _).trans
      ((congrArg (fun f => (scalarLeibnizPointIso s j Z).hom ≫ f)
        (scalarLeibnizTargetMap_snd s j g)).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun f => f ≫ (ihom L).map (innerHomPost A g))
            (scalarLeibnizPointIso_hom_snd s j Z))))
    exact hl.trans hr.symm

/-- Naturality is an equality of the two entire original Arrow composites. -/
theorem scalarLeibnizHomIso_naturality_target {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    scalarLeibnizInputTargetMap s j g ≫ (scalarLeibnizHomIso s j Z').hom =
      (scalarLeibnizHomIso s j Z).hom ≫ scalarLeibnizTargetMap s j g := by
  apply Arrow.hom_ext
  · exact scalarTensorHomIso_naturality_target L B g
  · exact scalarLeibnizPointIso_naturality_target s j g

private theorem inverseNaturality {C : Type*} [Category* C] {X X' Y Y' : C}
    (e : X ≅ X') (e' : Y ≅ Y') (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : a ≫ e'.hom = e.hom ≫ b) : b ≫ e'.inv = e.inv ≫ a := by
  apply (Iso.eq_inv_comp e).2
  exact ((Category.assoc _ _ _).symm).trans
    ((congrArg (fun f => f ≫ e'.inv) h.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => a ≫ f) e'.hom_inv_id).trans (Category.comp_id a))))

/-- The inverse whole Arrow square retains that same original target map. -/
theorem scalarLeibnizHomIso_inv_naturality_target {A B : SimplicialPresheaf.{u} D}
    {K L : SSet.{u}} (s : A ⟶ B) (j : K ⟶ L)
    {Z Z' : SimplicialPresheaf.{u} D} (g : Z ⟶ Z') :
    scalarLeibnizTargetMap s j g ≫ (scalarLeibnizHomIso s j Z').inv =
      (scalarLeibnizHomIso s j Z).inv ≫ scalarLeibnizInputTargetMap s j g :=
  inverseNaturality _ _ _ _ (scalarLeibnizHomIso_naturality_target s j g)

/-- The canonical native pushout transport for both original Arrow morphisms. -/
def scalarPushoutArrowMap {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') :
    Arrow.mk (scalarPushoutObjObj s.hom j.hom).ι ⟶
      Arrow.mk (scalarPushoutObjObj s'.hom j'.hom).ι :=
  Functor.PushoutObjObj.mapArrowLeft (F := scalarTensor (D := D))
    (f₁ := s) (f₁' := s') (f₂ := j)
    (scalarPushoutObjObj s.hom j.hom) (scalarPushoutObjObj s'.hom j.hom) a ≫
  Functor.PushoutObjObj.mapArrowRight (F := scalarTensor (D := D))
    (f₁ := s') (f₂ := j) (f₂' := j')
    (scalarPushoutObjObj s'.hom j.hom) (scalarPushoutObjObj s'.hom j'.hom) b

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The original left injection is retained by the canonical combined pushout map. -/
@[reassoc]
theorem scalarPushoutArrowMap_inl {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') :
    (scalarPushoutObjObj s.hom j.hom).inl ≫ (scalarPushoutArrowMap a b).left =
      ((scalarTensor.map a.right).app j.left ≫ (scalarTensor.obj s'.right).map b.left) ≫
        (scalarPushoutObjObj s'.hom j'.hom).inl := by
  simp only [scalarPushoutArrowMap, Arrow.comp_left,
    Functor.PushoutObjObj.mapArrowLeft_left, Functor.PushoutObjObj.mapArrowRight_left,
    Category.assoc, IsPushout.inl_desc_assoc, IsPushout.inl_desc]

omit [Small.{u} D] [LocallySmall.{u} D] in
/-- The original right injection is retained by that same canonical map. -/
@[reassoc]
theorem scalarPushoutArrowMap_inr {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') :
    (scalarPushoutObjObj s.hom j.hom).inr ≫ (scalarPushoutArrowMap a b).left =
      ((scalarTensor.map a.left).app j.right ≫ (scalarTensor.obj s'.left).map b.right) ≫
        (scalarPushoutObjObj s'.hom j'.hom).inr := by
  simp only [scalarPushoutArrowMap, Arrow.comp_left,
    Functor.PushoutObjObj.mapArrowLeft_left, Functor.PushoutObjObj.mapArrowRight_left,
    Category.assoc, IsPushout.inr_desc_assoc, IsPushout.inr_desc]

/-- Original source Arrow maps act contravariantly on the entire restriction square. -/
def scalarRestrictionSourceMap {s s' : Arrow (SimplicialPresheaf.{u} D)}
    (a : s ⟶ s') (Z : SimplicialPresheaf.{u} D) :
    Arrow.mk (innerHomPre s'.hom Z) ⟶ Arrow.mk (innerHomPre s.hom Z) :=
  Arrow.homMk (innerHomPre a.right Z) (innerHomPre a.left Z)
    ((innerHomPre_comp a.right s.hom Z).trans
      ((congrArg (fun f => innerHomPre f Z) a.w.symm).trans
        (innerHomPre_comp s'.hom a.left Z).symm))

/-- The actual scalar pullback transport goes from the new arrows to the old arrows. -/
def scalarLeibnizTransportMap {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    Arrow.mk (scalarLeibnizPullback s'.hom j'.hom Z).π ⟶
      Arrow.mk (scalarLeibnizPullback s.hom j.hom Z).π :=
  Functor.PullbackObjObj.mapArrowRight (G := MonoidalClosed.internalHom)
    (f₁ := j') (f₃ := Arrow.mk (innerHomPre s'.hom Z))
    (f₃' := Arrow.mk (innerHomPre s.hom Z))
    (scalarLeibnizPullback s'.hom j'.hom Z) (scalarLeibnizPullback s.hom j'.hom Z)
    (scalarRestrictionSourceMap a Z) ≫
  Functor.PullbackObjObj.mapArrowLeft (G := MonoidalClosed.internalHom)
    (f₁ := j') (f₁' := j) (f₃ := Arrow.mk (innerHomPre s.hom Z))
    (scalarLeibnizPullback s.hom j'.hom Z) (scalarLeibnizPullback s.hom j.hom Z) b

/-- The first projection keeps both original source and scalar components, in native order. -/
@[reassoc]
theorem scalarLeibnizTransportMap_fst {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizTransportMap a b Z).right ≫ (scalarLeibnizPullback s.hom j.hom Z).fst =
      (scalarLeibnizPullback s'.hom j'.hom Z).fst ≫
        (ihom j'.left).map (innerHomPre a.right Z) ≫
          (pre b.left).app (innerHom s.right Z) := by
  simp only [scalarLeibnizTransportMap, Arrow.comp_right,
    Functor.PullbackObjObj.mapArrowLeft_right, Functor.PullbackObjObj.mapArrowRight_right,
    Category.assoc, IsPullback.lift_fst, IsPullback.lift_fst_assoc,
    scalarRestrictionSourceMap, Arrow.homMk_left]
  rfl

/-- The second projection keeps both original components on the other pullback leg. -/
@[reassoc]
theorem scalarLeibnizTransportMap_snd {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    (scalarLeibnizTransportMap a b Z).right ≫ (scalarLeibnizPullback s.hom j.hom Z).snd =
      (scalarLeibnizPullback s'.hom j'.hom Z).snd ≫
        (ihom j'.right).map (innerHomPre a.left Z) ≫
          (pre b.right).app (innerHom s.left Z) := by
  simp only [scalarLeibnizTransportMap, Arrow.comp_right,
    Functor.PullbackObjObj.mapArrowLeft_right, Functor.PullbackObjObj.mapArrowRight_right,
    Category.assoc, IsPullback.lift_snd, IsPullback.lift_snd_assoc,
    scalarRestrictionSourceMap, Arrow.homMk_right]
  rfl

/-- The whole mapped pushout transport is contravariant in those same original arrows. -/
def scalarLeibnizInputTransportMap {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    Arrow.mk (innerHomPre (scalarPushoutObjObj s'.hom j'.hom).ι Z) ⟶
      Arrow.mk (innerHomPre (scalarPushoutObjObj s.hom j.hom).ι Z) :=
  Arrow.homMk (innerHomPre (scalarPushoutArrowMap a b).right Z)
    (innerHomPre (scalarPushoutArrowMap a b).left Z)
    ((innerHomPre_comp (scalarPushoutArrowMap a b).right
      (scalarPushoutObjObj s.hom j.hom).ι Z).trans
        ((congrArg (fun f => innerHomPre f Z) (scalarPushoutArrowMap a b).w.symm).trans
          (innerHomPre_comp (scalarPushoutObjObj s'.hom j'.hom).ι
            (scalarPushoutArrowMap a b).left Z).symm))

private theorem tensorHomCombined {A A' : SimplicialPresheaf.{u} D}
    {K K' : SSet.{u}} (a : A ⟶ A') (b : K ⟶ K') (Z : SimplicialPresheaf.{u} D) :
    innerHomPre ((scalarTensor.map a).app K ≫ (scalarTensor.obj A').map b) Z ≫
        (scalarTensorHomIso K A).hom.app Z =
      (scalarTensorHomIso K' A').hom.app Z ≫ (ihom K').map (innerHomPre a Z) ≫
        (pre b).app (innerHom A Z) := by
  have hs := scalarTensorHomIso_naturality_source K a Z
  have hb := scalarTensorHomIso_naturality_scalar b A' Z
  have hn := (pre b).naturality (innerHomPre a Z)
  have hc := innerHomPre_comp ((scalarTensor.obj A').map b) ((scalarTensor.map a).app K) Z
  exact (congrArg (fun f => f ≫ (scalarTensorHomIso K A).hom.app Z) hc.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun f => innerHomPre ((scalarTensor.obj A').map b) Z ≫ f) hs).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (fun f => f ≫ (ihom K).map (innerHomPre a Z)) hb).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun f => (scalarTensorHomIso K' A').hom.app Z ≫ f) hn.symm).trans
                (Category.assoc _ _ _).symm))))))

/-- Both original Arrow changes commute with the entire point comparison. -/
theorem scalarLeibnizPointIso_naturality_transport {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    innerHomPre (scalarPushoutArrowMap a b).left Z ≫
        (scalarLeibnizPointIso s.hom j.hom Z).hom =
      (scalarLeibnizPointIso s'.hom j'.hom Z).hom ≫ (scalarLeibnizTransportMap a b Z).right := by
  apply (scalarLeibnizPullback s.hom j.hom Z).hom_ext
  · let t := (scalarTensor.map a.right).app j.left ≫ (scalarTensor.obj s'.right).map b.left
    have hp : innerHomPre (scalarPushoutArrowMap a b).left Z ≫
        innerHomPre (scalarPushoutObjObj s.hom j.hom).inl Z =
        innerHomPre (scalarPushoutObjObj s'.hom j'.hom).inl Z ≫ innerHomPre t Z :=
      (innerHomPre_comp _ _ Z).trans
        ((congrArg (fun f => innerHomPre f Z) (scalarPushoutArrowMap_inl a b)).trans
          (innerHomPre_comp _ _ Z).symm)
    have hh : innerHomPre (scalarPushoutArrowMap a b).left Z ≫
        (innerHomPre (scalarPushoutObjObj s.hom j.hom).inl Z ≫
          (scalarTensorHomIso j.left s.right).hom.app Z) =
        (innerHomPre (scalarPushoutObjObj s'.hom j'.hom).inl Z ≫
          (scalarTensorHomIso j'.left s'.right).hom.app Z) ≫
            ((ihom j'.left).map (innerHomPre a.right Z) ≫
              (pre b.left).app (innerHom s.right Z)) :=
      ((Category.assoc _ _ _).symm).trans
        ((congrArg (fun f => f ≫ (scalarTensorHomIso j.left s.right).hom.app Z) hp).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => innerHomPre (scalarPushoutObjObj s'.hom j'.hom).inl Z ≫ f)
              (tensorHomCombined a.right b.left Z)).trans (Category.assoc _ _ _).symm)))
    have hl := (Category.assoc _ _ _).trans
      ((congrArg (fun f => innerHomPre (scalarPushoutArrowMap a b).left Z ≫ f)
        (scalarLeibnizPointIso_hom_fst s.hom j.hom Z)).trans hh)
    have hr := (Category.assoc _ _ _).trans
      ((congrArg (fun f => (scalarLeibnizPointIso s'.hom j'.hom Z).hom ≫ f)
        (scalarLeibnizTransportMap_fst a b Z)).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun f => f ≫ ((ihom j'.left).map (innerHomPre a.right Z) ≫
            (pre b.left).app (innerHom s.right Z)))
            (scalarLeibnizPointIso_hom_fst s'.hom j'.hom Z))))
    exact hl.trans hr.symm
  · let t := (scalarTensor.map a.left).app j.right ≫ (scalarTensor.obj s'.left).map b.right
    have hp : innerHomPre (scalarPushoutArrowMap a b).left Z ≫
        innerHomPre (scalarPushoutObjObj s.hom j.hom).inr Z =
        innerHomPre (scalarPushoutObjObj s'.hom j'.hom).inr Z ≫ innerHomPre t Z :=
      (innerHomPre_comp _ _ Z).trans
        ((congrArg (fun f => innerHomPre f Z) (scalarPushoutArrowMap_inr a b)).trans
          (innerHomPre_comp _ _ Z).symm)
    have hh : innerHomPre (scalarPushoutArrowMap a b).left Z ≫
        (innerHomPre (scalarPushoutObjObj s.hom j.hom).inr Z ≫
          (scalarTensorHomIso j.right s.left).hom.app Z) =
        (innerHomPre (scalarPushoutObjObj s'.hom j'.hom).inr Z ≫
          (scalarTensorHomIso j'.right s'.left).hom.app Z) ≫
            ((ihom j'.right).map (innerHomPre a.left Z) ≫
              (pre b.right).app (innerHom s.left Z)) :=
      ((Category.assoc _ _ _).symm).trans
        ((congrArg (fun f => f ≫ (scalarTensorHomIso j.right s.left).hom.app Z) hp).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => innerHomPre (scalarPushoutObjObj s'.hom j'.hom).inr Z ≫ f)
              (tensorHomCombined a.left b.right Z)).trans (Category.assoc _ _ _).symm)))
    have hl := (Category.assoc _ _ _).trans
      ((congrArg (fun f => innerHomPre (scalarPushoutArrowMap a b).left Z ≫ f)
        (scalarLeibnizPointIso_hom_snd s.hom j.hom Z)).trans hh)
    have hr := (Category.assoc _ _ _).trans
      ((congrArg (fun f => (scalarLeibnizPointIso s'.hom j'.hom Z).hom ≫ f)
        (scalarLeibnizTransportMap_snd a b Z)).trans
        (((Category.assoc _ _ _).symm).trans
          (congrArg (fun f => f ≫ ((ihom j'.right).map (innerHomPre a.left Z) ≫
            (pre b.right).app (innerHom s.left Z)))
            (scalarLeibnizPointIso_hom_snd s'.hom j'.hom Z))))
    exact hl.trans hr.symm

/-- The equality holds for the two whole original Arrow composites. -/
theorem scalarLeibnizHomIso_naturality_transport {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    scalarLeibnizInputTransportMap a b Z ≫ (scalarLeibnizHomIso s.hom j.hom Z).hom =
      (scalarLeibnizHomIso s'.hom j'.hom Z).hom ≫ scalarLeibnizTransportMap a b Z := by
  apply Arrow.hom_ext
  · exact tensorHomCombined a.right b.right Z
  · exact scalarLeibnizPointIso_naturality_transport a b Z

/-- The inverse comparison retains those same original contravariant Arrow changes. -/
theorem scalarLeibnizHomIso_inv_naturality_transport {s s' : Arrow (SimplicialPresheaf.{u} D)}
    {j j' : Arrow SSet.{u}} (a : s ⟶ s') (b : j ⟶ j') (Z : SimplicialPresheaf.{u} D) :
    scalarLeibnizTransportMap a b Z ≫ (scalarLeibnizHomIso s.hom j.hom Z).inv =
      (scalarLeibnizHomIso s'.hom j'.hom Z).inv ≫ scalarLeibnizInputTransportMap a b Z :=
  inverseNaturality _ _ _ _ (scalarLeibnizHomIso_naturality_transport a b Z)

end SimplicialPresheaf
