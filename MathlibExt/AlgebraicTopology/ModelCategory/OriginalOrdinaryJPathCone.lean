/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedArrowFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.OrdinaryHoChosenPuppe
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Original J path cones and the actual fibre-side cofiber

The original fixed-κ J factory factors every map from the caller's zero
object. Its entire middle functor, zero insertion and fibration projection
provide a cone in the opposite model category. The opposite chosen cofiber
is an actual pullback of that original projection and the original input
arrow, with both projections retained. At a fibration with fibrant target,
the caller's ordinary fibre maps weakly to that same cofiber. The original
J insertion and the model's cofibrant cube prove this comparison.

The source data are the given generation on C and its same κ and bottom.
The loop/suspension identification and the signed covariant Puppe maps are
subsequent constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra
open Opposite

namespace HomotopicalAlgebra.OriginalOrdinaryJPathCone

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- Every zero-source square retains the actual original target map. -/
def initialArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (hZ.isInitial.to X)
  map {X Y} f := Arrow.homMk (𝟙 Z) f (by
    change (𝟙 Z) ≫ hZ.isInitial.to Y = hZ.isInitial.to X ≫ f
    rw [Category.id_comp]
    exact hZ.isInitial.hom_ext _ _)
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (Category.id_comp _).symm
    · rfl

/-- The original J middle functor at the literal original zero-source arrows. -/
def pathObject : C ⥤ C := initialArrowFunctor Z hZ ⋙ (GeneratedArrowFactorizations.fibrant d).Z

/-- The original J left factor is the complete natural zero insertion. -/
def insertion : (Functor.const C).obj Z ⟶ pathObject d Z hZ where
  app X := (GeneratedArrowFactorizations.fibrant d).i.app ((initialArrowFunctor Z hZ).obj X)
  naturality _ _ f := (GeneratedArrowFactorizations.fibrant d).i.naturality
    ((initialArrowFunctor Z hZ).map f)

/-- The entire original J right factor is the same natural fibration projection. -/
def projection : pathObject d Z hZ ⟶ 𝟭 C where
  app X := (GeneratedArrowFactorizations.fibrant d).p.app ((initialArrowFunctor Z hZ).obj X)
  naturality _ _ f := (GeneratedArrowFactorizations.fibrant d).p.naturality
    ((initialArrowFunctor Z hZ).map f)

/-- Both original J factors recover the actual caller zero-source arrow. -/
theorem insertion_projection (X : C) :
    (insertion d Z hZ).app X ≫ (projection d Z hZ).app X = hZ.isInitial.to X :=
  (GeneratedArrowFactorizations.fibrant d).fac_app

/-- Every original zero insertion belongs to the actual original trivial-cofibration class. -/
theorem insertion_trivialCofibration (X : C) :
    trivialCofibrations C ((insertion d Z hZ).app X) :=
  (GeneratedArrowFactorizations.fibrant d).hi ((initialArrowFunctor Z hZ).obj X)

/-- Every original path projection is a fibration by its actual original factor class. -/
theorem projection_fibration (X : C) : fibrations C ((projection d Z hZ).app X) :=
  (GeneratedArrowFactorizations.fibrant d).hp ((initialArrowFunctor Z hZ).obj X)

/-- The actual original zero insertion is weak. -/
theorem insertion_weak (X : C) : weakEquivalences C ((insertion d Z hZ).app X) :=
  (insertion_trivialCofibration d Z hZ X).2

/-- Every original J middle object is cofibrant from that same original zero insertion. -/
theorem pathObject_isCofibrant (X : C) : IsCofibrant ((pathObject d Z hZ).obj X) := by
  let : IsCofibrant Z := (isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial).mpr (by infer_instance)
  let : IsCofibrant (((Functor.const C).obj Z).obj X) := inferInstanceAs (IsCofibrant Z)
  let : Cofibration ((insertion d Z hZ).app X) :=
    (cofibration_iff _).mpr (insertion_trivialCofibration d Z hZ X).1
  exact isCofibrant_of_cofibration ((insertion d Z hZ).app X)

/-- At a fibrant original target the same original J middle object is fibrant. -/
theorem pathObject_isFibrant (X : C) [IsFibrant X] : IsFibrant ((pathObject d Z hZ).obj X) := by
  let : IsFibrant ((𝟭 C).obj X) := inferInstanceAs (IsFibrant X)
  let : Fibration ((projection d Z hZ).app X) := (fibration_iff _).mpr (projection_fibration d Z hZ X)
  exact isFibrant_of_fibration ((projection d Z hZ).app X)

/-- Every entire original path map is weak by the two original zero insertions and their actual square. -/
theorem pathObject_map_weak {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C ((pathObject d Z hZ).map f) := by
  have h : (insertion d Z hZ).app X ≫ (pathObject d Z hZ).map f = (insertion d Z hZ).app Y := by
    simpa using ((insertion d Z hZ).naturality f).symm
  exact (weakEquivalences C).of_precomp ((insertion d Z hZ).app X) _
    (insertion_weak d Z hZ X) (h.symm ▸ insertion_weak d Z hZ Y)

/-- The whole original J functor supplies the opposite-category cone. -/
def oppositeCone : Cᵒᵖ ⥤ Cᵒᵖ := (pathObject d Z hZ).op

/-- The complete opposite insertion is the original fibration projection, reversed. -/
def oppositeInclusion : 𝟭 Cᵒᵖ ⟶ oppositeCone d Z hZ :=
  NatTrans.op (projection d Z hZ)

/-- The original zero insertion, reversed, is the whole opposite cone contraction. -/
def oppositeContraction : oppositeCone d Z hZ ⟶ (Functor.const Cᵒᵖ).obj (op Z) :=
  NatTrans.op (insertion d Z hZ)

/-- Every opposite insertion is a cofibration by the same original J fibration law. -/
theorem oppositeInclusion_cofibration (X : Cᵒᵖ) :
    Cofibration ((oppositeInclusion d Z hZ).app X) :=
  (cofibration_op_iff _).mpr ((fibration_iff _).mpr (projection_fibration d Z hZ X.unop))

/-- The actual original opposite contraction is weak by the original J trivial cofibration. -/
theorem oppositeContraction_weak (X : Cᵒᵖ) :
    weakEquivalences Cᵒᵖ ((oppositeContraction d Z hZ).app X) := by
  apply (weakEquivalence_iff _).mp
  exact (weakEquivalences_op_iff _).mpr
    ((weakEquivalence_iff _).mpr (insertion_weak d Z hZ X.unop))

/-- The entire opposite contraction is the literal caller zero endpoint used in the Puppe source. -/
theorem opposite_toZero_weak (X : Cᵒᵖ) :
    weakEquivalences Cᵒᵖ
      (OrdinaryHoChosenPuppe.toZero (op Z) hZ.op ((oppositeCone d Z hZ).obj X)) := by
  have h : (oppositeContraction d Z hZ).app X =
      OrdinaryHoChosenPuppe.toZero (op Z) hZ.op ((oppositeCone d Z hZ).obj X) :=
    hZ.op.isTerminal.hom_ext _ _
  rw [← h]
  exact oppositeContraction_weak d Z hZ X

/-- The opposite cofiber is the chosen pushout of the original J insertion and original input. -/
def oppositeCofiberCocone (F : Arrow Cᵒᵖ) :
    PushoutCocone ((oppositeInclusion d Z hZ).app F.left) F.hom :=
  pushout.cocone ((oppositeInclusion d Z hZ).app F.left) F.hom

/-- Its full colimit witness retains that same actual chosen pushout. -/
def oppositeCofiberIsColimit (F : Arrow Cᵒᵖ) : IsColimit (oppositeCofiberCocone d Z hZ F) :=
  pushout.isColimit ((oppositeInclusion d Z hZ).app F.left) F.hom

/-- Both reversed cofiber legs are the actual original pullback projections. -/
theorem oppositeCofiber_isPullback {X Y : C} (p : X ⟶ Y) :
    IsPullback ((oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).inr.unop)
      ((oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).inl.unop)
      p ((projection d Z hZ).app Y) :=
  (IsPushout.of_isColimit (oppositeCofiberIsColimit d Z hZ (Arrow.mk p.op))).unop

/-- The actual opposite cofiber is retained as the full original path-pullback cone. -/
def oppositeCofiberPullbackCone {X Y : C} (p : X ⟶ Y) :
    PullbackCone p ((projection d Z hZ).app Y) :=
  (oppositeCofiber_isPullback d Z hZ p).cone

/-- The entire pullback universal property is earned from the original opposite pushout witness. -/
def oppositeCofiberPullbackIsLimit {X Y : C} (p : X ⟶ Y) :
    IsLimit (oppositeCofiberPullbackCone d Z hZ p) :=
  (oppositeCofiber_isPullback d Z hZ p).isLimit

/-- The whole same cofiber compares isomorphically to every actual caller-selected path pullback. -/
def oppositeCofiberIsoPullback {X Y : C} (p : X ⟶ Y)
    (t : PullbackCone p ((projection d Z hZ).app Y)) (ht : IsLimit t) :
    (oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).pt.unop ≅ t.pt :=
  (oppositeCofiberPullbackIsLimit d Z hZ p).conePointUniqueUpToIso ht

/-- The complete first comparison projection is the original cofiber target leg, reversed. -/
theorem oppositeCofiberIsoPullback_fst {X Y : C} (p : X ⟶ Y)
    (t : PullbackCone p ((projection d Z hZ).app Y)) (ht : IsLimit t) :
    (oppositeCofiberIsoPullback d Z hZ p t ht).hom ≫ t.fst =
      (oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).inr.unop :=
  IsLimit.conePointUniqueUpToIso_hom_comp (oppositeCofiberPullbackIsLimit d Z hZ p) ht WalkingCospan.left

/-- The full second comparison projection is the original cofiber cone leg, reversed. -/
theorem oppositeCofiberIsoPullback_snd {X Y : C} (p : X ⟶ Y)
    (t : PullbackCone p ((projection d Z hZ).app Y)) (ht : IsLimit t) :
    (oppositeCofiberIsoPullback d Z hZ p t ht).hom ≫ t.snd =
      (oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).inl.unop :=
  IsLimit.conePointUniqueUpToIso_hom_comp (oppositeCofiberPullbackIsLimit d Z hZ p) ht WalkingCospan.right

/-- The caller's whole ordinary fibre maps by the actual limiting lift to that same opposite cofiber. -/
def fiberToOppositeCofiber {X Y : C} (p : X ⟶ Y)
    (s : PullbackCone p (hZ.isInitial.to Y)) :
    s.pt ⟶ (oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).pt.unop :=
  (oppositeCofiberPullbackIsLimit d Z hZ p).lift
    (PullbackCone.mk s.fst (s.snd ≫ (insertion d Z hZ).app Y) (by
      rw [Category.assoc, insertion_projection]
      exact s.condition))

/-- Every original first fibre projection is preserved by the complete comparison map. -/
theorem fiberToOppositeCofiber_fst {X Y : C} (p : X ⟶ Y)
    (s : PullbackCone p (hZ.isInitial.to Y)) :
    fiberToOppositeCofiber d Z hZ p s ≫
        (oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).inr.unop = s.fst :=
  (oppositeCofiberPullbackIsLimit d Z hZ p).fac _ WalkingCospan.left

/-- The full original zero-source fibre projection retains its original J insertion. -/
theorem fiberToOppositeCofiber_snd {X Y : C} (p : X ⟶ Y)
    (s : PullbackCone p (hZ.isInitial.to Y)) :
    fiberToOppositeCofiber d Z hZ p s ≫
        (oppositeCofiberCocone d Z hZ (Arrow.mk p.op)).inl.unop =
      s.snd ≫ (insertion d Z hZ).app Y :=
  (oppositeCofiberPullbackIsLimit d Z hZ p).fac _ WalkingCospan.right

private theorem op_isCofibrant (X : C) [IsFibrant X] : IsCofibrant (op X) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from X).op terminalIsTerminal.op).mpr
  exact (cofibration_op_iff _).mpr inferInstance

/-- The original weak J insertion gives the full actual fibre/cofiber comparison at every fibrant-target fibration. -/
theorem fiberToOppositeCofiber_weak {X Y : C} (p : X ⟶ Y) [Fibration p] [IsFibrant Y]
    (s : PullbackCone p (hZ.isInitial.to Y)) (hs : IsLimit s) :
    WeakEquivalence (fiberToOppositeCofiber d Z hZ p s) := by
  let : IsFibrant ((pathObject d Z hZ).obj Y) := pathObject_isFibrant d Z hZ Y
  let : IsFibrant Z := (isFibrant_iff_of_isTerminal (𝟙 Z) hZ.isTerminal).mpr (by infer_instance)
  let : IsCofibrant (op Y) := op_isCofibrant Y
  let : IsCofibrant (op ((pathObject d Z hZ).obj Y)) := op_isCofibrant _
  let : IsCofibrant (op (unop ((oppositeCone d Z hZ).obj (Arrow.mk p.op).left))) := by
    simpa [oppositeCone] using op_isCofibrant ((pathObject d Z hZ).obj Y)
  let : IsCofibrant (op Z) := op_isCofibrant Z
  let : Cofibration p.op := (cofibration_op_iff _).mpr inferInstance
  let : WeakEquivalence (𝟙 (op X)) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences Cᵒᵖ).of_isIso (𝟙 (op X)))
  let : WeakEquivalence (𝟙 (op Y)) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences Cᵒᵖ).of_isIso (𝟙 (op Y)))
  let : WeakEquivalence (((insertion d Z hZ).app Y).op) :=
    (weakEquivalences_op_iff _).mpr ((weakEquivalence_iff _).mpr (insertion_weak d Z hZ Y))
  have h : WeakEquivalence ((fiberToOppositeCofiber d Z hZ p s).op) :=
    weakEquivalence_map_of_isPushouts_of_cofibrant
      (oppositeCofiber_isPullback d Z hZ p).op.flip (IsPullback.of_isLimit hs).op.flip
      (a := 𝟙 (op Y)) (b := 𝟙 (op X)) (c := ((insertion d Z hZ).app Y).op)
      (d := (fiberToOppositeCofiber d Z hZ p s).op)
      (by simp)
      (by simpa using
        congrArg Quiver.Hom.op (insertion_projection d Z hZ Y))
      (by simpa using
        congrArg Quiver.Hom.op (fiberToOppositeCofiber_fst d Z hZ p s))
      (by simpa using
        congrArg Quiver.Hom.op (fiberToOppositeCofiber_snd d Z hZ p s))
  exact (weakEquivalences_op_iff _).mp h

end HomotopicalAlgebra.OriginalOrdinaryJPathCone
