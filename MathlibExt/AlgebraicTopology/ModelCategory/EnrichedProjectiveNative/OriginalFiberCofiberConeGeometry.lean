/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalFiberComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalISuspensionCofibrantComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHDiskMaximumGeometry

/-!
# Original fiber and cofiber geometry on enriched native diagrams

The index is an arbitrary category enriched over the actual pointed CGWH
coefficient category. Every construction uses the original native I replacement,
I cone and I suspension, at the caller's realized-generator bottom. The published
coefficient disk maximum is reused with its actual selected time-one point.
No stable model or Omega hypothesis is part of this geometry.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.DiskMaximumGeometry
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {J : Type} [EnrichedCategory PointedCGWH.{u, v} J]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} J
private abbrev H := toHomotopyCategory (Carrier (J := J))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := J)
private abbrev S := OriginalISuspension.suspension (B := B) (I := J)

variable (a : ∀ F : Arrow (Carrier (J := J)),
  PullbackCone F.hom (Diagrams.zeroTo F.right)) (ha : ∀ F, IsLimit (a F))

namespace ConeLiftGeometry

private abbrev cone := OriginalICone.cone (B := B) (I := J)
private abbrev iota := OriginalICone.inclusion (B := B) (I := J)
private abbrev Idata := HomotopicalAlgebra.EnrichedProjective.Native.cofibrantFactorizationData
  (B := B) (A := J)
private abbrev suspensionCone (A : (Carrier (J := J))) :=
  OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A
private abbrev suspensionConeIsColimit (A : (Carrier (J := J))) :=
  OriginalISuspensionCofibrantComparison.originalSuspensionCoconeIsColimit (B := B) A

private abbrev suspensionInl (A : Carrier (J := J)) : cone.obj A ⟶ S.obj A :=
  (suspensionCone A).inl
private abbrev suspensionInr (A : Carrier (J := J)) : Diagrams.zeroDiagram ⟶ S.obj A :=
  (suspensionCone A).inr

omit B in
private theorem originalPushout_hom_ext
    {C : Type u} [Category.{v} C] {A X Y T U : C} {f : A ⟶ X} {g : A ⟶ Y}
    (c : PushoutCocone f g) (hc : IsColimit c) (hpt : c.pt = T)
    (p : X ⟶ T) (q : Y ⟶ T) (hp : c.inl ≫ eqToHom hpt = p)
    (hq : c.inr ≫ eqToHom hpt = q) {a b : T ⟶ U}
    (ha : p ≫ a = p ≫ b) (hb : q ≫ a = q ≫ b) : a = b := by
  have h : eqToHom hpt ≫ a = eqToHom hpt ≫ b := by
    apply PushoutCocone.IsColimit.hom_ext hc
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) hp).trans (ha.trans
          ((congrArg (· ≫ b) hp).symm.trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ a) hq).trans (hb.trans
          ((congrArg (· ≫ b) hq).symm.trans (Category.assoc _ _ _))))
  exact (cancel_epi (eqToHom hpt)).mp h

private theorem suspension_hom_ext (A : Carrier (J := J)) {T : Carrier (J := J)}
    (f g : S.obj A ⟶ T) (hCone : suspensionInl A ≫ f = suspensionInl A ≫ g)
    (hZero : suspensionInr A ≫ f = suspensionInr A ≫ g) : f = g :=
  originalPushout_hom_ext (suspensionCone A) (suspensionConeIsColimit A) rfl
    (suspensionInl A) (suspensionInr A) (Category.comp_id _) (Category.comp_id _) hCone hZero

private theorem suspension_condition (A : Carrier (J := J)) :
    iota.app A ≫ suspensionInl A = Diagrams.toZero A ≫ suspensionInr A :=
  (suspensionCone A).condition

private theorem suspensionMap_cone {A X : Carrier (J := J)} (f : A ⟶ X) :
    suspensionInl A ≫ S.map f = cone.map f ≫ suspensionInl X :=
  OriginalISuspensionCofibrantComparison.originalSuspensionMap_cone f

private theorem suspensionMap_zero {A X : Carrier (J := J)} (f : A ⟶ X) :
    suspensionInr A ≫ S.map f = suspensionInr X :=
  OriginalISuspensionCofibrantComparison.originalSuspensionMap_zero f

private instance zeroIsCofibrant : IsCofibrant (Diagrams.zeroDiagram (A := J)) :=
  (isCofibrant_iff_of_isInitial (𝟙 Diagrams.zeroDiagram)
    Diagrams.zeroDiagram_isZero.isInitial).mpr inferInstance

/-- The actual two original cone copies are glued along their same source inclusion. -/
def doubleCone (A : (Carrier (J := J))) : (Carrier (J := J)) :=
  pushout (iota.app A) (iota.app A)

/-- The original fold keeps both cone-copy maps equal to the actual identity. -/
def coneFold (A : (Carrier (J := J))) : doubleCone A ⟶ cone.obj A :=
  pushout.desc (𝟙 _) (𝟙 _) rfl

/-- The relative cylinder is the unchanged original I middle object of the cone fold. -/
def relativeCone (A : (Carrier (J := J))) : (Carrier (J := J)) :=
  Idata.Z.obj (Arrow.mk (coneFold A))

/-- Its first endpoint is the first actual pushout leg followed by the original I first map. -/
def relativeFirst (A : (Carrier (J := J))) : cone.obj A ⟶ relativeCone A :=
  pushout.inl (iota.app A) (iota.app A) ≫ Idata.i.app (Arrow.mk (coneFold A))

/-- Its second endpoint keeps the second actual pushout leg and the same original I map. -/
def relativeSecond (A : (Carrier (J := J))) : cone.obj A ⟶ relativeCone A :=
  pushout.inr (iota.app A) (iota.app A) ≫ Idata.i.app (Arrow.mk (coneFold A))

/-- The cylinder projection is exactly the same original I second factorization map. -/
def relativeProjection (A : (Carrier (J := J))) : relativeCone A ⟶ cone.obj A :=
  Idata.p.app (Arrow.mk (coneFold A))

/-- The original source is retained as its first actual cone endpoint. -/
def relativeSource (A : (Carrier (J := J))) : A ⟶ relativeCone A :=
  iota.app A ≫ relativeFirst A

/-- Both full original cone endpoints agree on the complete original source. -/
theorem relativeSource_second (A : (Carrier (J := J))) :
    relativeSource A = iota.app A ≫ relativeSecond A := by
  let j : doubleCone A ⟶ relativeCone A := Idata.i.app (Arrow.mk (coneFold A))
  change iota.app A ≫ (pushout.inl (iota.app A) (iota.app A) ≫ j) =
    iota.app A ≫ (pushout.inr (iota.app A) (iota.app A) ≫ j)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ j) (pushout.condition (f := iota.app A) (g := iota.app A))).trans
      (Category.assoc _ _ _))

/-- The first original endpoint is a section of the exact original I projection. -/
theorem relativeFirst_projection (A : (Carrier (J := J))) :
    relativeFirst A ≫ relativeProjection A = 𝟙 (cone.obj A) := by
  let j : doubleCone A ⟶ relativeCone A := Idata.i.app (Arrow.mk (coneFold A))
  let p : relativeCone A ⟶ cone.obj A := Idata.p.app (Arrow.mk (coneFold A))
  have h : j ≫ p = coneFold A := Idata.fac_app (f := Arrow.mk (coneFold A))
  change (pushout.inl (iota.app A) (iota.app A) ≫ j) ≫ p = 𝟙 (cone.obj A)
  exact (Category.assoc _ _ _).trans
    ((congrArg (pushout.inl (iota.app A) (iota.app A) ≫ ·) h).trans
      (pushout.inl_desc _ _ _))

/-- The second original endpoint is the other section of the same projection. -/
theorem relativeSecond_projection (A : (Carrier (J := J))) :
    relativeSecond A ≫ relativeProjection A = 𝟙 (cone.obj A) := by
  let j : doubleCone A ⟶ relativeCone A := Idata.i.app (Arrow.mk (coneFold A))
  let p : relativeCone A ⟶ cone.obj A := Idata.p.app (Arrow.mk (coneFold A))
  have h : j ≫ p = coneFold A := Idata.fac_app (f := Arrow.mk (coneFold A))
  change (pushout.inr (iota.app A) (iota.app A) ≫ j) ≫ p = 𝟙 (cone.obj A)
  exact (Category.assoc _ _ _).trans
    ((congrArg (pushout.inr (iota.app A) (iota.app A) ≫ ·) h).trans
      (pushout.inr_desc _ _ _))

/-- The source projection is the same complete original cone inclusion. -/
theorem relativeSource_projection (A : (Carrier (J := J))) :
    relativeSource A ≫ relativeProjection A = iota.app A := by
  rw [relativeSource, Category.assoc, relativeFirst_projection, Category.comp_id]

private theorem originalInclusion_cofibration (A : (Carrier (J := J))) :
    Cofibration (iota.app A) :=
  (HomotopicalAlgebra.cofibration_iff _).mpr (OriginalICone.inclusion_cofibration A)

private theorem relativeFirst_cofibration (A : (Carrier (J := J))) :
    Cofibration (relativeFirst A) := by
  let j : doubleCone A ⟶ relativeCone A := Idata.i.app (Arrow.mk (coneFold A))
  have hj : cofibrations (Carrier (J := J)) j := Idata.hi _
  let _ : Cofibration (iota.app A) := originalInclusion_cofibration A
  have hIn : cofibrations (Carrier (J := J))
      (pushout.inl (iota.app A) (iota.app A)) := (cofibration_iff _).mp inferInstance
  exact (cofibration_iff _).mpr
    ((cofibrations (Carrier (J := J))).comp_mem _ _ hIn hj)

private theorem relativeSource_cofibration (A : (Carrier (J := J))) :
    Cofibration (relativeSource A) := by
  let _ : Cofibration (iota.app A) := originalInclusion_cofibration A
  let _ : Cofibration (relativeFirst A) := relativeFirst_cofibration A
  dsimp only [relativeSource]
  infer_instance

/-- The original relative I projection retains its actual trivial-fibration weakness. -/
theorem relativeProjection_weak (A : (Carrier (J := J))) :
    weakEquivalences (Carrier (J := J)) (relativeProjection A) :=
  (Idata.hp (Arrow.mk (coneFold A))).2

/-- The complete source is collapsed in the actual relative pushout. -/
def relativeSuspension (A : (Carrier (J := J))) : (Carrier (J := J)) :=
  pushout (relativeSource A) (Diagrams.toZero A)

private abbrev relativeSuspensionInl (A : Carrier (J := J)) :
    relativeCone A ⟶ relativeSuspension A := pushout.inl _ _
private abbrev relativeSuspensionInr (A : Carrier (J := J)) :
    Diagrams.zeroDiagram ⟶ relativeSuspension A := pushout.inr _ _

/-- The first cone endpoint gives the actual map from the caller's original suspension. -/
def suspensionFirst (A : (Carrier (J := J))) : S.obj A ⟶ relativeSuspension A :=
  (suspensionConeIsColimit A).desc (PushoutCocone.mk
    (relativeFirst A ≫ pushout.inl _ _) (pushout.inr _ _)
    (by rw [← Category.assoc]; exact pushout.condition))

/-- The second full cone endpoint gives the other actual suspension map. -/
def suspensionSecond (A : (Carrier (J := J))) : S.obj A ⟶ relativeSuspension A :=
  (suspensionConeIsColimit A).desc (PushoutCocone.mk
    (relativeSecond A ≫ pushout.inl _ _) (pushout.inr _ _)
    (by rw [← Category.assoc, ← relativeSource_second]; exact pushout.condition))

/-- The exact original I projection descends through the original suspension cocone. -/
def suspensionProjection (A : (Carrier (J := J))) : relativeSuspension A ⟶ S.obj A :=
  pushout.desc (relativeProjection A ≫ suspensionInl A) (suspensionInr A)
    (by rw [← Category.assoc, relativeSource_projection]; exact suspension_condition A)

theorem suspensionFirst_cone (A : (Carrier (J := J))) :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫
      suspensionFirst A = relativeFirst A ≫ pushout.inl _ _ :=
  (suspensionConeIsColimit A).fac _ WalkingSpan.left

theorem suspensionFirst_zero (A : (Carrier (J := J))) :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inr ≫
      suspensionFirst A = pushout.inr _ _ :=
  (suspensionConeIsColimit A).fac _ WalkingSpan.right

theorem suspensionSecond_cone (A : (Carrier (J := J))) :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫
      suspensionSecond A = relativeSecond A ≫ pushout.inl _ _ :=
  (suspensionConeIsColimit A).fac _ WalkingSpan.left

theorem suspensionSecond_zero (A : (Carrier (J := J))) :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inr ≫
      suspensionSecond A = pushout.inr _ _ :=
  (suspensionConeIsColimit A).fac _ WalkingSpan.right

private theorem suspensionFirst_typed_cone (A : Carrier (J := J)) :
    suspensionInl A ≫ suspensionFirst A = relativeFirst A ≫ relativeSuspensionInl A :=
  suspensionFirst_cone A
private theorem suspensionFirst_typed_zero (A : Carrier (J := J)) :
    suspensionInr A ≫ suspensionFirst A = relativeSuspensionInr A := suspensionFirst_zero A
private theorem suspensionSecond_typed_cone (A : Carrier (J := J)) :
    suspensionInl A ≫ suspensionSecond A = relativeSecond A ≫ relativeSuspensionInl A :=
  suspensionSecond_cone A
private theorem suspensionSecond_typed_zero (A : Carrier (J := J)) :
    suspensionInr A ≫ suspensionSecond A = relativeSuspensionInr A := suspensionSecond_zero A

private theorem suspensionProjection_inl (A : Carrier (J := J)) :
    relativeSuspensionInl A ≫ suspensionProjection A =
      relativeProjection A ≫ suspensionInl A := pushout.inl_desc _ _ _
private theorem suspensionProjection_inr (A : Carrier (J := J)) :
    relativeSuspensionInr A ≫ suspensionProjection A = suspensionInr A :=
  pushout.inr_desc _ _ _

/-- The first full suspension endpoint is a section of its actual original projection. -/
theorem suspensionFirst_projection (A : (Carrier (J := J))) :
    suspensionFirst A ≫ suspensionProjection A = 𝟙 (S.obj A) := by
  apply suspension_hom_ext A
  · let l : relativeCone A ⟶ relativeSuspension A := relativeSuspensionInl A
    have h : suspensionInl A ≫ suspensionFirst A = relativeFirst A ≫ l :=
      suspensionFirst_typed_cone A
    have hp : l ≫ suspensionProjection A = relativeProjection A ≫ suspensionInl A :=
      suspensionProjection_inl A
    calc
      _ = (suspensionInl A ≫ suspensionFirst A) ≫ suspensionProjection A :=
        (Category.assoc _ _ _).symm
      _ = (relativeFirst A ≫ l) ≫ suspensionProjection A := congrArg (· ≫ suspensionProjection A) h
      _ = relativeFirst A ≫ (relativeProjection A ≫ suspensionInl A) :=
        (Category.assoc _ _ _).trans (congrArg (relativeFirst A ≫ ·) hp)
      _ = suspensionInl A := (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ suspensionInl A) (relativeFirst_projection A)).trans (Category.id_comp _))
      _ = _ := (Category.comp_id _).symm
  · let r : Diagrams.zeroDiagram ⟶ relativeSuspension A := relativeSuspensionInr A
    have h : suspensionInr A ≫ suspensionFirst A = r := suspensionFirst_typed_zero A
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ suspensionProjection A) h).trans
        ((suspensionProjection_inr A).trans (Category.comp_id _).symm))

/-- The second full suspension endpoint is the other section of the unchanged projection. -/
theorem suspensionSecond_projection (A : (Carrier (J := J))) :
    suspensionSecond A ≫ suspensionProjection A = 𝟙 (S.obj A) := by
  apply suspension_hom_ext A
  · let l : relativeCone A ⟶ relativeSuspension A := relativeSuspensionInl A
    have h : suspensionInl A ≫ suspensionSecond A = relativeSecond A ≫ l :=
      suspensionSecond_typed_cone A
    have hp : l ≫ suspensionProjection A = relativeProjection A ≫ suspensionInl A :=
      suspensionProjection_inl A
    calc
      _ = (suspensionInl A ≫ suspensionSecond A) ≫ suspensionProjection A :=
        (Category.assoc _ _ _).symm
      _ = (relativeSecond A ≫ l) ≫ suspensionProjection A := congrArg (· ≫ suspensionProjection A) h
      _ = relativeSecond A ≫ (relativeProjection A ≫ suspensionInl A) :=
        (Category.assoc _ _ _).trans (congrArg (relativeSecond A ≫ ·) hp)
      _ = suspensionInl A := (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ suspensionInl A) (relativeSecond_projection A)).trans (Category.id_comp _))
      _ = _ := (Category.comp_id _).symm
  · let r : Diagrams.zeroDiagram ⟶ relativeSuspension A := relativeSuspensionInr A
    have h : suspensionInr A ≫ suspensionSecond A = r := suspensionSecond_typed_zero A
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ suspensionProjection A) h).trans
        ((suspensionProjection_inr A).trans (Category.comp_id _).symm))

/-- Cofibrant gluing proves weakness of the same actual suspension projection. -/
theorem suspensionProjection_weak (A : (Carrier (J := J))) [IsCofibrant A] :
    weakEquivalences (Carrier (J := J)) (suspensionProjection A) := by
  let _ : Cofibration (relativeSource A) := relativeSource_cofibration A
  let _ : Cofibration (iota.app A) := originalInclusion_cofibration A
  let _ : WeakEquivalence (relativeProjection A) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (relativeProjection_weak A)
  apply (HomotopicalAlgebra.weakEquivalence_iff _).mp
  exact weakEquivalence_map_of_isPushouts_of_cofibrant
    (A := A) (A' := A) (X := Diagrams.zeroDiagram) (X' := Diagrams.zeroDiagram)
    (IsPushout.of_hasPushout (relativeSource A) (Diagrams.toZero A))
    (IsPushout.of_isColimit (suspensionConeIsColimit A))
    (a := 𝟙 A) (b := relativeProjection A) (c := 𝟙 Diagrams.zeroDiagram)
    ((relativeSource_projection A).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (pushout.inl_desc _ _ _)
    ((pushout.inr_desc _ _ _).trans (Category.id_comp _).symm)

/-- The native original I fold and source pushout give a genuine suspension cylinder. -/
def originalSuspensionCylinder (A : (Carrier (J := J))) [IsCofibrant A] : Cylinder (S.obj A) where
  I := relativeSuspension A
  i₀ := suspensionFirst A
  i₁ := suspensionSecond A
  π := suspensionProjection A
  i₀_π := suspensionFirst_projection A
  i₁_π := suspensionSecond_projection A
  weakEquivalence_π := (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    (suspensionProjection_weak A)

/-- A map on the complete original cone descends through the actual original suspension. -/
def suspensionDesc (A T : (Carrier (J := J))) (f : cone.obj A ⟶ T)
    (hf : iota.app A ≫ f = Diagrams.toZero A ≫ Diagrams.zeroTo T) : S.obj A ⟶ T :=
  (suspensionConeIsColimit A).desc (PushoutCocone.mk f (Diagrams.zeroTo T) hf)

/-- The descent retains its same actual cone coefficient. -/
theorem suspensionDesc_cone (A T : (Carrier (J := J))) (f : cone.obj A ⟶ T)
    (hf : iota.app A ≫ f = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫
      suspensionDesc A T f hf = f :=
  (suspensionConeIsColimit A).fac _ WalkingSpan.left

/-- Its zero endpoint is the unchanged original native zero map. -/
theorem suspensionDesc_zero (A T : (Carrier (J := J))) (f : cone.obj A ⟶ T)
    (hf : iota.app A ≫ f = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inr ≫
      suspensionDesc A T f hf = Diagrams.zeroTo T :=
  (suspensionConeIsColimit A).fac _ WalkingSpan.right

private theorem suspensionDesc_typed_cone (A T : Carrier (J := J)) (f : cone.obj A ⟶ T)
    (hf : iota.app A ≫ f = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    suspensionInl A ≫ suspensionDesc A T f hf = f := suspensionDesc_cone A T f hf
private theorem suspensionDesc_typed_zero (A T : Carrier (J := J)) (f : cone.obj A ⟶ T)
    (hf : iota.app A ≫ f = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    suspensionInr A ≫ suspensionDesc A T f hf = Diagrams.zeroTo T := suspensionDesc_zero A T f hf

/-- Two complete cone maps agreeing on the original source form one actual pushout map. -/
def twoConeMap {A X : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) : doubleCone A ⟶ cone.obj X :=
  pushout.desc f g hfg

/-- The original I first map lifts against the actual original cone contraction. -/
theorem relativeConeLiftSquare {A X : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) :
    CommSq (twoConeMap f g hfg) (Idata.i.app (Arrow.mk (coneFold A)))
      ((OriginalICone.contraction (B := B)).app X) (Diagrams.toZero (relativeCone A)) :=
  ⟨Diagrams.zeroDiagramIsTerminal.hom_ext _ _⟩

private instance relativeConeLiftSquare_hasLift {A X : (Carrier (J := J))}
    (f g : cone.obj A ⟶ cone.obj X) (hfg : iota.app A ≫ f = iota.app A ≫ g) :
    (relativeConeLiftSquare f g hfg).HasLift := by
  have hi : cofibrations (Carrier (J := J)) (Idata.i.app (Arrow.mk (coneFold A))) := Idata.hi _
  have hp : trivialFibrations (Carrier (J := J))
      ((OriginalICone.contraction (B := B)).app X) := OriginalICone.contraction_trivialFibration X
  exact (MorphismProperty.hasLiftingProperty_of_wfs
    (Idata.i.app (Arrow.mk (coneFold A))) ((OriginalICone.contraction (B := B)).app X)
    hi hp).sq_hasLift _

/-- CM4 supplies the complete relative cone lift from the literal original I data. -/
def relativeConeLift {A X : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) : relativeCone A ⟶ cone.obj X :=
  (relativeConeLiftSquare f g hfg).lift

/-- The first cone coefficient is preserved by the actual relative lift. -/
theorem relativeConeLift_first {A X : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) :
    relativeFirst A ≫ relativeConeLift f g hfg = f := by
  let j : doubleCone A ⟶ relativeCone A := Idata.i.app (Arrow.mk (coneFold A))
  let h : relativeCone A ⟶ cone.obj X := (relativeConeLiftSquare f g hfg).lift
  have hj : j ≫ h = twoConeMap f g hfg := (relativeConeLiftSquare f g hfg).fac_left
  change (pushout.inl (iota.app A) (iota.app A) ≫ j) ≫ h = f
  exact (Category.assoc _ _ _).trans
    ((congrArg (pushout.inl (iota.app A) (iota.app A) ≫ ·) hj).trans
      (pushout.inl_desc _ _ _))

/-- The second cone coefficient is preserved by the same lift. -/
theorem relativeConeLift_second {A X : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) :
    relativeSecond A ≫ relativeConeLift f g hfg = g := by
  let j : doubleCone A ⟶ relativeCone A := Idata.i.app (Arrow.mk (coneFold A))
  let h : relativeCone A ⟶ cone.obj X := (relativeConeLiftSquare f g hfg).lift
  have hj : j ≫ h = twoConeMap f g hfg := (relativeConeLiftSquare f g hfg).fac_left
  change (pushout.inr (iota.app A) (iota.app A) ≫ j) ≫ h = g
  exact (Category.assoc _ _ _).trans
    ((congrArg (pushout.inr (iota.app A) (iota.app A) ≫ ·) hj).trans
      (pushout.inr_desc _ _ _))

/-- The unchanged source is carried to the same complete first cone coefficient. -/
theorem relativeConeLift_source {A X : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) :
    relativeSource A ≫ relativeConeLift f g hfg = iota.app A ≫ f := by
  rw [relativeSource, Category.assoc, relativeConeLift_first]

/-- The actual relative lift descends after the complete common source becomes zero. -/
def relativeLiftDesc {A X T : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    relativeSuspension A ⟶ T :=
  pushout.desc (relativeConeLift f g hfg ≫ t) (Diagrams.zeroTo T)
    (by rw [← Category.assoc, relativeConeLift_source, Category.assoc]; exact hft)

private theorem relativeLiftDesc_inl {A X T : Carrier (J := J)}
    (f g : cone.obj A ⟶ cone.obj X) (hfg : iota.app A ≫ f = iota.app A ≫ g)
    (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    relativeSuspensionInl A ≫ relativeLiftDesc f g hfg t hft =
      relativeConeLift f g hfg ≫ t := pushout.inl_desc _ _ _
private theorem relativeLiftDesc_inr {A X T : Carrier (J := J)}
    (f g : cone.obj A ⟶ cone.obj X) (hfg : iota.app A ≫ f = iota.app A ≫ g)
    (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    relativeSuspensionInr A ≫ relativeLiftDesc f g hfg t hft = Diagrams.zeroTo T :=
  pushout.inr_desc _ _ _

/-- Its first suspension endpoint is the same descended first cone map. -/
theorem relativeLiftDesc_first {A X T : (Carrier (J := J))} (f g : cone.obj A ⟶ cone.obj X)
    (hfg : iota.app A ≫ f = iota.app A ≫ g) (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    suspensionFirst A ≫ relativeLiftDesc f g hfg t hft =
      suspensionDesc A T (f ≫ t) hft := by
  apply suspension_hom_ext A
  · let l : relativeCone A ⟶ relativeSuspension A := relativeSuspensionInl A
    have h : suspensionInl A ≫ suspensionFirst A = relativeFirst A ≫ l :=
      suspensionFirst_typed_cone A
    calc
      _ = (suspensionInl A ≫ suspensionFirst A) ≫ relativeLiftDesc f g hfg t hft :=
        (Category.assoc _ _ _).symm
      _ = (relativeFirst A ≫ l) ≫ relativeLiftDesc f g hfg t hft := congrArg (· ≫ _) h
      _ = relativeFirst A ≫ (relativeConeLift f g hfg ≫ t) :=
        (Category.assoc _ _ _).trans (congrArg (relativeFirst A ≫ ·)
          (relativeLiftDesc_inl f g hfg t hft))
      _ = f ≫ t := (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ t) (relativeConeLift_first f g hfg))
      _ = _ := (suspensionDesc_typed_cone A T (f ≫ t) hft).symm
  · let r : Diagrams.zeroDiagram ⟶ relativeSuspension A := relativeSuspensionInr A
    have h : suspensionInr A ≫ suspensionFirst A = r := suspensionFirst_typed_zero A
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ relativeLiftDesc f g hfg t hft) h).trans
        ((relativeLiftDesc_inr f g hfg t hft).trans
          (suspensionDesc_typed_zero A T (f ≫ t) hft).symm))

/-- Its second suspension endpoint retains the whole second cone map. -/
theorem relativeLiftDesc_second {A X T : (Carrier (J := J))}
    (f g : cone.obj A ⟶ cone.obj X) (hfg : iota.app A ≫ f = iota.app A ≫ g)
    (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T)
    (hgt : iota.app A ≫ g ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    suspensionSecond A ≫ relativeLiftDesc f g hfg t hft =
      suspensionDesc A T (g ≫ t) hgt := by
  apply suspension_hom_ext A
  · let l : relativeCone A ⟶ relativeSuspension A := relativeSuspensionInl A
    have h : suspensionInl A ≫ suspensionSecond A = relativeSecond A ≫ l :=
      suspensionSecond_typed_cone A
    calc
      _ = (suspensionInl A ≫ suspensionSecond A) ≫ relativeLiftDesc f g hfg t hft :=
        (Category.assoc _ _ _).symm
      _ = (relativeSecond A ≫ l) ≫ relativeLiftDesc f g hfg t hft := congrArg (· ≫ _) h
      _ = relativeSecond A ≫ (relativeConeLift f g hfg ≫ t) :=
        (Category.assoc _ _ _).trans (congrArg (relativeSecond A ≫ ·)
          (relativeLiftDesc_inl f g hfg t hft))
      _ = g ≫ t := (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ t) (relativeConeLift_second f g hfg))
      _ = _ := (suspensionDesc_typed_cone A T (g ≫ t) hgt).symm
  · let r : Diagrams.zeroDiagram ⟶ relativeSuspension A := relativeSuspensionInr A
    have h : suspensionInr A ≫ suspensionSecond A = r := suspensionSecond_typed_zero A
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ relativeLiftDesc f g hfg t hft) h).trans
        ((relativeLiftDesc_inr f g hfg t hft).trans
          (suspensionDesc_typed_zero A T (g ≫ t) hgt).symm))

/-- The original I lift gives a genuine complete homotopy of the two original descents. -/
def twoConeDescLeftHomotopy {A X T : (Carrier (J := J))} [IsCofibrant A]
    (f g : cone.obj A ⟶ cone.obj X) (hfg : iota.app A ≫ f = iota.app A ≫ g)
    (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T)
    (hgt : iota.app A ≫ g ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    (originalSuspensionCylinder A).LeftHomotopy
      (suspensionDesc A T (f ≫ t) hft) (suspensionDesc A T (g ≫ t) hgt) where
  h := relativeLiftDesc f g hfg t hft
  h₀ := relativeLiftDesc_first f g hfg t hft
  h₁ := relativeLiftDesc_second f g hfg t hft hgt

/-- Equality in original level Ho is proved from the actual original relative cone lift. -/
theorem twoConeDesc_ho {A X T : (Carrier (J := J))} [IsCofibrant A]
    (f g : cone.obj A ⟶ cone.obj X) (hfg : iota.app A ≫ f = iota.app A ≫ g)
    (t : cone.obj X ⟶ T)
    (hft : iota.app A ≫ f ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T)
    (hgt : iota.app A ≫ g ≫ t = Diagrams.toZero A ≫ Diagrams.zeroTo T) :
    H.map (suspensionDesc A T (f ≫ t) hft) =
      H.map (suspensionDesc A T (g ≫ t) hgt) :=
  (LeftHomotopyRel.factorsThroughLocalization (Carrier (J := J))
    (twoConeDescLeftHomotopy f g hfg t hft hgt).leftHomotopyRel).map_eq H

private instance zeroToCone_cofibration (A : (Carrier (J := J))) [IsCofibrant A] :
    Cofibration (Diagrams.zeroTo (cone.obj A)) := by
  let _ : IsCofibrant (cone.obj A) := OriginalICone.cone_isCofibrant A
  exact (isCofibrant_iff_of_isInitial _ Diagrams.zeroDiagram_isZero.isInitial).mp
    inferInstance

private instance zeroToCone_weak (A : (Carrier (J := J))) :
    WeakEquivalence (Diagrams.zeroTo (cone.obj A)) := by
  let _ : WeakEquivalence ((OriginalICone.contraction (B := B)).app A) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (OriginalICone.contraction_trivialFibration A).2
  have h : Diagrams.zeroTo (cone.obj A) ≫
      (OriginalICone.contraction (B := B)).app A = 𝟙 Diagrams.zeroDiagram :=
    Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  exact weakEquivalence_of_postcomp_of_fac h

/-- A complete original suspension coefficient gives its actual zero-based fibration square. -/
theorem coneCoefficientLiftSquare (F : Arrow (Carrier (J := J))) (A : (Carrier (J := J)))
    (f : S.obj A ⟶ F.right) :
    CommSq (Diagrams.zeroTo F.left) (Diagrams.zeroTo (cone.obj A)) F.hom
      ((OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫ f) :=
  ⟨Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _⟩

private instance coneCoefficientLiftSquare_hasLift (F : Arrow (Carrier (J := J)))
    [Fibration F.hom] (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    (coneCoefficientLiftSquare F A f).HasLift := by
  infer_instance

/-- The original Serre fibration supplies a lift of the complete cone coefficient. -/
def coneCoefficientLift (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) : cone.obj A ⟶ F.left :=
  (coneCoefficientLiftSquare F A f).lift

/-- Its projection is exactly the same whole original suspension coefficient. -/
theorem coneCoefficientLift_over (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    coneCoefficientLift F A f ≫ F.hom =
      (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫ f :=
  (coneCoefficientLiftSquare F A f).fac_right

private theorem coneCoefficientLift_typed_over (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : Carrier (J := J)) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    coneCoefficientLift F A f ≫ F.hom = suspensionInl A ≫ f := coneCoefficientLift_over F A f


/-- The actual original source restriction lands over the unchanged zero endpoint. -/
theorem coneCoefficientLift_source_zero (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    (iota.app A ≫ coneCoefficientLift F A f) ≫ F.hom =
      Diagrams.toZero A ≫ Diagrams.zeroTo F.right := by
  rw [Category.assoc, coneCoefficientLift_typed_over, ← Category.assoc,
    suspension_condition A, Category.assoc]
  exact congrArg (Diagrams.toZero A ≫ ·)
    (Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _)


/-- Both actual projection maps construct the caller's chosen original fiber coefficient. -/
def coneCoefficientFiberMap (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) : A ⟶ (a F).pt :=
  (ha F).lift (PullbackCone.mk (iota.app A ≫ coneCoefficientLift F A f)
    (Diagrams.toZero A) (coneCoefficientLift_source_zero F A f))

/-- Its first original projection is the entire same lifted cone restriction. -/
theorem coneCoefficientFiberMap_fst (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    coneCoefficientFiberMap a ha F A f ≫ (a F).fst =
      iota.app A ≫ coneCoefficientLift F A f :=
  (ha F).fac _ WalkingCospan.left

/-- Its second original projection retains the caller's original native zero. -/
theorem coneCoefficientFiberMap_snd (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    coneCoefficientFiberMap a ha F A f ≫ (a F).snd = Diagrams.toZero A :=
  (ha F).fac _ WalkingCospan.right

/-- The actual Q counit is lifted over the complete original fiber coefficient. -/
theorem coneCoefficientQSquare (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    CommSq (Diagrams.zeroTo (Q.obj (a F).pt)) (Diagrams.zeroTo A)
      (Replacement.cofibrantReplacementCounit.app (a F).pt)
      (coneCoefficientFiberMap a ha F A f) :=
  ⟨Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _⟩

private instance coneCoefficientQSquare_hasLift (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    (coneCoefficientQSquare a ha F A f).HasLift := by
  let _ : Cofibration (Diagrams.zeroTo A) :=
    (isCofibrant_iff_of_isInitial _ Diagrams.zeroDiagram_isZero.isInitial).mp inferInstance
  let _ : Fibration (Replacement.cofibrantReplacementCounit.app (a F).pt) :=
    (HomotopicalAlgebra.fibration_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (a F).pt).1
  let _ : WeakEquivalence (Replacement.cofibrantReplacementCounit.app (a F).pt) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (Replacement.cofibrantReplacementCounit_mem_trivialFibrations (a F).pt).2
  infer_instance

/-- The literal Q counit lift constructs a coefficient in the original Q chosen fiber. -/
def coneCoefficientQFiberMap (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) : A ⟶ Q.obj (a F).pt :=
  (coneCoefficientQSquare a ha F A f).lift

/-- The complete actual counit recovers the same constructed original fiber coefficient. -/
theorem coneCoefficientQFiberMap_counit (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    coneCoefficientQFiberMap a ha F A f ≫
        Replacement.cofibrantReplacementCounit.app (a F).pt =
      coneCoefficientFiberMap a ha F A f :=
  (coneCoefficientQSquare a ha F A f).fac_right

/-- Counit followed by the first original fiber projection retains the same cone restriction. -/
theorem coneCoefficientQFiberMap_counit_fst (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    coneCoefficientQFiberMap a ha F A f ≫
        Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst =
      iota.app A ≫ coneCoefficientLift F A f := by
  rw [← Category.assoc, coneCoefficientQFiberMap_counit, coneCoefficientFiberMap_fst]

private abbrev originalCofiberCone (F : Arrow (Carrier (J := J))) :=
  OriginalISuspension.cocone (B := B) F
private abbrev originalCofiberConeIsColimit (F : Arrow (Carrier (J := J))) :=
  OriginalISuspension.coconeIsColimit (B := B) F

/-- The literal original Q-fiber null square gives its full original suspension map. -/
def rawQFiberComparison (F : Arrow (Carrier (J := J))) :
    S.obj (Q.obj (a F).pt) ⟶ (originalCofiberCone F).pt :=
  OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.QFiberSuspensionToCofiber
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a Q
    Replacement.cofibrantReplacementCounit cone iota
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B)) F

/-- The complete original cone leg preserves Q's actual counit and first fiber projection. -/
theorem rawQFiberComparison_cone (F : Arrow (Carrier (J := J))) :
    (suspensionCone (Q.obj (a F).pt)).inl ≫ rawQFiberComparison a F =
      cone.map (Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst) ≫
        (originalCofiberCone F).inl :=
  OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.QFiberSuspensionToCofiber_cone
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a Q
    Replacement.cofibrantReplacementCounit cone iota
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B)) F

/-- Its zero leg retains the full unchanged original target inclusion. -/
theorem rawQFiberComparison_zero (F : Arrow (Carrier (J := J))) :
    (suspensionCone (Q.obj (a F).pt)).inr ≫ rawQFiberComparison a F =
      Diagrams.zeroTo F.right ≫ (originalCofiberCone F).inr :=
  OrdinaryHoChosenFiberCofiberComparison.ArrowResolution.QFiberSuspensionToCofiber_zero
    Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero a Q
    Replacement.cofibrantReplacementCounit cone iota
    (OriginalISuspension.cocone (B := B)) (OriginalISuspension.coconeIsColimit (B := B)) F

/-- The actual Q coefficient and the actual fibration lift agree on the complete source. -/
theorem coneCoefficient_twoConeAgreement (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    iota.app A ≫ cone.map (coneCoefficientQFiberMap a ha F A f ≫
        Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst) =
      iota.app A ≫ (coneCoefficientLift F A f ≫ iota.app F.left) := by
  calc
    _ = (coneCoefficientQFiberMap a ha F A f ≫
        Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst) ≫
          iota.app F.left := (iota.naturality _).symm
    _ = (iota.app A ≫ coneCoefficientLift F A f) ≫ iota.app F.left := by
      rw [coneCoefficientQFiberMap_counit_fst]
    _ = _ := Category.assoc _ _ _

/-- The complete lifted cone coefficient becomes zero on the original collapsed source. -/
theorem coneCoefficient_liftDesc_zero (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    iota.app A ≫ (coneCoefficientLift F A f ≫ iota.app F.left) ≫
        (originalCofiberCone F).inl =
      Diagrams.toZero A ≫ Diagrams.zeroTo (originalCofiberCone F).pt := by
  calc
    _ = ((iota.app A ≫ coneCoefficientLift F A f) ≫ F.hom) ≫
        (originalCofiberCone F).inr := by
      rw [Category.assoc, Category.assoc, (originalCofiberCone F).condition]
      simp only [Category.assoc]
    _ = (Diagrams.toZero A ≫ Diagrams.zeroTo F.right) ≫
        (originalCofiberCone F).inr := by rw [coneCoefficientLift_source_zero]
    _ = _ := by
      rw [Category.assoc]
      exact congrArg (Diagrams.toZero A ≫ ·)
        (Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _)

/-- The original Q-fiber cone coefficient has the same complete zero source. -/
theorem coneCoefficient_qDesc_zero (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    iota.app A ≫ cone.map (coneCoefficientQFiberMap a ha F A f ≫
        Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst) ≫
          (originalCofiberCone F).inl =
      Diagrams.toZero A ≫ Diagrams.zeroTo (originalCofiberCone F).pt := by
  rw [← Category.assoc, coneCoefficient_twoConeAgreement, Category.assoc]
  exact coneCoefficient_liftDesc_zero F A f

private theorem rawQFiberComparison_typed_cone (F : Arrow (Carrier (J := J))) :
    suspensionInl (Q.obj (a F).pt) ≫ rawQFiberComparison a F =
      cone.map (Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst) ≫
        (originalCofiberCone F).inl := rawQFiberComparison_cone a F
private theorem rawQFiberComparison_typed_zero (F : Arrow (Carrier (J := J))) :
    suspensionInr (Q.obj (a F).pt) ≫ rawQFiberComparison a F =
      Diagrams.zeroTo F.right ≫ (originalCofiberCone F).inr := rawQFiberComparison_zero a F

/-- The original suspended Q-fiber word is the exact descent of its actual cone coefficient. -/
theorem coneCoefficient_qDesc (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    S.map (coneCoefficientQFiberMap a ha F A f) ≫ rawQFiberComparison a F =
      suspensionDesc A (originalCofiberCone F).pt
        (cone.map (coneCoefficientQFiberMap a ha F A f ≫
          Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst) ≫
            (originalCofiberCone F).inl) (coneCoefficient_qDesc_zero a ha F A f) := by
  apply suspension_hom_ext A
  · rw [← Category.assoc, suspensionMap_cone,
      Category.assoc, rawQFiberComparison_typed_cone, ← Category.assoc, ← cone.map_comp,
      suspensionDesc_typed_cone]
  · rw [← Category.assoc, suspensionMap_zero,
      rawQFiberComparison_typed_zero, suspensionDesc_typed_zero]
    exact Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _

/-- The full original target inclusion is the descent of the same actual fibration lift. -/
theorem coneCoefficient_targetDesc (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    f ≫ (originalCofiberCone F).inr =
      suspensionDesc A (originalCofiberCone F).pt
        ((coneCoefficientLift F A f ≫ iota.app F.left) ≫ (originalCofiberCone F).inl)
        (coneCoefficient_liftDesc_zero F A f) := by
  apply suspension_hom_ext A
  · rw [suspensionDesc_typed_cone, Category.assoc, (originalCofiberCone F).condition,
      ← Category.assoc]
    simpa only [Category.assoc] using congrArg (fun k => k ≫ (originalCofiberCone F).inr)
      (coneCoefficientLift_typed_over F A f).symm
  · rw [suspensionDesc_typed_zero]
    exact Diagrams.zeroDiagram_isZero.isInitial.hom_ext _ _

/-- The original cone and counit lifts prove the actual coefficient comparison in level Ho. -/
theorem coneCoefficient_comparison_ho (F : Arrow (Carrier (J := J))) [Fibration F.hom]
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right) :
    H.map (S.map (coneCoefficientQFiberMap a ha F A f)) ≫ H.map (rawQFiberComparison a F) =
      H.map f ≫ H.map (originalCofiberCone F).inr := by
  rw [← H.map_comp, coneCoefficient_qDesc, ← H.map_comp, coneCoefficient_targetDesc]
  exact twoConeDesc_ho _ _ (coneCoefficient_twoConeAgreement a ha F A f)
    (originalCofiberCone F).inl (coneCoefficient_qDesc_zero a ha F A f)
    (coneCoefficient_liftDesc_zero F A f)

/-- The two-cone homotopy applies to the specific geometric lift and Q coefficient.
Only their genuine over-base and source/projection equations are inputs. -/
theorem coneCoefficient_comparison_ho_of_lift (F : Arrow (Carrier (J := J)))
    (A : (Carrier (J := J))) [IsCofibrant A] (f : S.obj A ⟶ F.right)
    (g : cone.obj A ⟶ F.left)
    (hg : g ≫ F.hom = (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫
      f)
    (d : A ⟶ Q.obj (a F).pt)
    (hd : d ≫ Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst =
      iota.app A ≫ g) :
    H.map (S.map d) ≫ H.map (rawQFiberComparison a F) =
      H.map f ≫ H.map (originalCofiberCone F).inr := by
  have hgTyped : g ≫ F.hom = suspensionInl A ≫ f := hg
  let k := d ≫ Replacement.cofibrantReplacementCounit.app (a F).pt ≫ (a F).fst
  have hfg : iota.app A ≫ cone.map k = iota.app A ≫ (g ≫ iota.app F.left) := by
    calc
      _ = k ≫ iota.app F.left := (iota.naturality k).symm
      _ = (iota.app A ≫ g) ≫ iota.app F.left := by dsimp only [k]; rw [hd]
      _ = _ := Category.assoc _ _ _
  have hgt : iota.app A ≫ (g ≫ iota.app F.left) ≫ (originalCofiberCone F).inl =
      Diagrams.toZero A ≫ Diagrams.zeroTo (originalCofiberCone F).pt := by
    calc
      _ = iota.app A ≫ (g ≫ F.hom) ≫ (originalCofiberCone F).inr := by
        simp only [Category.assoc]
        rw [(originalCofiberCone F).condition]
      _ = ((iota.app A ≫ suspensionInl A) ≫ f) ≫
          (originalCofiberCone F).inr := by rw [hgTyped]; simp only [Category.assoc]
      _ = (Diagrams.toZero A ≫ suspensionInr A) ≫ f ≫
          (originalCofiberCone F).inr := by
        rw [suspension_condition A]
        simp only [Category.assoc]
      _ = _ := by
        simp only [Category.assoc]
        exact congrArg (Diagrams.toZero A ≫ ·)
          (Diagrams.zeroDiagramIsInitial.hom_ext _ _)
  have hft : iota.app A ≫ cone.map k ≫ (originalCofiberCone F).inl =
      Diagrams.toZero A ≫ Diagrams.zeroTo (originalCofiberCone F).pt := by
    rw [← Category.assoc, hfg, Category.assoc]
    exact hgt
  have hQ : S.map d ≫ rawQFiberComparison a F =
      suspensionDesc A (originalCofiberCone F).pt
        (cone.map k ≫ (originalCofiberCone F).inl) hft := by
    apply suspension_hom_ext A
    · rw [← Category.assoc,
        suspensionMap_cone,
        Category.assoc, rawQFiberComparison_typed_cone, ← Category.assoc, ← cone.map_comp,
        suspensionDesc_typed_cone]
    · rw [← Category.assoc,
        suspensionMap_zero,
        rawQFiberComparison_typed_zero, suspensionDesc_typed_zero]
      exact Diagrams.zeroDiagramIsInitial.hom_ext _ _
  have hTarget : f ≫ (originalCofiberCone F).inr =
      suspensionDesc A (originalCofiberCone F).pt
        ((g ≫ iota.app F.left) ≫ (originalCofiberCone F).inl) hgt := by
    apply suspension_hom_ext A
    · rw [suspensionDesc_typed_cone, Category.assoc, (originalCofiberCone F).condition,
        ← Category.assoc]
      simpa only [Category.assoc] using
        congrArg (· ≫ (originalCofiberCone F).inr) hgTyped.symm
    · rw [suspensionDesc_typed_zero]
      exact Diagrams.zeroDiagramIsInitial.hom_ext _ _
  rw [← H.map_comp, hQ, ← H.map_comp, hTarget]
  exact twoConeDesc_ho (cone.map k) (g ≫ iota.app F.left) hfg
    (originalCofiberCone F).inl hft hgt

private abbrev T := EnrichedFunctorCat.tensorLeft (A := J) PointedCGWH.sphereOne
private abbrev disk := EnrichedFunctorCat.tensorLeft (A := J) PointedCGWH.diskOne

/-- The scalar disk boundary keeps the complete original source-unit isomorphism. -/
def scalarBoundary (A : (Carrier (J := J))) : A ⟶ disk.obj A :=
  (ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A ≫
    EnrichedFunctorCat.scalarTensorMap PointedCGWH.diskBoundary A

/-- The actual scalar disk contraction receives the unchanged original I cone inclusion. -/
theorem coneToScalarDiskSquare (A : (Carrier (J := J))) :
    CommSq (scalarBoundary A) (iota.app A) (Diagrams.toZero (disk.obj A))
      (Diagrams.toZero (cone.obj A)) :=
  ⟨Diagrams.zeroDiagramIsTerminal.hom_ext _ _⟩

private instance coneToScalarDiskSquare_hasLift (A : (Carrier (J := J))) [IsCofibrant A] :
    (coneToScalarDiskSquare A).HasLift := by
  let _ : Cofibration (iota.app A) := originalInclusion_cofibration A
  let _ : Fibration (Diagrams.toZero (disk.obj A)) :=
    (isFibrant_iff_of_isTerminal _ Diagrams.zeroDiagram_isZero.isTerminal).mp
      (HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant _)
  let _ : WeakEquivalence (Diagrams.toZero (disk.obj A)) :=
    ScalarSphereSuspension.diskCollapse_weak A
  infer_instance

/-- CM4 constructs an actual map from the unchanged I cone to the actual scalar disk. -/
def coneToScalarDisk (A : (Carrier (J := J))) [IsCofibrant A] : cone.obj A ⟶ disk.obj A :=
  (coneToScalarDiskSquare A).lift

/-- This lift preserves the entire original scalar boundary-source word. -/
theorem coneToScalarDisk_source (A : (Carrier (J := J))) [IsCofibrant A] :
    iota.app A ≫ coneToScalarDisk A = scalarBoundary A :=
  (coneToScalarDiskSquare A).fac_left

/-- The original cone and scalar disk spans retain their actual complete common source. -/
def coneToScalarSpan (A : (Carrier (J := J))) [IsCofibrant A] :
    (OriginalISuspension.coneSpan (B := B) (I := J)).obj A ⟶
      (ScalarSphereSuspension.diskSpan (I := J)).obj A :=
  spanHomMk ((ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A)
    (coneToScalarDisk A) (𝟙 Diagrams.zeroDiagram) (coneToScalarDisk_source A)
    (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)

/-- Both unchanged cone collapses commute through the exact original scalar source-unit map. -/
theorem coneToScalarSpan_collapse (A : (Carrier (J := J))) [IsCofibrant A] :
    coneToScalarSpan A ≫ (ScalarSphereSuspension.diskToZeroSpan (I := J)).app A =
      (OriginalISuspension.coneToZeroSpan (B := B) (I := J)).app A ≫
        (OriginalISuspension.zeroSpan (I := J)).map
          ((ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A) := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact Diagrams.zeroDiagramIsTerminal.hom_ext _ _
  · exact (Category.id_comp _).trans (Category.id_comp _).symm

/-- The original lifted cone and the actual scalar quotient have the unchanged full zero source. -/
theorem coneToScalarDisk_quotient_zero (A : (Carrier (J := J))) [IsCofibrant A] :
    iota.app A ≫ (coneToScalarDisk A ≫
        EnrichedFunctorCat.scalarTensorMap ScalarSphereSuspension.quotient A) =
      Diagrams.toZero A ≫ Diagrams.zeroTo (T.obj A) := by
  let k : cone.obj A ⟶ tensorLeftObject PointedCGWH.diskOne A := coneToScalarDisk A
  let t : tensorLeftObject PointedCGWH.diskOne A ⟶ T.obj A :=
    scalarTensorMap ScalarSphereSuspension.quotient A
  have hk : iota.app A ≫ k = scalarBoundary A := coneToScalarDisk_source A
  have hq : scalarTensorMap PointedCGWH.diskBoundary A ≫ t =
      Diagrams.toZero (tensorLeftObject (Arrow.mk PointedCGWH.diskBoundary).left A) ≫
        Diagrams.zeroTo (T.obj A) := (ScalarSphereSuspension.sphereScalarIsPushout A).w
  change iota.app A ≫ (k ≫ t) = Diagrams.toZero A ≫ Diagrams.zeroTo (T.obj A)
  calc
    _ = (iota.app A ≫ k) ≫ t := (Category.assoc _ _ _).symm
    _ = scalarBoundary A ≫ t := congrArg (· ≫ t) hk
    _ = ((ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A ≫
          scalarTensorMap PointedCGWH.diskBoundary A) ≫ t := rfl
    _ = (ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A ≫
        (scalarTensorMap PointedCGWH.diskBoundary A ≫ t) := Category.assoc _ _ _
    _ = ((ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A ≫
        Diagrams.toZero (tensorLeftObject (Arrow.mk PointedCGWH.diskBoundary).left A)) ≫
          Diagrams.zeroTo (T.obj A) :=
      (congrArg ((ScalarSphereSuspension.sourceTensorUnitIso (I := J)).inv.app A ≫ ·) hq).trans
        (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ Diagrams.zeroTo (T.obj A))
      (Diagrams.zeroDiagramIsTerminal.hom_ext _ _)


/-- The actual original I cone lift descends into the unchanged one-sphere scalar suspension. -/
def coneToScalarSuspension (A : (Carrier (J := J))) [IsCofibrant A] : S.obj A ⟶ T.obj A :=
  suspensionDesc A (T.obj A)
    (coneToScalarDisk A ≫ EnrichedFunctorCat.scalarTensorMap ScalarSphereSuspension.quotient A)
    (coneToScalarDisk_quotient_zero A)

/-- Its actual original cone leg is the complete scalar disk lift followed by the quotient. -/
theorem coneToScalarSuspension_cone (A : (Carrier (J := J))) [IsCofibrant A] :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inl ≫
      coneToScalarSuspension A =
      coneToScalarDisk A ≫ EnrichedFunctorCat.scalarTensorMap ScalarSphereSuspension.quotient A :=
  suspensionDesc_typed_cone _ _ _ _

/-- The full original zero leg is retained by the same actual scalar comparison. -/
theorem coneToScalarSuspension_zero (A : (Carrier (J := J))) [IsCofibrant A] :
    (OriginalISuspensionCofibrantComparison.originalSuspensionCocone (B := B) A).inr ≫
      coneToScalarSuspension A = Diagrams.zeroTo (T.obj A) :=
  suspensionDesc_typed_zero _ _ _ _

/-- The actual cone-span colimit map keeps both full original quotient comparison functions. -/
theorem coneToScalarSuspension_colimit (A : (Carrier (J := J))) [IsCofibrant A] :
    colim.map (coneToScalarSpan A) ≫ (ScalarSphereSuspension.sphereScalarNatIso
        (I := J)).hom.app A =
      (OriginalISuspension.coneColimitIsoSuspension (B := B) (I := J)).hom.app A ≫
        coneToScalarSuspension A := by
  let m : S.obj A ⟶ colim.obj ((ScalarSphereSuspension.diskSpan (I := J)).obj A) :=
    colim.map (coneToScalarSpan A)
  let e : colim.obj ((ScalarSphereSuspension.diskSpan (I := J)).obj A) ⟶ T.obj A :=
    (ScalarSphereSuspension.sphereScalarNatIso (I := J)).hom.app A
  have hm : m ≫ e = coneToScalarSuspension A := by
    apply suspension_hom_ext A
    · let k : cone.obj A ⟶ tensorLeftObject PointedCGWH.diskOne A := coneToScalarDisk A
      let j : tensorLeftObject PointedCGWH.diskOne A ⟶
          colim.obj ((ScalarSphereSuspension.diskSpan (I := J)).obj A) :=
        colimit.ι ((ScalarSphereSuspension.diskSpan (I := J)).obj A) WalkingSpan.left
      let t : tensorLeftObject PointedCGWH.diskOne A ⟶ T.obj A :=
        scalarTensorMap ScalarSphereSuspension.quotient A
      have h : suspensionInl A ≫ m = k ≫ j :=
        ι_colimMap (coneToScalarSpan A) WalkingSpan.left
      have hLeg : j ≫ e = t := ScalarSphereSuspension.sphereScalarColimitIso_inl A
      have hFace : suspensionInl A ≫ coneToScalarSuspension A = k ≫ t :=
        coneToScalarSuspension_cone A
      exact (Category.assoc (suspensionInl A) m e).symm.trans
        ((congrArg (· ≫ e) h).trans
          ((Category.assoc k j e).trans ((congrArg (k ≫ ·) hLeg).trans hFace.symm)))
    · have h : suspensionInr A ≫ m = 𝟙 Diagrams.zeroDiagram ≫
          colimit.ι ((ScalarSphereSuspension.diskSpan (I := J)).obj A) WalkingSpan.right :=
        ι_colimMap (coneToScalarSpan A) WalkingSpan.right
      have hLeg : colimit.ι ((ScalarSphereSuspension.diskSpan (I := J)).obj A)
          WalkingSpan.right ≫ e =
          Diagrams.zeroTo (T.obj A) := ScalarSphereSuspension.sphereScalarColimitIso_inr A
      calc
        _ = (suspensionInr A ≫ m) ≫ e := (Category.assoc _ _ _).symm
        _ = (𝟙 Diagrams.zeroDiagram ≫ colimit.ι
            ((ScalarSphereSuspension.diskSpan (I := J)).obj A) WalkingSpan.right) ≫ e :=
          congrArg (· ≫ e) h
        _ = Diagrams.zeroTo (T.obj A) :=
          (Category.assoc _ _ _).trans ((congrArg (𝟙 Diagrams.zeroDiagram ≫ ·) hLeg).trans
            (Category.id_comp _))
        _ = _ := (coneToScalarSuspension_zero A).symm
  have hIso : (OriginalISuspension.coneColimitIsoSuspension (B := B) (I := J)).hom.app A =
      𝟙 (S.obj A) := rfl
  exact hm.trans ((Category.id_comp (coneToScalarSuspension A)).symm.trans
    (congrArg (· ≫ coneToScalarSuspension A) hIso.symm))


/-- Naturality of the actual homotopy-pushout comparison preserves the full quotient triangle. -/
theorem coneToScalarSuspension_pushoutTriangle (A : (Carrier (J := J))) [IsCofibrant A] :
    (OriginalISuspension.toSuspension (B := B) (I := J)).app A ≫
        coneToScalarSuspension A =
      homotopyPushout.map (coneToScalarSpan A) ≫
        (ScalarSphereSuspension.toSpherePushout (B := B) (I := J)).app A := by
  dsimp only [OriginalISuspension.toSuspension, ScalarSphereSuspension.toSpherePushout,
    NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← coneToScalarSuspension_colimit, ← Category.assoc,
    ← homotopyPushoutComparison.naturality, Category.assoc]

/-- The same actual quotient triangle is retained after the original level localization. -/
theorem coneToScalarSuspension_pushoutTriangle_ho (A : (Carrier (J := J))) [IsCofibrant A] :
    H.map ((OriginalISuspension.toSuspension (B := B) (I := J)).app A) ≫
        H.map (coneToScalarSuspension A) =
      H.map (homotopyPushout.map (coneToScalarSpan A)) ≫
        H.map ((ScalarSphereSuspension.toSpherePushout (B := B) (I := J)).app A) := by
  simpa only [H.map_comp] using H.congr_map (coneToScalarSuspension_pushoutTriangle A)

/-- Both actual cone collapses retain the complete source-unit map on homotopy pushouts. -/
theorem coneToScalarSpan_collapse_ho (A : (Carrier (J := J))) [IsCofibrant A] :
    H.map (homotopyPushout.map (coneToScalarSpan A)) ≫
        H.map ((ScalarSphereSuspension.toZeroPushout (B := B) (I := J)).app A) =
      H.map ((OriginalISuspension.toZeroPushout (B := B) (I := J)).app A) ≫
        (OriginalISuspensionCofibrantComparison.sourceZeroPushoutUnitNatIso
          (B := B) (I := J)).inv.app A := by
  have h := homotopyPushout.congr_map (coneToScalarSpan_collapse A)
  simp only [Functor.map_comp] at h
  have k := H.congr_map h
  simp only [H.map_comp] at k
  simpa only [OriginalISuspension.toZeroPushout, ScalarSphereSuspension.toZeroPushout,
    OriginalISuspensionCofibrantComparison.sourceZeroPushoutUnitNatIso,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app] using k

/-- The constructed I-cone/scalar-disk lift is exactly the existing full five-span Ho comparison. -/
theorem coneToScalarSuspension_ho (A : (Carrier (J := J))) [IsCofibrant A] :
    H.map (coneToScalarSuspension A) =
      (OriginalISuspensionCofibrantComparison.comparison (B := B) A).hom := by
  apply (cancel_epi (OriginalISuspensionCofibrantComparison.coneSuspensionIso
    (B := B) A).hom).1
  rw [OriginalISuspensionCofibrantComparison.comparison_hom]
  simp only [Iso.hom_inv_id_assoc]
  calc
    _ = H.map (homotopyPushout.map (coneToScalarSpan A)) ≫
        (OriginalISuspensionCofibrantComparison.diskSphereIso (B := B) A).hom :=
      coneToScalarSuspension_pushoutTriangle_ho A
    _ = (OriginalISuspensionCofibrantComparison.coneZeroIso (B := B) A).hom ≫
        (OriginalISuspensionCofibrantComparison.sourceZeroPushoutUnitNatIso
          (B := B) (I := J)).inv.app A ≫
          (OriginalISuspensionCofibrantComparison.diskZeroIso (B := B) A).inv ≫
            (OriginalISuspensionCofibrantComparison.diskSphereIso (B := B) A).hom := by
      have h := coneToScalarSpan_collapse_ho A
      change H.map (homotopyPushout.map (coneToScalarSpan A)) ≫
          (OriginalISuspensionCofibrantComparison.diskZeroIso (B := B) A).hom =
        (OriginalISuspensionCofibrantComparison.coneZeroIso (B := B) A).hom ≫
          (OriginalISuspensionCofibrantComparison.sourceZeroPushoutUnitNatIso
            (B := B) (I := J)).inv.app A at h
      have k := congrArg (fun f => f ≫
        (OriginalISuspensionCofibrantComparison.diskZeroIso (B := B) A).inv ≫
          (OriginalISuspensionCofibrantComparison.diskSphereIso (B := B) A).hom) h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using k

/--
The actual constructed original cone/scalar quotient map is weak by its proved full span word.
-/
theorem coneToScalarSuspension_weak (A : (Carrier (J := J))) [IsCofibrant A] :
    weakEquivalences (Carrier (J := J)) (coneToScalarSuspension A) := by
  apply (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mpr
  rw [coneToScalarSuspension_ho]
  infer_instance

end ConeLiftGeometry

end HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry
