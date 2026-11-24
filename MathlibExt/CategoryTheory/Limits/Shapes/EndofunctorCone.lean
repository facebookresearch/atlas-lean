/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/


module

public import MathlibExt.CategoryTheory.Limits.Shapes.Cofiber
public import MathlibExt.CategoryTheory.Limits.Shapes.ZeroObjectArrowFunctors
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Cones, cofibers, suspension and rotation from endofunctor endpoints

Original source maps and endpoint/cocone equations are retained. These
constructions supply the categorical source framework used in MMSS
Definition 6.8 and its cone, cylinder and homotopy-pushout applications.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory CategoryTheory.Limits
open HomotopicalAlgebra
open scoped ZeroObject

namespace CategoryTheory.OriginalScalarCone

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasPushouts C]

/-- The full original cone span collapses the given second endpoint to zero. -/
def coneSpan (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) : C ⥤ (WalkingSpan ⥤ C) where
  obj X := span (e₁.app X) (0 : X ⟶ (0 : C))
  map f := spanHomMk f (S.map f) (𝟙 (0 : C))
    (e₁.naturality f).symm (by simp)
  map_id X := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _) <;> simp
  map_comp f g := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _) <;> simp

/-- Every actual cone map is induced by the entire original endpoint span. -/
def coneFunctor (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) : C ⥤ C := coneSpan S e₁ ⋙ colim

/-- The original interval quotient is the actual left pushout leg. -/
def quotient (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) (X : C) :
    S.obj X ⟶ (coneFunctor S e₁).obj X := pushout.inl (e₁.app X) (0 : X ⟶ (0 : C))

/-- The given second endpoint is zero in the same actual scalar cone. -/
@[reassoc]
theorem endpoint_quotient (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) (X : C) :
    e₁.app X ≫ quotient S e₁ X = 0 := by
  change e₁.app X ≫ pushout.inl (e₁.app X) (0 : X ⟶ (0 : C)) = 0
  simpa only [zero_comp] using
    (pushout.condition (f := e₁.app X) (g := (0 : X ⟶ (0 : C))))

/-- Both original quotient maps commute with every full original input map. -/
@[reassoc]
theorem quotient_naturality (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    S.map f ≫ quotient S e₁ Y = quotient S e₁ X ≫ (coneFunctor S e₁).map f := by
  exact (ι_colimMap ((coneSpan S e₁).map f) WalkingSpan.left).symm

/-- The quotient is a whole natural transformation on all original input arrows. -/
def quotientNatTrans (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) : S ⟶ coneFunctor S e₁ where
  app := quotient S e₁
  naturality _ _ f := quotient_naturality S e₁ f

/-- The original first endpoint followed by the actual cone quotient. -/
def inclusionNatTrans (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) : 𝟭 C ⟶ coneFunctor S e₁ :=
  e₀ ≫ quotientNatTrans S e₁

/-- The actual cone cocone is a pushout of the original second endpoint. -/
theorem coneIsPushout (S : C ⥤ C) (e₁ : 𝟭 C ⟶ S) (X : C) :
    IsPushout (e₁.app X) (0 : X ⟶ (0 : C)) (quotient S e₁ X)
      (pushout.inr (e₁.app X) (0 : X ⟶ (0 : C))) :=
  IsPushout.of_hasPushout _ _

/-- The full interval contraction descends through the actual cone pushout. -/
def contraction (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    (e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C) (a : S ⋙ T ⟶ S)
    (hFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
    (X : C) : T.obj ((coneFunctor S e₁).obj X) ⟶ (coneFunctor S e₁).obj X :=
  ((coneIsPushout S e₁ X).map T).desc (a.app X ≫ quotient S e₁ X) 0 (by
    rw [← Category.assoc, hFixed, Category.assoc, endpoint_quotient, comp_zero, comp_zero])

/-- The original whole interval leg of the cone contraction is retained. -/
@[reassoc]
theorem quotient_contraction (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    (e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C) (a : S ⋙ T ⟶ S)
    (hFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
    (X : C) : T.map (quotient S e₁ X) ≫ contraction T S e₁ pT a hFixed X =
      a.app X ≫ quotient S e₁ X :=
  ((coneIsPushout S e₁ X).map T).inl_desc _ _ _

/-- The cone contraction starts at the identity on the same actual cone. -/
theorem contraction_zero (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    (t₀ : 𝟭 C ⟶ T) (e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C) (a : S ⋙ T ⟶ S)
    (hFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
    (hZero : ∀ X : C, t₀.app (S.obj X) ≫ a.app X = 𝟙 (S.obj X)) (X : C) :
    t₀.app ((coneFunctor S e₁).obj X) ≫ contraction T S e₁ pT a hFixed X = 𝟙 _ := by
  have hn : quotient S e₁ X ≫ t₀.app ((coneFunctor S e₁).obj X) =
      t₀.app (S.obj X) ≫ T.map (quotient S e₁ X) := t₀.naturality _
  apply (coneIsPushout S e₁ X).hom_ext
  · rw [← Category.assoc, hn, Category.assoc,
      quotient_contraction, ← Category.assoc, hZero, Category.id_comp]
    exact (Category.comp_id _).symm
  · exact (isZero_zero C).isInitial.hom_ext _ _

/-- The cone contraction ends at the actual zero map, on arbitrary source objects. -/
theorem contraction_one (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    (t₁ : 𝟭 C ⟶ T) (e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C) (pS : S ⟶ 𝟭 C)
    (a : S ⋙ T ⟶ S)
    (hFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
    (hOne : ∀ X : C, t₁.app (S.obj X) ≫ a.app X = pS.app X ≫ e₁.app X) (X : C) :
    t₁.app ((coneFunctor S e₁).obj X) ≫ contraction T S e₁ pT a hFixed X = 0 := by
  have hn : quotient S e₁ X ≫ t₁.app ((coneFunctor S e₁).obj X) =
      t₁.app (S.obj X) ≫ T.map (quotient S e₁ X) := t₁.naturality _
  apply (coneIsPushout S e₁ X).hom_ext
  · rw [← Category.assoc, hn, Category.assoc,
      quotient_contraction, ← Category.assoc, hOne, Category.assoc,
      endpoint_quotient, comp_zero, comp_zero]
  · exact (isZero_zero C).isInitial.hom_ext _ _

/-- Every original input arrow commutes with the full cone contraction. -/
@[reassoc]
theorem contraction_naturality (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    [T.PreservesZeroMorphisms] (e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C) (a : S ⋙ T ⟶ S)
    (hFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X)
    {X Y : C} (f : X ⟶ Y) :
    T.map ((coneFunctor S e₁).map f) ≫ contraction T S e₁ pT a hFixed Y =
      contraction T S e₁ pT a hFixed X ≫ (coneFunctor S e₁).map f := by
  have hn : T.map (S.map f) ≫ a.app Y = a.app X ≫ S.map f := a.naturality f
  apply ((coneIsPushout S e₁ X).map T).hom_ext
  · rw [← Category.assoc, ← T.map_comp, ← quotient_naturality, T.map_comp,
      Category.assoc, quotient_contraction, ← Category.assoc, hn,
      Category.assoc, quotient_naturality, ← Category.assoc]
    simpa only [Category.assoc] using
      congrArg (fun g => g ≫ (coneFunctor S e₁).map f)
        (quotient_contraction T S e₁ pT a hFixed X).symm
  · exact (T.map_isZero (isZero_zero C)).isInitial.hom_ext _ _

/-- The contraction is natural on the entire original cone functor. -/
def contractionNatTrans (T S : C ⥤ C) [PreservesColimitsOfShape WalkingSpan T]
    [T.PreservesZeroMorphisms] (e₁ : 𝟭 C ⟶ S) (pT : T ⟶ 𝟭 C) (a : S ⋙ T ⟶ S)
    (hFixed : ∀ X : C, T.map (e₁.app X) ≫ a.app X = pT.app X ≫ e₁.app X) :
    coneFunctor S e₁ ⋙ T ⟶ coneFunctor S e₁ where
  app := contraction T S e₁ pT a hFixed
  naturality _ _ f := contraction_naturality T S e₁ pT a hFixed f

/-- The scalar cofiber uses the actual cone inclusion and the entire original arrow. -/
def cofiberSpan (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) : Arrow C ⥤ (WalkingSpan ⥤ C) where
  obj f := span f.hom ((inclusionNatTrans S e₀ e₁).app f.left)
  map sq := spanHomMk sq.left sq.right ((coneFunctor S e₁).map sq.left)
    sq.w.symm ((inclusionNatTrans S e₀ e₁).naturality sq.left).symm
  map_id f := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _) <;> simp
  map_comp f g := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _) <;> simp

/-- The actual scalar cofiber is the colimit of its full original cone span. -/
def cofiberFunctor (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) : Arrow C ⥤ C :=
  cofiberSpan S e₀ e₁ ⋙ colim

/-- The original target leg of the scalar cofiber. -/
def cofiberTarget (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    Y ⟶ (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) :=
  pushout.inl f ((inclusionNatTrans S e₀ e₁).app X)

/-- The original cone leg of the same scalar cofiber. -/
def cofiberCone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    (coneFunctor S e₁).obj X ⟶ (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) :=
  pushout.inr f ((inclusionNatTrans S e₀ e₁).app X)

/-- The actual original target and cone legs keep their complete source equation. -/
theorem cofiber_condition (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    f ≫ cofiberTarget S e₀ e₁ f =
      (inclusionNatTrans S e₀ e₁).app X ≫ cofiberCone S e₀ e₁ f :=
  pushout.condition

/-- The actual scalar cofiber keeps the original full pushout cocone. -/
theorem cofiberIsPushout (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    IsPushout f ((inclusionNatTrans S e₀ e₁).app X)
      (cofiberTarget S e₀ e₁ f) (cofiberCone S e₀ e₁ f) :=
  IsPushout.of_hasPushout _ _

/-- The original joint boundary attaches the actual cone inclusion after collapsing its end. -/
theorem coneJointIsPushout [HasBinaryCoproducts C]
    (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (X : C) :
    IsPushout (coprod.desc (e₀.app X) (e₁.app X))
      (coprod.desc (𝟙 X) (0 : X ⟶ X)) (quotient S e₁ X)
      ((inclusionNatTrans S e₀ e₁).app X) := by
  let i := coprod.desc (e₀.app X) (e₁.app X)
  let p := coprod.desc (𝟙 X) (0 : X ⟶ X)
  let q := quotient S e₁ X
  let c := (inclusionNatTrans S e₀ e₁).app X
  let sqC := coneIsPushout S e₁ X
  have hw : i ≫ q = p ≫ c := by
    apply coprod.hom_ext
    · simp only [i, p, coprod.inl_desc_assoc]
      change c = 𝟙 X ≫ c
      exact (Category.id_comp c).symm
    · simp only [i, p, coprod.inr_desc_assoc, zero_comp]
      exact endpoint_quotient S e₁ X
  have he₀ (s : PushoutCocone i p) : e₀.app X ≫ s.inl = s.inr := by
    have h := congrArg (fun g => (coprod.inl : X ⟶ X ⨿ X) ≫ g) s.condition
    simpa only [i, p, Category.assoc, coprod.inl_desc_assoc, Category.id_comp] using h
  have he₁ (s : PushoutCocone i p) : e₁.app X ≫ s.inl = 0 := by
    have h := congrArg (fun g => (coprod.inr : X ⟶ X ⨿ X) ≫ g) s.condition
    simpa only [i, p, Category.assoc, coprod.inr_desc_assoc, zero_comp] using h
  let hc : IsColimit (PushoutCocone.mk q c hw) :=
    PushoutCocone.IsColimit.mk hw
      (fun s => sqC.desc s.inl 0 (by rw [he₁ s, zero_comp]))
      (fun s => sqC.inl_desc _ _ _)
      (fun s => by
        change (e₀.app X ≫ q) ≫ _ = s.inr
        rw [Category.assoc, sqC.inl_desc]
        exact he₀ s)
      (fun s m hLeft _ => by
        apply (coneIsPushout S e₁ X).hom_ext
        · rw [sqC.inl_desc]
          exact hLeft
        · exact (isZero_zero C).isInitial.hom_ext _ _)
  exact IsPushout.of_isColimit hc

end CategoryTheory.OriginalScalarCone

namespace CategoryTheory.OriginalScalarCone

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasPushouts C]

/-- The actual original double cylinder collapses the second source endpoint. -/
abbrev doubleCylinder (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) : C :=
  pushout (e₁.app X ≫ pushout.inl (e₀.app X) f) (0 : X ⟶ (0 : C))

/-- The complete mapping-cylinder map uses the original scalar cone and target legs. -/
def cylinderToCofiber (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    pushout (e₀.app X) f ⟶ (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) :=
  pushout.desc (quotient S e₁ X ≫ cofiberCone S e₀ e₁ f)
    (cofiberTarget S e₀ e₁ f) (by
      have h : (e₀.app X ≫ quotient S e₁ X) ≫ cofiberCone S e₀ e₁ f =
          f ≫ cofiberTarget S e₀ e₁ f := (cofiber_condition S e₀ e₁ f).symm
      exact (Category.assoc _ _ _).symm.trans h)

/-- The whole original interval map is retained before the endpoint collapse. -/
@[reassoc]
theorem cylinderToCofiber_interval (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    pushout.inl (e₀.app X) f ≫ cylinderToCofiber S e₀ e₁ f =
      quotient S e₁ X ≫ cofiberCone S e₀ e₁ f := pushout.inl_desc _ _ _

/-- The original target map is retained before the endpoint collapse. -/
@[reassoc]
theorem cylinderToCofiber_target (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    pushout.inr (e₀.app X) f ≫ cylinderToCofiber S e₀ e₁ f =
      cofiberTarget S e₀ e₁ f := pushout.inr_desc _ _ _

/-- The same actual second endpoint vanishes in the scalar cofiber. -/
@[reassoc]
theorem cylinderToCofiber_endpoint (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    (e₁.app X ≫ pushout.inl (e₀.app X) f) ≫ cylinderToCofiber S e₀ e₁ f = 0 := by
  rw [Category.assoc, cylinderToCofiber_interval, ← Category.assoc,
    endpoint_quotient, zero_comp]

/-- The full original double cylinder maps to the same scalar cofiber. -/
def doubleToCofiber (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    doubleCylinder S e₀ e₁ f ⟶ (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) :=
  pushout.desc (cylinderToCofiber S e₀ e₁ f) 0 (by
    rw [cylinderToCofiber_endpoint, zero_comp])

/-- The double-cylinder comparison retains its entire actual cylinder leg. -/
@[reassoc]
theorem doubleToCofiber_cylinder (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    pushout.inl (e₁.app X ≫ pushout.inl (e₀.app X) f) (0 : X ⟶ (0 : C)) ≫
        doubleToCofiber S e₀ e₁ f = cylinderToCofiber S e₀ e₁ f :=
  pushout.inl_desc _ _ _

/-- The inverse cone map descends the exact original interval-to-double-cylinder map. -/
def coneToDouble (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    (coneFunctor S e₁).obj X ⟶ doubleCylinder S e₀ e₁ f :=
  pushout.desc
    (pushout.inl (e₀.app X) f ≫
      pushout.inl (e₁.app X ≫ pushout.inl (e₀.app X) f) (0 : X ⟶ (0 : C)))
    0 (by
      rw [← Category.assoc, pushout.condition, zero_comp, zero_comp])

/-- The complete inverse cone map retains the original interval leg. -/
@[reassoc]
theorem coneToDouble_interval (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    quotient S e₁ X ≫ coneToDouble S e₀ e₁ f =
      pushout.inl (e₀.app X) f ≫
        pushout.inl (e₁.app X ≫ pushout.inl (e₀.app X) f) (0 : X ⟶ (0 : C)) :=
  pushout.inl_desc _ _ _

/-- The actual inverse scalar-cofiber map uses the same target and inverse cone legs. -/
def cofiberToDouble (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) ⟶ doubleCylinder S e₀ e₁ f :=
  pushout.desc
    (pushout.inr (e₀.app X) f ≫
      pushout.inl (e₁.app X ≫ pushout.inl (e₀.app X) f) (0 : X ⟶ (0 : C)))
    (coneToDouble S e₀ e₁ f) (by
      change f ≫ (pushout.inr (e₀.app X) f ≫ _) =
        (e₀.app X ≫ quotient S e₁ X) ≫ coneToDouble S e₀ e₁ f
      rw [Category.assoc, coneToDouble_interval, ← Category.assoc, ← Category.assoc,
        pushout.condition])

/-- The original target leg is retained by the inverse scalar-cofiber comparison. -/
@[reassoc]
theorem cofiberToDouble_target (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    cofiberTarget S e₀ e₁ f ≫ cofiberToDouble S e₀ e₁ f =
      pushout.inr (e₀.app X) f ≫
        pushout.inl (e₁.app X ≫ pushout.inl (e₀.app X) f) (0 : X ⟶ (0 : C)) :=
  pushout.inl_desc _ _ _

/-- The actual cone leg is retained by the inverse scalar-cofiber comparison. -/
@[reassoc]
theorem cofiberToDouble_cone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    cofiberCone S e₀ e₁ f ≫ cofiberToDouble S e₀ e₁ f = coneToDouble S e₀ e₁ f :=
  pushout.inr_desc _ _ _

/-- Both complete original comparison maps compose to the actual double-cylinder identity. -/
theorem doubleToCofiber_cofiberToDouble (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    doubleToCofiber S e₀ e₁ f ≫ cofiberToDouble S e₀ e₁ f = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [← Category.assoc, doubleToCofiber_cylinder]
    apply pushout.hom_ext
    · rw [← Category.assoc, cylinderToCofiber_interval, Category.assoc,
        cofiberToDouble_cone, coneToDouble_interval, Category.comp_id]
    · rw [← Category.assoc, cylinderToCofiber_target,
        cofiberToDouble_target, Category.comp_id]
  · exact (isZero_zero C).isInitial.hom_ext _ _

/-- Both complete original comparison maps compose to the actual scalar-cofiber identity. -/
theorem cofiberToDouble_doubleToCofiber (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y : C} (f : X ⟶ Y) :
    cofiberToDouble S e₀ e₁ f ≫ doubleToCofiber S e₀ e₁ f = 𝟙 _ := by
  apply (cofiberIsPushout S e₀ e₁ f).hom_ext
  · rw [← Category.assoc, cofiberToDouble_target, Category.assoc,
      doubleToCofiber_cylinder, cylinderToCofiber_target, Category.comp_id]
  · rw [← Category.assoc, cofiberToDouble_cone]
    apply (coneIsPushout S e₁ X).hom_ext
    · rw [← Category.assoc, coneToDouble_interval, Category.assoc,
        doubleToCofiber_cylinder, cylinderToCofiber_interval, Category.comp_id]
    · exact (isZero_zero C).isInitial.hom_ext _ _

/-- The whole original scalar cofiber is isomorphic to the actual double cylinder. -/
def doubleCofiberIso (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {X Y : C} (f : X ⟶ Y) :
    doubleCylinder S e₀ e₁ f ≅ (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) where
  hom := doubleToCofiber S e₀ e₁ f
  inv := cofiberToDouble S e₀ e₁ f
  hom_inv_id := doubleToCofiber_cofiberToDouble S e₀ e₁ f
  inv_hom_id := cofiberToDouble_doubleToCofiber S e₀ e₁ f

end CategoryTheory.OriginalScalarCone

namespace CategoryTheory.OriginalScalarCone

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasPushouts C]

/-- The actual scalar-cofiber comparison uses the given zero object and caller cocone. -/
def cofiberQuotientComparison (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y Z P : C} (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z)
    (kY : Y ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout f z kY kZ) :
    (cofiberFunctor S e₀ e₁).obj (Arrow.mk f) ⟶ P :=
  (cofiberIsPushout S e₀ e₁ f).desc kY 0 (by
    rw [comp_zero, sq.w, hZ.eq_of_tgt z 0, zero_comp])

/-- The actual target leg of the scalar-cofiber comparison is the caller target leg. -/
@[reassoc]
theorem cofiberQuotientComparison_target (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y Z P : C} (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z)
    (kY : Y ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout f z kY kZ) :
    cofiberTarget S e₀ e₁ f ≫ cofiberQuotientComparison S e₀ e₁ f z hZ kY kZ sq = kY :=
  (cofiberIsPushout S e₀ e₁ f).inl_desc _ _ _

/-- The same original cone vanishes under the actual scalar-cofiber comparison. -/
@[reassoc]
theorem cofiberQuotientComparison_cone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {X Y Z P : C} (f : X ⟶ Y) (z : X ⟶ Z) (hZ : IsZero Z)
    (kY : Y ⟶ P) (kZ : Z ⟶ P) (sq : IsPushout f z kY kZ) :
    cofiberCone S e₀ e₁ f ≫ cofiberQuotientComparison S e₀ e₁ f z hZ kY kZ sq = 0 :=
  (cofiberIsPushout S e₀ e₁ f).inr_desc _ _ _

/-- Every full original arrow square retains its actual scalar-cofiber target square. -/
@[reassoc]
theorem cofiberTarget_map (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {f g : Arrow C} (sq : f ⟶ g) :
    cofiberTarget S e₀ e₁ f.hom ≫ (cofiberFunctor S e₀ e₁).map sq =
      sq.right ≫ cofiberTarget S e₀ e₁ g.hom :=
  ι_colimMap ((cofiberSpan S e₀ e₁).map sq) WalkingSpan.left

/-- Every full original arrow square retains its actual scalar-cofiber cone square. -/
@[reassoc]
theorem cofiberCone_map (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {f g : Arrow C} (sq : f ⟶ g) :
    cofiberCone S e₀ e₁ f.hom ≫ (cofiberFunctor S e₀ e₁).map sq =
      (coneFunctor S e₁).map sq.left ≫ cofiberCone S e₀ e₁ g.hom :=
  ι_colimMap ((cofiberSpan S e₀ e₁).map sq) WalkingSpan.right

/-- Scalar suspension is the actual cofiber of the original object-to-given-zero map. -/
def suspensionFunctor (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) : C ⥤ C :=
  originalTerminalArrowFunctor hZ ⋙ cofiberFunctor S e₀ e₁

/-- The scalar suspension quotient retains the original cone and given zero choice. -/
def suspensionQuotient (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) (X : C) :
    (coneFunctor S e₁).obj X ⟶ (suspensionFunctor S e₀ e₁ hZ).obj X :=
  cofiberCone S e₀ e₁ (hZ.from_ X)

/-- The same given zero object is the original scalar suspension's target cocone leg. -/
def suspensionZeroLeg (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) (X : C) :
    Z ⟶ (suspensionFunctor S e₀ e₁ hZ).obj X :=
  cofiberTarget S e₀ e₁ (hZ.from_ X)

/-- The original first endpoint is also zero in the same scalar suspension. -/
@[reassoc]
theorem inclusion_suspensionQuotient (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {Z : C} (hZ : IsZero Z) (X : C) :
    (inclusionNatTrans S e₀ e₁).app X ≫ suspensionQuotient S e₀ e₁ hZ X = 0 := by
  have h := (cofiber_condition S e₀ e₁ (hZ.from_ X)).symm
  let q : Z ⟶ (suspensionFunctor S e₀ e₁ hZ).obj X := cofiberTarget S e₀ e₁ (hZ.from_ X)
  have hq : hZ.from_ X ≫ q = 0 := by
    rw [hZ.eq_of_tgt (hZ.from_ X) 0, zero_comp]
  exact h.trans hq

/-- Every complete original source map retains the same scalar suspension quotient square. -/
@[reassoc]
theorem suspensionQuotient_naturality (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {Z : C} (hZ : IsZero Z) {X Y : C} (f : X ⟶ Y) :
    (coneFunctor S e₁).map f ≫ suspensionQuotient S e₀ e₁ hZ Y =
      suspensionQuotient S e₀ e₁ hZ X ≫ (suspensionFunctor S e₀ e₁ hZ).map f :=
  (cofiberCone_map S e₀ e₁ ((originalTerminalArrowFunctor hZ).map f)).symm

/-- The actual scalar boundary collapses the original target and quotients the original cone. -/
def boundary (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    (cofiberFunctor S e₀ e₁).obj f ⟶ (suspensionFunctor S e₀ e₁ hZ).obj f.left :=
  (cofiberIsPushout S e₀ e₁ f.hom).desc 0
    (suspensionQuotient S e₀ e₁ hZ f.left) (by
      rw [comp_zero, inclusion_suspensionQuotient])

/-- The actual scalar boundary vanishes on the complete original target leg. -/
@[reassoc]
theorem boundary_target (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    cofiberTarget S e₀ e₁ f.hom ≫ boundary S e₀ e₁ hZ f = 0 :=
  (cofiberIsPushout S e₀ e₁ f.hom).inl_desc _ _ _

/-- The actual scalar boundary preserves the complete original cone quotient. -/
@[reassoc]
theorem boundary_cone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    cofiberCone S e₀ e₁ f.hom ≫ boundary S e₀ e₁ hZ f =
      suspensionQuotient S e₀ e₁ hZ f.left :=
  (cofiberIsPushout S e₀ e₁ f.hom).inr_desc _ _ _

/-- The full scalar boundary keeps every complete original arrow square. -/
@[reassoc]
theorem boundary_naturality (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z)
    {f g : Arrow C} (sq : f ⟶ g) :
    (cofiberFunctor S e₀ e₁).map sq ≫ boundary S e₀ e₁ hZ g =
      boundary S e₀ e₁ hZ f ≫ (suspensionFunctor S e₀ e₁ hZ).map sq.left := by
  let iF : f.right ⟶ (cofiberFunctor S e₀ e₁).obj f := cofiberTarget S e₀ e₁ f.hom
  let iG : g.right ⟶ (cofiberFunctor S e₀ e₁).obj g := cofiberTarget S e₀ e₁ g.hom
  let qF : (coneFunctor S e₁).obj f.left ⟶ (cofiberFunctor S e₀ e₁).obj f :=
    cofiberCone S e₀ e₁ f.hom
  let qG : (coneFunctor S e₁).obj g.left ⟶ (cofiberFunctor S e₀ e₁).obj g :=
    cofiberCone S e₀ e₁ g.hom
  let bF : (cofiberFunctor S e₀ e₁).obj f ⟶ (suspensionFunctor S e₀ e₁ hZ).obj f.left :=
    boundary S e₀ e₁ hZ f
  let bG : (cofiberFunctor S e₀ e₁).obj g ⟶ (suspensionFunctor S e₀ e₁ hZ).obj g.left :=
    boundary S e₀ e₁ hZ g
  let m : (cofiberFunctor S e₀ e₁).obj f ⟶ (cofiberFunctor S e₀ e₁).obj g :=
    (cofiberFunctor S e₀ e₁).map sq
  let s := (suspensionFunctor S e₀ e₁ hZ).map sq.left
  have hL : iF ≫ m = sq.right ≫ iG := cofiberTarget_map S e₀ e₁ sq
  have hR : qF ≫ m = (coneFunctor S e₁).map sq.left ≫ qG := cofiberCone_map S e₀ e₁ sq
  have hLF : iF ≫ bF = 0 := boundary_target S e₀ e₁ hZ f
  have hLG : iG ≫ bG = 0 := boundary_target S e₀ e₁ hZ g
  have hRF : qF ≫ bF = suspensionQuotient S e₀ e₁ hZ f.left := boundary_cone S e₀ e₁ hZ f
  have hRG : qG ≫ bG = suspensionQuotient S e₀ e₁ hZ g.left := boundary_cone S e₀ e₁ hZ g
  have sqF : IsPushout f.hom ((inclusionNatTrans S e₀ e₁).app f.left) iF qF :=
    cofiberIsPushout S e₀ e₁ f.hom
  apply sqF.hom_ext
  · change iF ≫ (m ≫ bG) = iF ≫ (bF ≫ s)
    rw [← Category.assoc, hL, Category.assoc, hLG, comp_zero,
      ← Category.assoc, hLF, zero_comp]
  · change qF ≫ (m ≫ bG) = qF ≫ (bF ≫ s)
    rw [← Category.assoc, hR, Category.assoc, hRG,
      suspensionQuotient_naturality, ← Category.assoc, hRF]

/-- The boundary is a whole natural transformation on the original full arrow category. -/
def boundaryNatTrans (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) :
    cofiberFunctor S e₀ e₁ ⟶ Arrow.leftFunc ⋙ suspensionFunctor S e₀ e₁ hZ where
  app := boundary S e₀ e₁ hZ
  naturality _ _ sq := boundary_naturality S e₀ e₁ hZ sq

/-- The full original target-to-cofiber arrows form a genuine functor on all arrow squares. -/
def rotationArrowFunctor (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (cofiberTarget S e₀ e₁ f.hom)
  map sq := Arrow.homMk sq.right ((cofiberFunctor S e₀ e₁).map sq)
    (cofiberTarget_map S e₀ e₁ sq).symm
  map_id f := by
    cases f
    apply Arrow.hom_ext
    · rfl
    · exact (cofiberFunctor S e₀ e₁).map_id _
  map_comp sq sq' := by
    apply Arrow.hom_ext
    · rfl
    · exact (cofiberFunctor S e₀ e₁).map_comp sq sq'

/-- The actual scalar cofiber rotation uses the entire original target-to-cofiber map. -/
def rotationFunctor (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) : Arrow C ⥤ C :=
  rotationArrowFunctor S e₀ e₁ ⋙ cofiberFunctor S e₀ e₁

/-- The actual boundary and original zero leg present the quotient of the original target. -/
theorem boundaryIsPushout (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z)
    (f : Arrow C) :
    IsPushout (cofiberTarget S e₀ e₁ f.hom) (hZ.from_ f.right)
      (boundary S e₀ e₁ hZ f) (suspensionZeroLeg S e₀ e₁ hZ f.left) := by
  have hZero : f.hom ≫ hZ.from_ f.right = hZ.from_ f.left := hZ.eq_of_tgt _ _
  have hOuter : IsPushout (f.hom ≫ hZ.from_ f.right)
      ((inclusionNatTrans S e₀ e₁).app f.left)
      (suspensionZeroLeg S e₀ e₁ hZ f.left)
      (cofiberCone S e₀ e₁ f.hom ≫ boundary S e₀ e₁ hZ f) := by
    rw [hZero, boundary_cone]
    exact cofiberIsPushout S e₀ e₁ (hZ.from_ f.left)
  have hw : hZ.from_ f.right ≫ suspensionZeroLeg S e₀ e₁ hZ f.left =
      cofiberTarget S e₀ e₁ f.hom ≫ boundary S e₀ e₁ hZ f := by
    rw [hZ.eq_of_tgt (hZ.from_ f.right) 0, zero_comp, boundary_target]
  exact (IsPushout.of_left hOuter hw (cofiberIsPushout S e₀ e₁ f.hom)).flip

/-- The original scalar rotation comparison descends the actual boundary and zero cone leg. -/
def rotationComparison (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    (rotationFunctor S e₀ e₁).obj f ⟶ (suspensionFunctor S e₀ e₁ hZ).obj f.left :=
  cofiberQuotientComparison S e₀ e₁ (cofiberTarget S e₀ e₁ f.hom)
    (hZ.from_ f.right) hZ (boundary S e₀ e₁ hZ f)
    (suspensionZeroLeg S e₀ e₁ hZ f.left) (boundaryIsPushout S e₀ e₁ hZ f)

/-- The actual scalar rotation comparison keeps its complete original cofiber leg. -/
@[reassoc]
theorem rotationComparison_cofiber (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    cofiberTarget S e₀ e₁ (cofiberTarget S e₀ e₁ f.hom) ≫
      rotationComparison S e₀ e₁ hZ f = boundary S e₀ e₁ hZ f :=
  cofiberQuotientComparison_target S e₀ e₁ _ _ _ _ _ _

/-- The actual scalar rotation comparison collapses the original cone of the target. -/
@[reassoc]
theorem rotationComparison_cone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    cofiberCone S e₀ e₁ (cofiberTarget S e₀ e₁ f.hom) ≫
      rotationComparison S e₀ e₁ hZ f = 0 :=
  cofiberQuotientComparison_cone S e₀ e₁ _ _ _ _ _ _

/-- All actual original arrow maps retain the whole scalar rotation comparison square. -/
@[reassoc]
theorem rotationComparison_naturality (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {Z : C} (hZ : IsZero Z) {f g : Arrow C} (sq : f ⟶ g) :
    (rotationFunctor S e₀ e₁).map sq ≫ rotationComparison S e₀ e₁ hZ g =
      rotationComparison S e₀ e₁ hZ f ≫ (suspensionFunctor S e₀ e₁ hZ).map sq.left := by
  let iF : (cofiberFunctor S e₀ e₁).obj f ⟶ (rotationFunctor S e₀ e₁).obj f :=
    cofiberTarget S e₀ e₁ (cofiberTarget S e₀ e₁ f.hom)
  let iG : (cofiberFunctor S e₀ e₁).obj g ⟶ (rotationFunctor S e₀ e₁).obj g :=
    cofiberTarget S e₀ e₁ (cofiberTarget S e₀ e₁ g.hom)
  let qF : (coneFunctor S e₁).obj f.right ⟶ (rotationFunctor S e₀ e₁).obj f :=
    cofiberCone S e₀ e₁ (cofiberTarget S e₀ e₁ f.hom)
  let qG : (coneFunctor S e₁).obj g.right ⟶ (rotationFunctor S e₀ e₁).obj g :=
    cofiberCone S e₀ e₁ (cofiberTarget S e₀ e₁ g.hom)
  let rF : (rotationFunctor S e₀ e₁).obj f ⟶ (suspensionFunctor S e₀ e₁ hZ).obj f.left :=
    rotationComparison S e₀ e₁ hZ f
  let rG : (rotationFunctor S e₀ e₁).obj g ⟶ (suspensionFunctor S e₀ e₁ hZ).obj g.left :=
    rotationComparison S e₀ e₁ hZ g
  let m : (rotationFunctor S e₀ e₁).obj f ⟶ (rotationFunctor S e₀ e₁).obj g :=
    (rotationFunctor S e₀ e₁).map sq
  let n : (cofiberFunctor S e₀ e₁).obj f ⟶ (cofiberFunctor S e₀ e₁).obj g :=
    (cofiberFunctor S e₀ e₁).map sq
  let s := (suspensionFunctor S e₀ e₁ hZ).map sq.left
  have hL : iF ≫ m = n ≫ iG :=
    cofiberTarget_map S e₀ e₁ ((rotationArrowFunctor S e₀ e₁).map sq)
  have hR : qF ≫ m = (coneFunctor S e₁).map sq.right ≫ qG :=
    cofiberCone_map S e₀ e₁ ((rotationArrowFunctor S e₀ e₁).map sq)
  have hLF : iF ≫ rF = boundary S e₀ e₁ hZ f := rotationComparison_cofiber S e₀ e₁ hZ f
  have hLG : iG ≫ rG = boundary S e₀ e₁ hZ g := rotationComparison_cofiber S e₀ e₁ hZ g
  have hRF : qF ≫ rF = 0 := rotationComparison_cone S e₀ e₁ hZ f
  have hRG : qG ≫ rG = 0 := rotationComparison_cone S e₀ e₁ hZ g
  have sqF : IsPushout (cofiberTarget S e₀ e₁ f.hom)
      ((inclusionNatTrans S e₀ e₁).app f.right) iF qF :=
    cofiberIsPushout S e₀ e₁ (cofiberTarget S e₀ e₁ f.hom)
  apply sqF.hom_ext
  · change iF ≫ (m ≫ rG) = iF ≫ (rF ≫ s)
    rw [← Category.assoc, hL, Category.assoc, hLG,
      boundary_naturality, ← Category.assoc, hLF]
  · change qF ≫ (m ≫ rG) = qF ≫ (rF ≫ s)
    rw [← Category.assoc, hR, Category.assoc, hRG, comp_zero,
      ← Category.assoc, hRF, zero_comp]

/-- The scalar rotation comparison is natural on the whole original arrow category. -/
def rotationComparisonNatTrans (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) {Z : C} (hZ : IsZero Z) :
    rotationFunctor S e₀ e₁ ⟶ Arrow.leftFunc ⋙ suspensionFunctor S e₀ e₁ hZ where
  app := rotationComparison S e₀ e₁ hZ
  naturality _ _ sq := rotationComparison_naturality S e₀ e₁ hZ sq

end CategoryTheory.OriginalScalarCone

namespace CategoryTheory.OriginalScalarCone

variable {C : Type uC} [Category.{vC} C] [HasPushouts C] [HasTerminal C]

/-- The actual ordinary quotient uses the original target-to-colimit leg. -/
def ordinaryQuotientTarget (f : Arrow C) : f.right ⟶ (ordinaryCofiber (C := C)).obj f :=
  ordinaryCofiberTarget f

/-- The actual ordinary quotient retains the selected terminal-to-colimit leg. -/
def ordinaryQuotientZero (f : Arrow C) : (⊤_ C) ⟶ (ordinaryCofiber (C := C)).obj f :=
  ordinaryCofiberPoint f

/-- The actual ordinary quotient retains its whole original pushout cocone. -/
theorem ordinaryQuotientIsPushout (f : Arrow C) :
    IsPushout f.hom (terminal.from f.left)
      (ordinaryQuotientTarget f) (ordinaryQuotientZero f) :=
  ordinaryCofiberIsPushout f

/-- Every actual arrow square retains the entire original ordinary quotient target square. -/
@[reassoc]
theorem ordinaryQuotientTarget_map {f g : Arrow C} (sq : f ⟶ g) :
    ordinaryQuotientTarget f ≫ (ordinaryCofiber (C := C)).map sq =
      sq.right ≫ ordinaryQuotientTarget g :=
  ordinaryCofiberTarget_naturality sq

/-- Every actual arrow square keeps the same original terminal quotient leg. -/
@[reassoc]
theorem ordinaryQuotientZero_map {f g : Arrow C} (sq : f ⟶ g) :
    ordinaryQuotientZero f ≫ (ordinaryCofiber (C := C)).map sq = ordinaryQuotientZero g :=
  ordinaryCofiberPoint_naturality sq

/-- The original quotient map across an actual pushout is an isomorphism by pasting.
No weak-equivalence or endpoint hypothesis is needed for this categorical comparison. -/
theorem ordinaryCofiberMap_isIso_of_isPushout
    {A B Z P : C} (i : A ⟶ B) (z : A ⟶ Z) (kB : B ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kB kZ) :
    IsIso ((ordinaryCofiber (C := C)).map
      (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk kZ) z kB sq.w.symm)) := by
  let f : Arrow C := Arrow.mk i
  let g : Arrow C := Arrow.mk kZ
  let a : f ⟶ g := Arrow.homMk z kB sq.w.symm
  let qF : B ⟶ (ordinaryCofiber (C := C)).obj f := ordinaryQuotientTarget f
  let qG : P ⟶ (ordinaryCofiber (C := C)).obj g := ordinaryQuotientTarget g
  let eF : (⊤_ C) ⟶ (ordinaryCofiber (C := C)).obj f := ordinaryQuotientZero f
  let eG : (⊤_ C) ⟶ (ordinaryCofiber (C := C)).obj g := ordinaryQuotientZero g
  have hOuter : IsPushout i (terminal.from A) (kB ≫ qG) eG := by
    have h := sq.paste_vert (ordinaryQuotientIsPushout g)
    have hz : z ≫ terminal.from Z = terminal.from A := terminalIsTerminal.hom_ext _ _
    exact hz ▸ h
  have hF : IsPushout i (terminal.from A) qF eF := ordinaryQuotientIsPushout f
  let e : (ordinaryCofiber (C := C)).obj f ≅ (ordinaryCofiber (C := C)).obj g :=
    hF.isoIsPushout B (⊤_ C) hOuter
  let m : (ordinaryCofiber (C := C)).obj f ⟶ (ordinaryCofiber (C := C)).obj g :=
    (ordinaryCofiber (C := C)).map a
  have hm : m = e.hom := by
    have hT : qF ≫ m = kB ≫ qG := ordinaryQuotientTarget_map a
    have hZ : eF ≫ m = eG := ordinaryQuotientZero_map a
    apply hF.hom_ext
    · exact hT.trans
        (hF.inl_isoIsPushout_hom _ _ hOuter).symm
    · exact hZ.trans
        (hF.inr_isoIsPushout_hom _ _ hOuter).symm
  change IsIso m
  exact hm.symm ▸ (inferInstance : IsIso e.hom)

variable [HasZeroObject C] [HasZeroMorphisms C]

omit [HasPushouts C] [HasZeroMorphisms C] in
/-- The original terminal object is zero by the actual original zero-object comparison. -/
theorem terminalIsZero : IsZero (⊤_ C) :=
  (isZero_zero C).of_iso HasZeroObject.zeroIsoTerminal.symm

/-- The actual scalar cofiber compares to the same canonical ordinary quotient. -/
def canonicalQuotientComparison (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (f : Arrow C) :
    (cofiberFunctor S e₀ e₁).obj f ⟶ (ordinaryCofiber (C := C)).obj f :=
  cofiberQuotientComparison S e₀ e₁ f.hom (terminal.from f.left) terminalIsZero
    (ordinaryQuotientTarget f) (ordinaryQuotientZero f) (ordinaryQuotientIsPushout f)

/-- The canonical comparison retains the entire original target leg. -/
@[reassoc]
theorem canonicalQuotientComparison_target (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (f : Arrow C) :
    cofiberTarget S e₀ e₁ f.hom ≫ canonicalQuotientComparison S e₀ e₁ f =
      ordinaryQuotientTarget f :=
  cofiberQuotientComparison_target S e₀ e₁ _ _ _ _ _ _

/-- The canonical comparison collapses the same original scalar cone. -/
@[reassoc]
theorem canonicalQuotientComparison_cone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (f : Arrow C) :
    cofiberCone S e₀ e₁ f.hom ≫ canonicalQuotientComparison S e₀ e₁ f = 0 :=
  cofiberQuotientComparison_cone S e₀ e₁ _ _ _ _ _ _

/-- All original arrow maps retain the exact canonical quotient comparison square. -/
@[reassoc]
theorem canonicalQuotientComparison_naturality (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {f g : Arrow C} (sq : f ⟶ g) :
    (cofiberFunctor S e₀ e₁).map sq ≫ canonicalQuotientComparison S e₀ e₁ g =
      canonicalQuotientComparison S e₀ e₁ f ≫ (ordinaryCofiber (C := C)).map sq := by
  let iF : f.right ⟶ (cofiberFunctor S e₀ e₁).obj f := cofiberTarget S e₀ e₁ f.hom
  let iG : g.right ⟶ (cofiberFunctor S e₀ e₁).obj g := cofiberTarget S e₀ e₁ g.hom
  let qF : (coneFunctor S e₁).obj f.left ⟶ (cofiberFunctor S e₀ e₁).obj f :=
    cofiberCone S e₀ e₁ f.hom
  let qG : (coneFunctor S e₁).obj g.left ⟶ (cofiberFunctor S e₀ e₁).obj g :=
    cofiberCone S e₀ e₁ g.hom
  let cF : (cofiberFunctor S e₀ e₁).obj f ⟶ (ordinaryCofiber (C := C)).obj f :=
    canonicalQuotientComparison S e₀ e₁ f
  let cG : (cofiberFunctor S e₀ e₁).obj g ⟶ (ordinaryCofiber (C := C)).obj g :=
    canonicalQuotientComparison S e₀ e₁ g
  let m : (cofiberFunctor S e₀ e₁).obj f ⟶ (cofiberFunctor S e₀ e₁).obj g :=
    (cofiberFunctor S e₀ e₁).map sq
  let n : (ordinaryCofiber (C := C)).obj f ⟶ (ordinaryCofiber (C := C)).obj g :=
    (ordinaryCofiber (C := C)).map sq
  have hL : iF ≫ m = sq.right ≫ iG := cofiberTarget_map S e₀ e₁ sq
  have hR : qF ≫ m = (coneFunctor S e₁).map sq.left ≫ qG := cofiberCone_map S e₀ e₁ sq
  have hLF : iF ≫ cF = ordinaryQuotientTarget f := canonicalQuotientComparison_target S e₀ e₁ f
  have hLG : iG ≫ cG = ordinaryQuotientTarget g := canonicalQuotientComparison_target S e₀ e₁ g
  have hRF : qF ≫ cF = 0 := canonicalQuotientComparison_cone S e₀ e₁ f
  have hRG : qG ≫ cG = 0 := canonicalQuotientComparison_cone S e₀ e₁ g
  have sqF : IsPushout f.hom ((inclusionNatTrans S e₀ e₁).app f.left) iF qF :=
    cofiberIsPushout S e₀ e₁ f.hom
  apply sqF.hom_ext
  · change iF ≫ (m ≫ cG) = iF ≫ (cF ≫ n)
    rw [← Category.assoc, hL, Category.assoc, hLG,
      ← ordinaryQuotientTarget_map, ← Category.assoc, hLF]
  · change qF ≫ (m ≫ cG) = qF ≫ (cF ≫ n)
    rw [← Category.assoc, hR, Category.assoc, hRG, comp_zero,
      ← Category.assoc, hRF, zero_comp]

/-- The canonical ordinary quotient comparison is a full natural transformation. -/
def canonicalQuotientComparisonNatTrans (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) :
    cofiberFunctor S e₀ e₁ ⟶ ordinaryCofiber (C := C) where
  app := canonicalQuotientComparison S e₀ e₁
  naturality _ _ sq := canonicalQuotientComparison_naturality S e₀ e₁ sq

end CategoryTheory.OriginalScalarCone

namespace CategoryTheory.OriginalScalarCone

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasPushouts C]

/-- The actual cofiber compares to the original target cone by its original two legs. -/
def targetConeComparison (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (f : Arrow C) :
    (cofiberFunctor S e₀ e₁).obj f ⟶ (coneFunctor S e₁).obj f.right :=
  (cofiberIsPushout S e₀ e₁ f.hom).desc ((inclusionNatTrans S e₀ e₁).app f.right)
    ((coneFunctor S e₁).map f.hom) ((inclusionNatTrans S e₀ e₁).naturality f.hom)

/-- The entire original target leg becomes the target cone inclusion. -/
@[reassoc]
theorem targetConeComparison_target (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (f : Arrow C) :
    cofiberTarget S e₀ e₁ f.hom ≫ targetConeComparison S e₀ e₁ f =
      (inclusionNatTrans S e₀ e₁).app f.right :=
  (cofiberIsPushout S e₀ e₁ f.hom).inl_desc _ _ _

/-- The entire original cone leg is the full target cone map of the original source arrow. -/
@[reassoc]
theorem targetConeComparison_cone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S) (f : Arrow C) :
    cofiberCone S e₀ e₁ f.hom ≫ targetConeComparison S e₀ e₁ f =
      (coneFunctor S e₁).map f.hom :=
  (cofiberIsPushout S e₀ e₁ f.hom).inr_desc _ _ _

/-- The actual boundary and suspended arrow factor through the original target cone. -/
theorem boundary_suspension_factors_targetCone (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {Z : C} (hZ : IsZero Z) (f : Arrow C) :
    boundary S e₀ e₁ hZ f ≫ (suspensionFunctor S e₀ e₁ hZ).map f.hom =
      targetConeComparison S e₀ e₁ f ≫ suspensionQuotient S e₀ e₁ hZ f.right := by
  let i : f.right ⟶ (cofiberFunctor S e₀ e₁).obj f := cofiberTarget S e₀ e₁ f.hom
  let q : (coneFunctor S e₁).obj f.left ⟶ (cofiberFunctor S e₀ e₁).obj f :=
    cofiberCone S e₀ e₁ f.hom
  let b : (cofiberFunctor S e₀ e₁).obj f ⟶ (suspensionFunctor S e₀ e₁ hZ).obj f.left :=
    boundary S e₀ e₁ hZ f
  let a : (cofiberFunctor S e₀ e₁).obj f ⟶ (coneFunctor S e₁).obj f.right :=
    targetConeComparison S e₀ e₁ f
  let r := suspensionQuotient S e₀ e₁ hZ f.right
  have sq : IsPushout f.hom ((inclusionNatTrans S e₀ e₁).app f.left) i q :=
    cofiberIsPushout S e₀ e₁ f.hom
  have hI : i ≫ b = 0 := boundary_target S e₀ e₁ hZ f
  have hQ : q ≫ b = suspensionQuotient S e₀ e₁ hZ f.left := boundary_cone S e₀ e₁ hZ f
  have hAI : i ≫ a = (inclusionNatTrans S e₀ e₁).app f.right :=
    targetConeComparison_target S e₀ e₁ f
  have hAQ : q ≫ a = (coneFunctor S e₁).map f.hom :=
    targetConeComparison_cone S e₀ e₁ f
  apply sq.hom_ext
  · change i ≫ (b ≫ _) = i ≫ (a ≫ r)
    rw [← Category.assoc, hI, zero_comp, ← Category.assoc, hAI,
      inclusion_suspensionQuotient]
  · change q ≫ (b ≫ _) = q ≫ (a ≫ r)
    rw [← Category.assoc, hQ, ← Category.assoc, hAQ]
    exact (suspensionQuotient_naturality S e₀ e₁ hZ f.hom).symm

end CategoryTheory.OriginalScalarCone

namespace CategoryTheory.OriginalScalarCone

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasPushouts C]

/-- Every actual map of two caller pushout cocones gives the original commuting cofiber square. -/
theorem originalCallerPushoutCofiber_square
    (S : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ S)
    {A X Z P A' X' Z' P' : C}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (h : IsPushout i z kX kZ) (h' : IsPushout i' z' kX' kZ')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hi : a ≫ i' = i ≫ b) (hz : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ d) (hZ : c ≫ kZ' = kZ ≫ d) :
    (cofiberFunctor S e₀ e₁).map (Arrow.homMk (f := Arrow.mk i) (g := Arrow.mk i') a b hi) ≫
      (cofiberFunctor S e₀ e₁).map (Arrow.homMk (f := Arrow.mk i') (g :=
        Arrow.mk kZ') z' kX' h'.w.symm) =
        (cofiberFunctor S e₀ e₁).map (Arrow.homMk (f := Arrow.mk i) (g :=
          Arrow.mk kZ) z kX h.w.symm) ≫
          (cofiberFunctor S e₀ e₁).map (Arrow.homMk (f := Arrow.mk kZ) (g :=
            Arrow.mk kZ') c d hZ) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply Functor.congr_map
  apply Arrow.hom_ext
  · exact hz
  · exact hX

end CategoryTheory.OriginalScalarCone
