/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.FunctorObjIndex
public import MathlibExt.CategoryTheory.Limits.CofanColimit
public import MathlibExt.CategoryTheory.Presentable.Colimits
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Actual native attaching cofans and successor accessibility

The original attaching-square labels and their source and target coproduct
maps are retained. Generator Arrow-Hom labels keep both original square
maps and the original generator tag. Working-small coproduct presentations
leave the native chosen cofan points unchanged.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe w uC vC uI

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SmallObject

variable {C : Type uC} [Category.{vC} C]
  {I : Type uI} {A B : I → C} (f : ∀ i, A i ⟶ B i)

namespace FunctorObjIndex

/-- The whole original square label is its original tag and actual Arrow morphism. -/
def equivSigmaArrowHom (p : Arrow C) :
    FunctorObjIndex f p.hom ≃ Σ i : I, Arrow.mk (f i) ⟶ p where
  toFun x := ⟨x.i, Arrow.homMk x.t x.b x.w⟩
  invFun x := ⟨x.1, x.2.left, x.2.right, x.2.w⟩
  left_inv x := by cases x; rfl
  right_inv x := by
    rcases x with ⟨i, x⟩
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Arrow.hom_ext <;> rfl

/-- The original tag is retained by the whole Arrow-Hom conversion. -/
@[simp]
theorem equivSigmaArrowHom_apply_i (p : Arrow C) (x : FunctorObjIndex f p.hom) :
    (equivSigmaArrowHom f p x).1 = x.i := rfl

/-- The original top map is retained by the whole Arrow-Hom conversion. -/
@[simp]
theorem equivSigmaArrowHom_apply_left (p : Arrow C) (x : FunctorObjIndex f p.hom) :
    (equivSigmaArrowHom f p x).2.left = x.t := rfl

/-- The original bottom map is retained by the whole Arrow-Hom conversion. -/
@[simp]
theorem equivSigmaArrowHom_apply_right (p : Arrow C) (x : FunctorObjIndex f p.hom) :
    (equivSigmaArrowHom f p x).2.right = x.b := rfl

/-- The inverse conversion retains the original generator tag. -/
@[simp]
theorem equivSigmaArrowHom_symm_apply_i (p : Arrow C) (i : I) (x : Arrow.mk (f i) ⟶ p) :
    ((equivSigmaArrowHom f p).symm ⟨i, x⟩).i = i := rfl

/-- The inverse conversion retains the whole original top map. -/
@[simp]
theorem equivSigmaArrowHom_symm_apply_t (p : Arrow C) (i : I) (x : Arrow.mk (f i) ⟶ p) :
    ((equivSigmaArrowHom f p).symm ⟨i, x⟩).t = x.left := rfl

/-- The inverse conversion retains the whole original bottom map. -/
@[simp]
theorem equivSigmaArrowHom_symm_apply_b (p : Arrow C) (i : I) (x : Arrow.mk (f i) ⟶ p) :
    ((equivSigmaArrowHom f p).symm ⟨i, x⟩).b = x.right := rfl

/-- Original postcomposition agrees with the whole original Arrow-Hom action. -/
theorem equivSigmaArrowHom_postcomp {p q : Arrow C}
    (x : FunctorObjIndex f p.hom) (τ : p ⟶ q) :
    equivSigmaArrowHom f q (x.postcomp τ) =
      ⟨x.i, Arrow.homMk x.t x.b x.w ≫ τ⟩ := by
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Arrow.hom_ext <;> rfl

end FunctorObjIndex

/-- Actual original cofan structures and compact generator Arrows give accessibility. -/
private theorem isCardinalAccessible_of_originalCofans
    (X : I → C) (H : Arrow C ⥤ C)
    (ι : ∀ (p : Arrow C) (x : FunctorObjIndex f p.hom), X x.i ⟶ H.obj p)
    (hmap : ∀ {p q : Arrow C} (τ : p ⟶ q) (x : FunctorObjIndex f p.hom),
      ι p x ≫ H.map τ = ι q (x.postcomp τ))
    (hcofan : ∀ p : Arrow C, IsColimit (Cofan.mk (H.obj p) (ι p)))
    (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ i : I, IsCardinalPresentable (Arrow.mk (f i)) χ] :
    H.IsCardinalAccessible χ := by
  refine { preservesColimitOfShape := fun J _ _ ↦ ?_ }
  refine { preservesColimit := fun {G} ↦
    { preserves := fun {c} hc ↦ ⟨?_⟩ } }
  let labels (i : I) : Arrow C ⥤ Type vC := coyoneda.obj (op (Arrow.mk (f i)))
  let F (i : I) : J ⥤ Type vC := G ⋙ labels i
  let d (i : I) : Cocone (F i) := (labels i).mapCocone c
  have hd (i : I) : IsColimit (d i) := by
    letI : (labels i).IsCardinalAccessible χ :=
      inferInstanceAs (IsCardinalPresentable (Arrow.mk (f i)) χ)
    letI : PreservesColimitsOfShape J (labels i) :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible (labels i) χ J
    exact isColimitOfPreserves (labels i) hc
  let inject (p : Arrow C) (i : I) (a : Arrow.mk (f i) ⟶ p) : X i ⟶ H.obj p :=
    ι p ((FunctorObjIndex.equivSigmaArrowHom f p).symm ⟨i, a⟩)
  have cofan (p : Arrow C) : IsColimit (Cofan.mk (H.obj p)
      (fun a : Σ i : I, Arrow.mk (f i) ⟶ p ↦ inject p a.1 a.2)) :=
    (Cofan.isColimitEquivOfEquiv
      (FunctorObjIndex.equivSigmaArrowHom f p).symm
      (Cofan.mk (H.obj p) (ι p))).1 (hcofan p)
  have hm {j k : J} (u : j ⟶ k) (i : I) (a : (F i).obj j) :
      inject (G.obj j) i a ≫ (G ⋙ H).map u =
        inject (G.obj k) i ((F i).map u a) := by
    exact hmap (G.map u)
      ((FunctorObjIndex.equivSigmaArrowHom f (G.obj j)).symm ⟨i, a⟩)
  have hl (j : J) (i : I) (a : (F i).obj j) :
      inject (G.obj j) i a ≫ (H.mapCocone c).ι.app j =
        inject c.pt i ((d i).ι.app j a) := by
    exact hmap (c.ι.app j)
      ((FunctorObjIndex.equivSigmaArrowHom f (G.obj j)).symm ⟨i, a⟩)
  exact CofanColimit.isColimit X F (G ⋙ H)
    (fun j i a ↦ inject (G.obj j) i a) hm d hd (H.mapCocone c)
    (inject c.pt) (fun j ↦ cofan (G.obj j)) (cofan c.pt) hl

section WorkingSize

variable [Small.{w} I] [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} C]

/-- The literal original source attaching cofan, with its native maps. -/
def sourceCofanFunctor : Arrow C ⥤ C := by
  letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  refine
    { obj := fun p ↦ ∐ functorObjSrcFamily f p.hom
      map := fun τ ↦ functorMapSrc f τ
      map_id := ?_
      map_comp := ?_ }
  · intro p
    change Sigma.map' (f := functorObjSrcFamily f p.hom)
        (g := functorObjSrcFamily f p.hom)
        (fun x : FunctorObjIndex f p.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ 𝟙 p.left) (x.b ≫ 𝟙 p.right) (by simp))
        (fun _ ↦ 𝟙 _) = 𝟙 (∐ functorObjSrcFamily f p.hom)
    apply Sigma.hom_ext
    rintro ⟨i, t, b, h⟩
    simp only [Sigma.ι_comp_map', Category.id_comp, Category.comp_id]
    congr 1
    simp only [Category.comp_id]
  · intro p q r τ σ
    change Sigma.map' (f := functorObjSrcFamily f r.hom)
        (g := functorObjSrcFamily f p.hom)
        (fun x : FunctorObjIndex f p.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ (τ ≫ σ).left) (x.b ≫ (τ ≫ σ).right)
            (by simp)) (fun _ ↦ 𝟙 _) =
      Sigma.map' (f := functorObjSrcFamily f q.hom)
        (g := functorObjSrcFamily f p.hom)
        (fun x : FunctorObjIndex f p.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ (τ).left) (x.b ≫ (τ).right) (by simp)) (fun _ ↦ 𝟙 _) ≫
      Sigma.map' (f := functorObjSrcFamily f r.hom)
        (g := functorObjSrcFamily f q.hom)
        (fun x : FunctorObjIndex f q.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ (σ).left) (x.b ≫ (σ).right) (by simp)) (fun _ ↦ 𝟙 _)
    apply Sigma.hom_ext
    rintro ⟨i, t, b, h⟩
    simp only [Sigma.ι_comp_map', Sigma.ι_comp_map'_assoc,
      Category.id_comp, Arrow.comp_left, Arrow.comp_right]
    congr 1
    simp only [Category.assoc]

/-- The literal original target attaching cofan, with its native maps. -/
def targetCofanFunctor : Arrow C ⥤ C := by
  letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  refine
    { obj := fun p ↦ ∐ functorObjTgtFamily f p.hom
      map := fun τ ↦ functorMapTgt f τ
      map_id := ?_
      map_comp := ?_ }
  · intro p
    change Sigma.map' (f := functorObjTgtFamily f p.hom)
        (g := functorObjTgtFamily f p.hom)
        (fun x : FunctorObjIndex f p.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ 𝟙 p.left) (x.b ≫ 𝟙 p.right) (by simp))
        (fun _ ↦ 𝟙 _) = 𝟙 (∐ functorObjTgtFamily f p.hom)
    apply Sigma.hom_ext
    rintro ⟨i, t, b, h⟩
    simp only [Sigma.ι_comp_map', Category.id_comp, Category.comp_id]
    congr 1
    simp only [Category.comp_id]
  · intro p q r τ σ
    change Sigma.map' (f := functorObjTgtFamily f r.hom)
        (g := functorObjTgtFamily f p.hom)
        (fun x : FunctorObjIndex f p.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ (τ ≫ σ).left) (x.b ≫ (τ ≫ σ).right)
            (by simp)) (fun _ ↦ 𝟙 _) =
      Sigma.map' (f := functorObjTgtFamily f q.hom)
        (g := functorObjTgtFamily f p.hom)
        (fun x : FunctorObjIndex f p.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ (τ).left) (x.b ≫ (τ).right) (by simp)) (fun _ ↦ 𝟙 _) ≫
      Sigma.map' (f := functorObjTgtFamily f r.hom)
        (g := functorObjTgtFamily f q.hom)
        (fun x : FunctorObjIndex f q.hom ↦
          FunctorObjIndex.mk x.i (x.t ≫ (σ).left) (x.b ≫ (σ).right) (by simp)) (fun _ ↦ 𝟙 _)
    apply Sigma.hom_ext
    rintro ⟨i, t, b, h⟩
    simp only [Sigma.ι_comp_map', Sigma.ι_comp_map'_assoc,
      Category.id_comp, Arrow.comp_left, Arrow.comp_right]
    congr 1
    simp only [Category.assoc]

/-- Both original endpoint bounds make the SAME native source cofan accessible. -/
theorem sourceCofanFunctor_isCardinalAccessible
    (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ i : I, IsCardinalPresentable (A i) χ]
    [∀ i : I, IsCardinalPresentable (B i) χ] :
    (sourceCofanFunctor f).IsCardinalAccessible χ := by
  let {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  let (i : I) : IsCardinalPresentable (Arrow.mk (f i)) χ :=
    Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) (κ := χ) (f i)
  let inject (p : Arrow C) (x : FunctorObjIndex f p.hom) :
      A x.i ⟶ (sourceCofanFunctor f).obj p := Sigma.ι (functorObjSrcFamily f p.hom) x
  have hm {p q : Arrow C} (τ : p ⟶ q) (x : FunctorObjIndex f p.hom) :
      inject p x ≫ (sourceCofanFunctor f).map τ = inject q (x.postcomp τ) := by
    rcases x with ⟨i, t, b, h⟩
    change Sigma.ι (functorObjSrcFamily f p.hom) (FunctorObjIndex.mk i t b h) ≫
        functorMapSrc f τ =
      Sigma.ι (functorObjSrcFamily f q.hom) ((FunctorObjIndex.mk i t b h).postcomp τ)
    exact ι_functorMapSrc f τ i t b h (b ≫ τ.right) rfl (t ≫ τ.left) rfl
  have hp (p : Arrow C) :
      IsColimit (Cofan.mk ((sourceCofanFunctor f).obj p) (inject p)) := by
    change IsColimit (Cofan.mk (∐ functorObjSrcFamily f p.hom)
      (Sigma.ι (functorObjSrcFamily f p.hom)))
    exact coproductIsCoproduct _
  exact isCardinalAccessible_of_originalCofans f A (sourceCofanFunctor f)
    inject hm hp χ

/-- Both original endpoint bounds make the SAME native target cofan accessible. -/
theorem targetCofanFunctor_isCardinalAccessible
    (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ i : I, IsCardinalPresentable (A i) χ]
    [∀ i : I, IsCardinalPresentable (B i) χ] :
    (targetCofanFunctor f).IsCardinalAccessible χ := by
  let {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  let (i : I) : IsCardinalPresentable (Arrow.mk (f i)) χ :=
    Comma.isCardinalPresentable_mk (F₁ := 𝟭 C) (F₂ := 𝟭 C) (κ := χ) (f i)
  let inject (p : Arrow C) (x : FunctorObjIndex f p.hom) :
      B x.i ⟶ (targetCofanFunctor f).obj p := Sigma.ι (functorObjTgtFamily f p.hom) x
  have hm {p q : Arrow C} (τ : p ⟶ q) (x : FunctorObjIndex f p.hom) :
      inject p x ≫ (targetCofanFunctor f).map τ = inject q (x.postcomp τ) := by
    rcases x with ⟨i, t, b, h⟩
    change Sigma.ι (functorObjTgtFamily f p.hom) (FunctorObjIndex.mk i t b h) ≫
        functorMapTgt f τ =
      Sigma.ι (functorObjTgtFamily f q.hom) ((FunctorObjIndex.mk i t b h).postcomp τ)
    exact ι_functorMapTgt f τ i t b h (b ≫ τ.right) rfl (t ≫ τ.left) rfl
  have hp (p : Arrow C) :
      IsColimit (Cofan.mk ((targetCofanFunctor f).obj p) (inject p)) := by
    change IsColimit (Cofan.mk (∐ functorObjTgtFamily f p.hom)
      (Sigma.ι (functorObjTgtFamily f p.hom)))
    exact coproductIsCoproduct _
  exact isCardinalAccessible_of_originalCofans f B (targetCofanFunctor f)
    inject hm hp χ

/-- The original top attaching map is a whole natural transformation. -/
def sourceCofanTop : sourceCofanFunctor f ⟶ Arrow.leftFunc := by
  letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  refine { app := fun p ↦ functorObjTop f p.hom, naturality := ?_ }
  intro p q τ
  change functorMapSrc f τ ≫ functorObjTop f q.hom = functorObjTop f p.hom ≫ τ.left
  exact functorMapSrc_functorObjTop f τ

/-- The original coefficient maps form the whole native left transformation. -/
def sourceCofanLeft : sourceCofanFunctor f ⟶ targetCofanFunctor f := by
  letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  refine { app := fun p ↦ functorObjLeft f p.hom, naturality := ?_ }
  intro p q τ
  change functorMapSrc f τ ≫ functorObjLeft f q.hom =
    functorObjLeft f p.hom ≫ functorMapTgt f τ
  exact (functorMap_comm f τ).symm

/-- The actual native successor left point, with its two original attaching legs. -/
def successorPushoutCocone : PushoutCocone (sourceCofanTop f) (sourceCofanLeft f) := by
  letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  letI : HasPushouts C := inferInstance
  let L : Arrow C ⥤ C := SmallObject.functor f ⋙ Arrow.leftFunc
  let ι : Arrow.leftFunc ⟶ L :=
    { app := fun p ↦ ιFunctorObj f p.hom
      naturality := by
        intro p q τ
        change τ.left ≫ ιFunctorObj f q.hom = ιFunctorObj f p.hom ≫ functorMap f τ
        exact (ιFunctorObj_naturality f τ).symm }
  let ρ : targetCofanFunctor f ⟶ L :=
    { app := fun p ↦ ρFunctorObj f p.hom
      naturality := by
        intro p q τ
        change functorMapTgt f τ ≫ ρFunctorObj f q.hom =
          ρFunctorObj f p.hom ≫ functorMap f τ
        simp [ρFunctorObj, functorMap] }
  refine PushoutCocone.mk ι ρ ?_
  ext p
  change functorObjTop f p.hom ≫ ιFunctorObj f p.hom =
    functorObjLeft f p.hom ≫ ρFunctorObj f p.hom
  exact functorObj_comm f p.hom

/-- Pointwise native pushouts prove the SAME whole successor cocone colimiting. -/
def successorPushoutCoconeIsColimit : IsColimit (successorPushoutCocone f) := by
  letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  letI : HasPushouts C := inferInstance
  apply evaluationJointlyReflectsColimits (successorPushoutCocone f)
  intro p
  let t := ((evaluation (Arrow C) C).obj p).mapCocone (successorPushoutCocone f)
  let e := diagramIsoSpan
    (span (sourceCofanTop f) (sourceCofanLeft f) ⋙ (evaluation (Arrow C) C).obj p)
  refine (IsColimit.precomposeInvEquiv e t).1 ?_
  exact IsColimit.ofIsoColimit (functorObj_isPushout f p.hom).isColimit
    (PushoutCocone.isoMk t).symm

/-- The pushout cocone point is the literal original native successor left functor. -/
theorem successorPushoutCocone_pt :
    letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
      hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
    letI : HasPushouts C := inferInstance
    (successorPushoutCocone f).pt = SmallObject.functor f ⋙ Arrow.leftFunc := rfl

/-- The first whole pushout leg retains every original native attaching inclusion. -/
theorem successorPushoutCocone_inl_app (p : Arrow C) :
    letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
      hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
    letI : HasPushouts C := inferInstance
    (successorPushoutCocone f).inl.app p = ιFunctorObj f p.hom := rfl

/-- The second whole pushout leg retains every original native coefficient inclusion. -/
theorem successorPushoutCocone_inr_app (p : Arrow C) :
    letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
      hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
    letI : HasPushouts C := inferInstance
    (successorPushoutCocone f).inr.app p = ρFunctorObj f p.hom := rfl

/-- Both original endpoint bounds make the SAME complete native Arrow successor accessible. -/
theorem functor_isCardinalAccessible
    (χ : Cardinal.{w}) [Fact χ.IsRegular]
    [∀ i : I, IsCardinalPresentable (A i) χ]
    [∀ i : I, IsCardinalPresentable (B i) χ] :
    letI {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
      hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
    letI : HasPushouts C := inferInstance
    (SmallObject.functor f).IsCardinalAccessible χ := by
  let {X S : C} (π : X ⟶ S) :
      HasColimitsOfShape (Discrete (FunctorObjIndex f π)) C :=
    hasCoproductsOfShape_of_small.{w} (C := C) (β := FunctorObjIndex f π)
  let : HasPushouts C := inferInstance
  let : (sourceCofanFunctor f).IsCardinalAccessible χ :=
    sourceCofanFunctor_isCardinalAccessible f χ
  let : (targetCofanFunctor f).IsCardinalAccessible χ :=
    targetCofanFunctor_isCardinalAccessible f χ
  let : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs (Functor.IsCardinalAccessible (Comma.fst (𝟭 C) (𝟭 C)) χ)
  let : (Arrow.rightFunc : Arrow C ⥤ C).IsCardinalAccessible χ :=
    inferInstanceAs (Functor.IsCardinalAccessible (Comma.snd (𝟭 C) (𝟭 C)) χ)
  let (j : WalkingSpan) :
      ((span (sourceCofanTop f) (sourceCofanLeft f)).obj j).IsCardinalAccessible χ := by
    rcases j with _ | (_ | _)
    · exact inferInstanceAs ((sourceCofanFunctor f).IsCardinalAccessible χ)
    · exact inferInstanceAs ((Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible χ)
    · exact inferInstanceAs ((targetCofanFunctor f).IsCardinalAccessible χ)
  let : (SmallObject.functor f ⋙ Arrow.leftFunc).IsCardinalAccessible χ :=
    Functor.isCardinalAccessible_of_isColimit χ
      (span (sourceCofanTop f) (sourceCofanLeft f))
      (successorPushoutCocone f) (successorPushoutCoconeIsColimit f)
  refine { preservesColimitOfShape := fun J _ _ ↦ ?_ }
  let : PreservesColimitsOfShape J (SmallObject.functor f ⋙ Arrow.leftFunc) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (SmallObject.functor f ⋙ Arrow.leftFunc) χ J
  let : PreservesColimitsOfShape J (Arrow.rightFunc : Arrow C ⥤ C) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible
      (Arrow.rightFunc : Arrow C ⥤ C) χ J
  refine { preservesColimit := fun {G} ↦
    { preserves := fun {c} hc ↦ ⟨?_⟩ } }
  have hleft :
      IsColimit (Arrow.leftFunc.mapCocone ((SmallObject.functor f).mapCocone c)) :=
    isColimitOfPreserves (SmallObject.functor f ⋙ Arrow.leftFunc) hc
  have hright :
      IsColimit (Arrow.rightFunc.mapCocone ((SmallObject.functor f).mapCocone c)) := by
    change IsColimit (Arrow.rightFunc.mapCocone c)
    exact isColimitOfPreserves Arrow.rightFunc hc
  exact Comma.fstSndJointlyReflectColimit hleft hright

end WorkingSize

end CategoryTheory.SmallObject
