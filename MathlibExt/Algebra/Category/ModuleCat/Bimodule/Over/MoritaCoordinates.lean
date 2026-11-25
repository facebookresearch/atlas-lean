/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.Over.MoritaReturn

/-!
# Coordinates of composite bimodule tensor functors

The left, right and ground scalar actions are recovered from the
enveloping-algebra action and the supplied ground map. These identifications
compare the balanced tensor objects with independent carrier universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe u r s p q v a

namespace ModuleCat.Bimodule.Over.Morita

variable (k : Type u) [CommRing k]
  (R : Type r) [Ring R] [Algebra k R] (S : Type s) [Ring S] [Algebra k S]
  (P : Type p) [AddCommGroup P] [Module k P]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [IsScalarTower k R P] [IsScalarTower k Sᵐᵒᵖ P]
  (Q : Type q) [AddCommGroup Q] [Module k Q]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q]

/-- The actual outer pure tensor class in the composite native functor. -/
def returnOuterMk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) (p₀ : P)
    (c : tensorObj k R S P Q X) (q₁ : Q) :
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X :=
  tensorMk k S R Q P (tensorObj k R S P Q X) p₀ c q₁

/-- The original ordered pure coefficients determine an additive map on the native composite. -/
theorem returnHom_ext (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    {C' : Type*} [AddCommMonoid C']
    {f g : ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X →+ C'}
    (h : letI := ModuleCat.Bimodule.Over.groundModule k R X
      letI := ModuleCat.Bimodule.Over.leftModule k R X
      letI := ModuleCat.Bimodule.Over.rightModule k R X
      letI := ModuleCat.Bimodule.Over.leftTower k R X
      letI := ModuleCat.Bimodule.Over.rightTower k R X
      letI := ModuleCat.Bimodule.Over.commute k R X
      letI := TensorProduct.Balanced.rightModule k R R Q X
      ∀ (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q),
        f (returnOuterMk k R S P Q X p₀
          (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q X) P
              (TensorProduct.Balanced.mk k R Q X q₀ x) p₁) q₁) =
        g (returnOuterMk k R S P Q X p₀
          (TensorProduct.Balanced.mk k R (TensorProduct.Balanced k R Q X) P
              (TensorProduct.Balanced.mk k R Q X q₀ x) p₁) q₁)) :
    f = g := by
  let := ModuleCat.Bimodule.Over.groundModule k R X
  let := ModuleCat.Bimodule.Over.leftModule k R X
  let := ModuleCat.Bimodule.Over.rightModule k R X
  let := ModuleCat.Bimodule.Over.leftTower k R X
  let := ModuleCat.Bimodule.Over.rightTower k R X
  let := ModuleCat.Bimodule.Over.commute k R X
  let := TensorProduct.Balanced.rightModule k R R Q X
  let A := tensorObj k R S P Q X
  let := ModuleCat.Bimodule.Over.groundModule k S A
  let := ModuleCat.Bimodule.Over.leftModule k S A
  let := ModuleCat.Bimodule.Over.rightModule k S A
  let := ModuleCat.Bimodule.Over.leftTower k S A
  let := ModuleCat.Bimodule.Over.rightTower k S A
  let := ModuleCat.Bimodule.Over.commute k S A
  let := TensorProduct.Balanced.rightModule k S S P A
  let B := TensorProduct.Balanced k S P A
  apply TensorProduct.Balanced.addHom_ext k S B Q
  intro b q₁
  have hb : f.comp (((TensorProduct.Balanced.mk k S B Q).flip q₁).toAddMonoidHom) =
      g.comp (((TensorProduct.Balanced.mk k S B Q).flip q₁).toAddMonoidHom) := by
    apply TensorProduct.Balanced.addHom_ext k S P A
    intro p₀ a
    have ha : (f.comp (((TensorProduct.Balanced.mk k S B Q).flip q₁).toAddMonoidHom)).comp
        ((TensorProduct.Balanced.mk k S P A p₀).toAddMonoidHom) =
      (g.comp (((TensorProduct.Balanced.mk k S B Q).flip q₁).toAddMonoidHom)).comp
        ((TensorProduct.Balanced.mk k S P A p₀).toAddMonoidHom) := by
      apply TensorProduct.Balanced.Morita.coefficientHom_ext k R Q X P
      intro q₀ x p₁
      exact h p₀ q₀ x p₁ q₁
    exact DFunLike.congr_fun ha a
  exact DFunLike.congr_fun hb b

/-- Values of the second tensor map on arbitrary native coefficient objects. -/
def outerTensorMapValue {A B : ModuleCat.{a} (S ⊗[k] Sᵐᵒᵖ)} (g : A ⟶ B) :
    P → A → Q → tensorObj k S R Q P B := by
  let A' := tensorObj k S R Q P A
  let B' := tensorObj k S R Q P B
  let L : A' →ₗ[R ⊗[k] Rᵐᵒᵖ] B' :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A' B' (tensorMap k S R Q P g)
  exact fun p₀ c q₁ => L (tensorMk k S R Q P A p₀ c q₁)

/-- The original middle-map formula on arbitrary native coefficient objects. -/
def outerTensorMappedValue {A B : ModuleCat.{a} (S ⊗[k] Sᵐᵒᵖ)} (g : A ⟶ B) :
    P → A → Q → tensorObj k S R Q P B := by
  let L : A →ₗ[S ⊗[k] Sᵐᵒᵖ] B :=
    @ModuleCat.Hom.hom (S ⊗[k] Sᵐᵒᵖ) _ A B g
  exact fun p₀ c q₁ => tensorMk k S R Q P B p₀ (L c) q₁

/-- The tensor-map characteristic as a generic three-argument function equality. -/
theorem outerTensorMapValue_eq {A B : ModuleCat.{a} (S ⊗[k] Sᵐᵒᵖ)} (g : A ⟶ B) :
    outerTensorMapValue k R S P Q g = outerTensorMappedValue k R S P Q g := by
  funext p₀ c q₁
  exact tensorMap_mk k S R Q P (X := A) (Y := B) g p₀ c q₁

/-- The original intermediate native carrier, named independently of its module fields. -/
def returnIntermediateCarrier (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    Type (max p q v) :=
  (tensorObj k R S P Q X).carrier

/-- The original composite native carrier, with the same stored actions. -/
def returnCompositeCarrier (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    Type (max p q v) :=
  (((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X).carrier

/-- Values of the actual composite map on the original outer pure points. -/
def returnOuterMapValue {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      returnCompositeCarrier k R S P Q Y := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let A : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj X
  let B : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj Y
  let g : A ⟶ B := F.map f
  exact outerTensorMapValue k R S P Q (A := A) (B := B) g

/-- The same outer factors with the original first tensor map applied to the middle point. -/
def returnOuterMappedValue {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      returnCompositeCarrier k R S P Q Y := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let A : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj X
  let B : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj Y
  let g : A ⟶ B := F.map f
  exact outerTensorMappedValue k R S P Q (A := A) (B := B) g

/-- The actual composite morphism is the second native map of the actual first map. -/
theorem returnComposite_map
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
        ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
    let G : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) ⥤
        ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := tensorFunctor k S R Q P
    (F ⋙ G).map f = tensorMap k S R Q P (F.map f) := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let G : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := tensorFunctor k S R Q P
  exact Functor.comp_map F G f

/-- The original composite map and the middle-map formula agree as typed value functions. -/
theorem returnOuterMapValue_eq
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnOuterMapValue k R S P Q f = returnOuterMappedValue k R S P Q f := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let A : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj X
  let B : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj Y
  let g : A ⟶ B := F.map f
  exact outerTensorMapValue_eq k R S P Q (A := A) (B := B) g

/-- The actual composite map preserves its outer factors and applies the first tensor map inside. -/
@[simp]
theorem returnOuterMap_mk {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y)
    (p₀ : P) (c : returnIntermediateCarrier k R S P Q X) (q₁ : Q) :
    returnOuterMapValue k R S P Q f p₀ c q₁ =
      returnOuterMappedValue k R S P Q f p₀ c q₁ :=
  congrFun (congrFun (congrFun (returnOuterMapValue_eq k R S P Q f) p₀) c) q₁

include P Q in
/-- The earned identity-coordinate comparison together with its original pure getter. -/
def returnCoordinateData (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    {e : ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X ≅
        rawReturnObject k R S P Q X //
      ∀ (p₀ : P) (c : tensorObj k R S P Q X) (q₁ : Q),
        e.hom.hom (returnOuterMk k R S P Q X p₀ c q₁) =
          rawReturnOuterMk k R S P Q X p₀ c q₁} := by
  letI := ModuleCat.Bimodule.Over.groundModule k R X
  letI := ModuleCat.Bimodule.Over.leftModule k R X
  letI := ModuleCat.Bimodule.Over.rightModule k R X
  letI := ModuleCat.Bimodule.Over.leftTower k R X
  letI := ModuleCat.Bimodule.Over.rightTower k R X
  letI := ModuleCat.Bimodule.Over.commute k R X
  let C := TensorProduct.Balanced.Morita.coefficientTensor k R Q X P
  let A := tensorObj k R S P Q X
  let z₁ : Module k C := inferInstance
  let z₀ : Module k C := ModuleCat.Bimodule.Over.groundModule k S A
  let l₁ : Module S C := TensorProduct.Balanced.Morita.coefficientLeftModule k R S Q X P
  let r₁ : Module Sᵐᵒᵖ C := TensorProduct.Balanced.Morita.coefficientRightModule k R S Q X P
  let l₀ : Module S C := ModuleCat.Bimodule.Over.leftModule k S A
  let r₀ : Module Sᵐᵒᵖ C := ModuleCat.Bimodule.Over.rightModule k S A
  let c₁ : (letI := z₁; letI := l₁; letI := r₁; SMulCommClass S Sᵐᵒᵖ C) := by
    let := z₁
    let := l₁
    let := r₁
    exact TensorProduct.Balanced.Morita.coefficientActionsComm k R S Q X P
  let t₁ : @IsScalarTower k S C
      (Algebra.toModule : Module k S).toSMul l₁.toSMul z₁.toSMul := by
    let := z₁
    let := l₁
    exact TensorProduct.Balanced.Morita.coefficientLeftTower k R S Q X P
  let u₁ : @IsScalarTower k Sᵐᵒᵖ C
      (Algebra.toModule : Module k Sᵐᵒᵖ).toSMul r₁.toSMul z₁.toSMul := by
    let := z₁
    let := r₁
    exact TensorProduct.Balanced.Morita.coefficientRightTower k R S Q X P
  let c₀ : (letI := z₀; letI := l₀; letI := r₀; SMulCommClass S Sᵐᵒᵖ C) :=
    ModuleCat.Bimodule.Over.commute k S A
  let t₀ : @IsScalarTower k S C
      (Algebra.toModule : Module k S).toSMul l₀.toSMul z₀.toSMul :=
    ModuleCat.Bimodule.Over.leftTower k S A
  let u₀ : @IsScalarTower k Sᵐᵒᵖ C
      (Algebra.toModule : Module k Sᵐᵒᵖ).toSMul r₀.toSMul z₀.toSMul :=
    ModuleCat.Bimodule.Over.rightTower k S A
  have hz : z₀ = z₁ := tensorObject_groundModule k R S P Q X
  have hl : l₀ = l₁ := tensorObject_leftModule k R S P Q X
  have hr : r₀ = r₁ := tensorObject_rightModule k R S P Q X
  let dP : Module k P := inferInstance
  let rP : Module Sᵐᵒᵖ P := inferInstance
  let dQ : Module k Q := inferInstance
  let lQ : Module S Q := inferInstance
  let eC :
      @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _
        C C _ _ z₀ z₁ :=
    @AddEquiv.toLinearEquiv k C C _ _ _ z₀ z₁ (AddEquiv.refl C) (by
      intro a x
      change z₀.smul a x = z₁.smul a x
      exact congrArg (fun z : Module k C => z.smul a x) hz)
  have eC_apply (x : C) : eC x = x := rfl
  have eCS (s : S) (x : C) :
      eC (l₀.smul s x) = l₁.smul s (eC x) := by
    have h := congrArg (fun l : Module S C => l.smul s x) hl
    simpa only [eC_apply] using h
  have eCR (s : Sᵐᵒᵖ) (x : C) :
      eC (r₀.smul s x) = r₁.smul s (eC x) := by
    have h := congrArg (fun r : Module Sᵐᵒᵖ C => r.smul s x) hr
    simpa only [eC_apply] using h

  let eCinv :
      @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _
        C C _ _ z₁ z₀ :=
    @AddEquiv.toLinearEquiv k C C _ _ _ z₁ z₀ (AddEquiv.refl C) (by
      intro a x
      change z₁.smul a x = z₀.smul a x
      exact congrArg (fun z : Module k C => z.smul a x) hz.symm)
  have eCinv_apply (x : C) : eCinv x = x := rfl
  have eCSinv (s : S) (x : C) :
      eCinv (l₁.smul s x) = l₀.smul s (eCinv x) := by
    have h := (congrArg (fun l : Module S C => l.smul s x) hl).symm
    simpa only [eCinv_apply] using h
  have eCRinv (s : Sᵐᵒᵖ) (x : C) :
      eCinv (r₁.smul s x) = r₀.smul s (eCinv x) := by
    have h := (congrArg (fun r : Module Sᵐᵒᵖ C => r.smul s x) hr).symm
    simpa only [eCinv_apply] using h

  letI : Module k C := z₀
  letI : Module S C := l₀
  letI : Module Sᵐᵒᵖ C := r₀
  letI := c₀
  letI := t₀
  letI := u₀
  let eEnv₀ : Module (S ⊗[k] Sᵐᵒᵖ) C := TensorProduct.Algebra.module
  let T₀ : Type (max p q v) := TensorProduct.Balanced.Morita.coefficientTensor k S P C Q
  let dEnv₀ : Module (R ⊗[k] Rᵐᵒᵖ) T₀ :=
    TensorProduct.Balanced.Morita.coefficientModule k S R P C Q
  let m₀ := TensorProduct.Balanced.mk k S P C
  letI := TensorProduct.Balanced.rightModule k S S P C
  let n₀ := TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P C) Q
  let point₀ : P → C → Q → T₀ := fun p₀ x q₁ => n₀ (m₀ p₀ x) q₁

  letI : Module k C := z₁
  letI : Module S C := l₁
  letI : Module Sᵐᵒᵖ C := r₁
  letI := c₁
  letI := t₁
  letI := u₁
  let eEnv₁ : Module (S ⊗[k] Sᵐᵒᵖ) C := TensorProduct.Algebra.module
  let T₁ : Type (max p q v) := TensorProduct.Balanced.Morita.coefficientTensor k S P C Q
  let dEnv₁ : Module (R ⊗[k] Rᵐᵒᵖ) T₁ :=
    TensorProduct.Balanced.Morita.coefficientModule k S R P C Q
  let m₁ := TensorProduct.Balanced.mk k S P C
  letI := TensorProduct.Balanced.rightModule k S S P C
  let n₁ := TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P C) Q
  let point₁ : P → C → Q → T₁ := fun p₀ x q₁ => n₁ (m₁ p₀ x) q₁

  let L₀₁ :
      @LinearMap (S ⊗[k] Sᵐᵒᵖ) (S ⊗[k] Sᵐᵒᵖ) _ _
        (RingHom.id (S ⊗[k] Sᵐᵒᵖ)) C C _ _ eEnv₀ eEnv₁ :=
    @TensorProduct.Algebra.ofLinearMap k _ S Sᵐᵒᵖ _ _ _ _
      C C _ _ z₀ z₁ l₀ l₁ r₀ r₁ t₀ t₁ u₀ u₁ c₀ c₁
      (@LinearEquiv.toLinearMap k k _ _ (RingHom.id k) (RingHom.id k) _ _
        C C _ _ z₀ z₁ eC) eCS eCR
  let L₁₀ :
      @LinearMap (S ⊗[k] Sᵐᵒᵖ) (S ⊗[k] Sᵐᵒᵖ) _ _
        (RingHom.id (S ⊗[k] Sᵐᵒᵖ)) C C _ _ eEnv₁ eEnv₀ :=
    @TensorProduct.Algebra.ofLinearMap k _ S Sᵐᵒᵖ _ _ _ _
      C C _ _ z₁ z₀ l₁ l₀ r₁ r₀ t₁ t₀ u₁ u₀ c₁ c₀
      (@LinearEquiv.toLinearMap k k _ _ (RingHom.id k) (RingHom.id k) _ _
        C C _ _ z₁ z₀ eCinv) eCSinv eCRinv
  have hL₀₁ (x : C) : L₀₁ x = x := rfl
  have hL₁₀ (x : C) : L₁₀ x = x := rfl
  let nativeCoefficientData
      {M₀ M₁ : Type (max p q v)}
      [g0 : AddCommGroup M₀] [g1 : AddCommGroup M₁]
      [k0 : Module k M₀] [k1 : Module k M₁]
      [l0 : Module S M₀] [l1 : Module S M₁]
      [r0 : Module Sᵐᵒᵖ M₀] [r1 : Module Sᵐᵒᵖ M₁]
      [c0 : SMulCommClass S Sᵐᵒᵖ M₀] [c1 : SMulCommClass S Sᵐᵒᵖ M₁]
      [t0 : IsScalarTower k S M₀] [t1 : IsScalarTower k S M₁]
      [u0 : IsScalarTower k Sᵐᵒᵖ M₀] [u1 : IsScalarTower k Sᵐᵒᵖ M₁]
      (f : letI : Module (S ⊗[k] Sᵐᵒᵖ) M₀ := TensorProduct.Algebra.module
        letI : Module (S ⊗[k] Sᵐᵒᵖ) M₁ := TensorProduct.Algebra.module
        M₀ →ₗ[S ⊗[k] Sᵐᵒᵖ] M₁) :
      {h : (letI := TensorProduct.Balanced.Morita.coefficientModule k S R P M₀ Q
          letI := TensorProduct.Balanced.Morita.coefficientModule k S R P M₁ Q
          TensorProduct.Balanced.Morita.coefficientTensor k S P M₀ Q →ₗ[R ⊗[k] Rᵐᵒᵖ]
            TensorProduct.Balanced.Morita.coefficientTensor k S P M₁ Q) //
        letI := TensorProduct.Balanced.rightModule k S S P M₀
        letI := TensorProduct.Balanced.rightModule k S S P M₁
        ∀ (p₀ : P) (x : M₀) (q₁ : Q),
          h (TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P M₀) Q
              (TensorProduct.Balanced.mk k S P M₀ p₀ x) q₁) =
            TensorProduct.Balanced.mk k S (TensorProduct.Balanced k S P M₁) Q
              (TensorProduct.Balanced.mk k S P M₁ p₀ (f x)) q₁} := by
    refine ⟨TensorProduct.Balanced.Morita.coefficientMap
      (k := k) (R := S) (S := R) (Q := P) (M := M₀) (N := M₁) (P := Q) f, ?_⟩
    intro p₀ x q₁
    exact TensorProduct.Balanced.Morita.coefficientMap_mk
      (k := k) (R := S) (S := R) (Q := P) (M := M₀) (N := M₁) (P := Q)
      f p₀ x q₁
  let D₀₁ := nativeCoefficientData (M₀ := C) (M₁ := C)
    (g0 := inferInstance) (g1 := inferInstance)
    (k0 := z₀) (k1 := z₁) (l0 := l₀) (l1 := l₁) (r0 := r₀) (r1 := r₁)
    (c0 := c₀) (c1 := c₁) (t0 := t₀) (t1 := t₁) (u0 := u₀) (u1 := u₁) L₀₁
  let D₁₀ := nativeCoefficientData (M₀ := C) (M₁ := C)
    (g0 := inferInstance) (g1 := inferInstance)
    (k0 := z₁) (k1 := z₀) (l0 := l₁) (l1 := l₀) (r0 := r₁) (r1 := r₀)
    (c0 := c₁) (c1 := c₀) (t0 := t₁) (t1 := t₀) (u0 := u₁) (u1 := u₀) L₁₀
  let F :
      @LinearMap (R ⊗[k] Rᵐᵒᵖ) (R ⊗[k] Rᵐᵒᵖ) _ _
        (RingHom.id (R ⊗[k] Rᵐᵒᵖ)) T₀ T₁ _ _ dEnv₀ dEnv₁ := D₀₁.1
  let G :
      @LinearMap (R ⊗[k] Rᵐᵒᵖ) (R ⊗[k] Rᵐᵒᵖ) _ _
        (RingHom.id (R ⊗[k] Rᵐᵒᵖ)) T₁ T₀ _ _ dEnv₁ dEnv₀ := D₁₀.1
  have hF (p₀ : P) (x : C) (q₁ : Q) :
      F (point₀ p₀ x q₁) = point₁ p₀ x q₁ := by
    have h := D₀₁.2 p₀ x q₁
    exact h.trans (congrArg (fun y : C => point₁ p₀ y q₁) (hL₀₁ x))
  have hG (p₀ : P) (x : C) (q₁ : Q) :
      G (point₁ p₀ x q₁) = point₀ p₀ x q₁ := by
    have h := D₁₀.2 p₀ x q₁
    exact h.trans (congrArg (fun y : C => point₀ p₀ y q₁) (hL₁₀ x))

  let O₀ : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) :=
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X
  let O₁ : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) := rawReturnObject k R S P Q X
  let e : O₀ ≅ O₁ :=
    { hom := @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ O₀.carrier O₁.carrier
        O₀.isAddCommGroup O₀.isModule O₁.isAddCommGroup O₁.isModule F
      inv := @ModuleCat.ofHom (R ⊗[k] Rᵐᵒᵖ) _ O₁.carrier O₀.carrier
        O₁.isAddCommGroup O₁.isModule O₀.isAddCommGroup O₀.isModule G
      hom_inv_id := by
        apply ModuleCat.Hom.ext
        apply LinearMap.toAddMonoidHom_injective
        let : Module k C := z₀
        let : Module S C := l₀
        let : Module Sᵐᵒᵖ C := r₀
        let := c₀
        let := t₀
        let := u₀
        apply TensorProduct.Balanced.Morita.coefficientHom_ext k S P C Q
        intro p₀ x q₁
        change G (F (point₀ p₀ x q₁)) = point₀ p₀ x q₁
        exact (congrArg (fun y : T₁ => G y) (hF p₀ x q₁)).trans (hG p₀ x q₁)
      inv_hom_id := by
        apply ModuleCat.Hom.ext
        apply LinearMap.toAddMonoidHom_injective
        let : Module k C := z₁
        let : Module S C := l₁
        let : Module Sᵐᵒᵖ C := r₁
        let := c₁
        let := t₁
        let := u₁
        apply TensorProduct.Balanced.Morita.coefficientHom_ext k S P C Q
        intro p₀ x q₁
        change F (G (point₁ p₀ x q₁)) = point₁ p₀ x q₁
        exact (congrArg (fun y : T₀ => F y) (hG p₀ x q₁)).trans (hF p₀ x q₁) }
  refine ⟨e, ?_⟩
  intro p₀ x q₁
  change F (point₀ p₀ x q₁) = point₁ p₀ x q₁
  exact hF p₀ x q₁

include P Q in
/-- The actual comparison of the complete native composite and original raw tensors. -/
def returnCoordinates (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X ≅
      rawReturnObject k R S P Q X :=
  (returnCoordinateData k R S P Q X).1

-- keeps the actual composite-object getter for rw; Functor.comp_obj simplifies its source
@[simp, nolint simpNF]
theorem returnCoordinates_mk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ))
    (p₀ : P) (c : tensorObj k R S P Q X) (q₁ : Q) :
    letI := ModuleCat.Bimodule.Over.groundModule k R X
    letI := ModuleCat.Bimodule.Over.leftModule k R X
    letI := ModuleCat.Bimodule.Over.rightModule k R X
    letI := ModuleCat.Bimodule.Over.leftTower k R X
    letI := ModuleCat.Bimodule.Over.rightTower k R X
    letI := ModuleCat.Bimodule.Over.commute k R X
    let H := (tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)
    let T : ModuleCat (R ⊗[k] Rᵐᵒᵖ) := rawReturnObject k R S P Q X
    (@ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ (H.obj X) T
      (show H.obj X ⟶ T from (returnCoordinates k R S P Q X).hom))
        (returnOuterMk k R S P Q X p₀ c q₁) =
      rawReturnOuterMk k R S P Q X p₀ c q₁ :=
  (returnCoordinateData k R S P Q X).2 p₀ c q₁

end ModuleCat.Bimodule.Over.Morita
