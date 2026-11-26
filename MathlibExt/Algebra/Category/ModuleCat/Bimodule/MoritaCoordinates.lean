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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.MoritaReturn
public import MathlibExt.Algebra.Module.NatInt

/-!
# Coordinates of composite bimodule tensor functors

Let R,S be rings in universes r,s, with bimodules P:(R,S), Q:(S,R) and coefficient carriers in
v. The tensor functors F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q have composite object G(FX).

The outer coefficient class is (p₀⊗_S c)⊗_S q₁ for c∈F(X). The identity-coordinate comparison
identifies the composite object with its raw balanced-tensor model T(X)=(P⊗_S((Q⊗_R X)⊗_R P))⊗_S
Q, carrying the same outer R-actions.

For a morphism f:X→Y, the composite map fixes p₀,q₁ and applies F(f) to c. Additive maps out of
the composite are determined by the classes with all five factors p₀,q₀,x,p₁,q₁. The coordinate
comparison is packaged together with its formula for every outer class.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe r s v

namespace ModuleCat.Bimodule.Morita

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Write F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q for the enveloping-module tensor
functors. For X∈ModuleCat_v(R⊗_ℤRᵒᵖ), p₀∈P,c∈F(X),q₁∈Q, the outer class is (p₀⊗_S c)⊗_S q₁ in
G(FX). The S-actions on c are the endpoint restrictions of its S-enveloping module. -/
def returnOuterMk (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) (p₀ : P)
    (c : tensorObj R S P Q X) (q₁ : Q) :
    ((tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)).obj X := by
  let A := tensorObj R S P Q X
  letI : Module ℤ A := AddCommGroup.toIntModule A
  letI := ModuleCat.Bimodule.leftModule S A
  letI := ModuleCat.Bimodule.rightModule S A
  letI := ModuleCat.Bimodule.commute S A
  letI := TensorProduct.Balanced.rightModule ℤ S S P A
  exact mk ℤ S (TensorProduct.Balanced ℤ S P A) Q (mk ℤ S P A p₀ c) q₁

/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Write F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q for the enveloping-module tensor
functors. For X in the R-enveloping module category and an additive commutative monoid C' in any
universe, additive maps f,g:G(FX)→C' are equal if they agree on every class (p₀⊗((q₀⊗x)⊗p₁))⊗q₁.
The variables range over P,Q,X,P,Q respectively. -/
theorem returnHom_ext (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ))
    {C' : Type*} [AddCommMonoid C']
    {f g : ((tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)).obj X →+ C'}
    (h : letI := ModuleCat.Bimodule.leftModule R X
      letI := ModuleCat.Bimodule.rightModule R X
      letI := ModuleCat.Bimodule.commute R X
      letI := TensorProduct.Balanced.rightModule ℤ R R Q X
      ∀ (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q),
        f (returnOuterMk R S P Q X p₀
          (mk ℤ R (TensorProduct.Balanced ℤ R Q X) P (mk ℤ R Q X q₀ x) p₁) q₁) =
        g (returnOuterMk R S P Q X p₀
          (mk ℤ R (TensorProduct.Balanced ℤ R Q X) P (mk ℤ R Q X q₀ x) p₁) q₁)) :
    f = g := by
  let := ModuleCat.Bimodule.leftModule R X
  let := ModuleCat.Bimodule.rightModule R X
  let := ModuleCat.Bimodule.commute R X
  let := TensorProduct.Balanced.rightModule ℤ R R Q X
  let A := tensorObj R S P Q X
  let : Module ℤ A := AddCommGroup.toIntModule A
  let := ModuleCat.Bimodule.leftModule S A
  let := ModuleCat.Bimodule.rightModule S A
  let := ModuleCat.Bimodule.commute S A
  let := TensorProduct.Balanced.rightModule ℤ S S P A
  let B := TensorProduct.Balanced ℤ S P A
  apply addHom_ext ℤ S B Q
  intro b q₁
  have hb : f.comp (((mk ℤ S B Q).flip q₁).toAddMonoidHom) =
      g.comp (((mk ℤ S B Q).flip q₁).toAddMonoidHom) := by
    apply addHom_ext ℤ S P A
    intro p₀ a
    have ha : (f.comp (((mk ℤ S B Q).flip q₁).toAddMonoidHom)).comp
        ((mk ℤ S P A p₀).toAddMonoidHom) =
      (g.comp (((mk ℤ S B Q).flip q₁).toAddMonoidHom)).comp
        ((mk ℤ S P A p₀).toAddMonoidHom) := by
      apply TensorProduct.Balanced.Morita.coefficientHom_ext ℤ R Q X P
      intro q₀ x p₁
      exact h p₀ q₀ x p₁ q₁
    exact DFunLike.congr_fun ha a
  exact DFunLike.congr_fun hb b

-- composite-functor form for rw; Functor.comp_map simplifies LHS
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Write F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q for the enveloping-module tensor
functors. For an R-enveloping module morphism f:X→Y and p₀∈P,c∈F(X),q₁∈Q,
(GF)(f)((p₀⊗c)⊗q₁)=(p₀⊗F(f)(c))⊗q₁. Both tensors are balanced over S in the outer two steps. -/
@[simp, nolint simpNF]
theorem returnOuterMap_mk {X Y : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)} (f : X ⟶ Y)
    (p₀ : P) (c : tensorObj R S P Q X) (q₁ : Q) :
    (((tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)).map f).hom
        (returnOuterMk R S P Q X p₀ c q₁) =
      returnOuterMk R S P Q Y p₀ ((tensorMap R S P Q f).hom c) q₁ := by
  let A := tensorObj R S P Q X
  let B := tensorObj R S P Q Y
  let : Module ℤ A := AddCommGroup.toIntModule A
  let : Module ℤ B := AddCommGroup.toIntModule B
  let := ModuleCat.Bimodule.leftModule S A
  let := ModuleCat.Bimodule.rightModule S A
  let := ModuleCat.Bimodule.commute S A
  let := ModuleCat.Bimodule.leftModule S B
  let := ModuleCat.Bimodule.rightModule S B
  let := ModuleCat.Bimodule.commute S B
  let := TensorProduct.Balanced.rightModule ℤ S S P A
  let := TensorProduct.Balanced.rightModule ℤ S S P B
  exact tensorMap_mk S R Q P (tensorMap R S P Q f) p₀ c q₁

include P Q in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Write F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q for the enveloping-module tensor
functors. For X in the R-enveloping module category, let T(X) be the raw balanced tensor (P⊗_S
F(X))⊗_S Q with its computed R-actions. There is an isomorphism e_X:G(FX)≅T(X), together with
the equality e_X((p₀⊗c)⊗q₁)=(p₀⊗c)⊗q₁ in raw coordinates for every p₀,c,q₁. -/
def returnCoordinateData (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    letI := ModuleCat.Bimodule.leftModule R X
    letI := ModuleCat.Bimodule.rightModule R X
    letI := ModuleCat.Bimodule.commute R X
    {e : ((tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)).obj X ≅
        rawReturnObject R S P Q X //
      ∀ (p₀ : P) (c : tensorObj R S P Q X) (q₁ : Q),
        e.hom.hom (returnOuterMk R S P Q X p₀ c q₁) =
          rawReturnOuterMk R S P Q X p₀ c q₁} := by
  letI := ModuleCat.Bimodule.leftModule R X
  letI := ModuleCat.Bimodule.rightModule R X
  letI := ModuleCat.Bimodule.commute R X
  let C := TensorProduct.Balanced.Morita.coefficientTensor ℤ R Q X P
  let A := tensorObj R S P Q X
  let z₁ : Module ℤ C := inferInstance
  let z₀ : Module ℤ C := AddCommGroup.toIntModule C
  let l₁ : Module S C := TensorProduct.Balanced.Morita.coefficientLeftModule ℤ R S Q X P
  let r₁ : Module Sᵐᵒᵖ C := TensorProduct.Balanced.Morita.coefficientRightModule ℤ R S Q X P
  let l₀ : Module S C := ModuleCat.Bimodule.leftModule S A
  let r₀ : Module Sᵐᵒᵖ C := ModuleCat.Bimodule.rightModule S A
  let c₁ : (letI := z₁; letI := l₁; letI := r₁; SMulCommClass S Sᵐᵒᵖ C) := by
    let := z₁
    let := l₁
    let := r₁
    exact TensorProduct.Balanced.Morita.coefficientActionsComm ℤ R S Q X P
  let t₁ : @IsScalarTower ℤ S C
      (Algebra.toModule : Module ℤ S).toSMul l₁.toSMul z₁.toSMul :=
    Module.intModule_isScalarTower (dRM := l₁)
      (Algebra.toModule : Module ℤ S) z₁
  let u₁ : @IsScalarTower ℤ Sᵐᵒᵖ C
      (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul r₁.toSMul z₁.toSMul :=
    Module.intModule_isScalarTower (dRM := r₁)
      (Algebra.toModule : Module ℤ Sᵐᵒᵖ) z₁
  let c₀ : (letI := z₀; letI := l₀; letI := r₀; SMulCommClass S Sᵐᵒᵖ C) :=
    ModuleCat.Bimodule.commute S A
  let t₀ : @IsScalarTower ℤ S C
      (Algebra.toModule : Module ℤ S).toSMul l₀.toSMul z₀.toSMul :=
    Module.intModule_isScalarTower (dRM := l₀)
      (Algebra.toModule : Module ℤ S) z₀
  let u₀ : @IsScalarTower ℤ Sᵐᵒᵖ C
      (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul r₀.toSMul z₀.toSMul :=
    Module.intModule_isScalarTower (dRM := r₀)
      (Algebra.toModule : Module ℤ Sᵐᵒᵖ) z₀
  have hz : z₀ = z₁ := Subsingleton.elim _ _
  have hl : l₀ = l₁ := by
    let := z₁
    let := l₁
    let := r₁
    let := c₁
    let := t₁
    let := u₁
    exact ModuleCat.Bimodule.leftModule_ofTensor S C
  have hr : r₀ = r₁ := by
    let := z₁
    let := l₁
    let := r₁
    let := c₁
    let := t₁
    let := u₁
    exact ModuleCat.Bimodule.rightModule_ofTensor S C
  let K : (z : Module ℤ C) → (l : Module S C) → (r : Module Sᵐᵒᵖ C) →
      (letI := z; letI := l; letI := r; SMulCommClass S Sᵐᵒᵖ C) →
      (@IsScalarTower ℤ S C
        (Algebra.toModule : Module ℤ S).toSMul l.toSMul z.toSMul) →
      (@IsScalarTower ℤ Sᵐᵒᵖ C
        (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul r.toSMul z.toSMul) →
      ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ) := fun z l r c t u =>
    letI := z
    letI := l
    letI := r
    letI := c
    letI := t
    letI := u
    tensorObject S R Q P C
  let g : ∀ (z : Module ℤ C) (l : Module S C) (r : Module Sᵐᵒᵖ C)
      (c : letI := z; letI := l; letI := r; SMulCommClass S Sᵐᵒᵖ C)
      (t : @IsScalarTower ℤ S C
        (Algebra.toModule : Module ℤ S).toSMul l.toSMul z.toSMul)
      (u : @IsScalarTower ℤ Sᵐᵒᵖ C
        (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul r.toSMul z.toSMul),
      P → C → Q → K z l r c t u := fun z l r c t u p x q =>
    letI := z
    letI := l
    letI := r
    letI := c
    letI := t
    letI := u
    letI := Module.intModule_smulCommClass
      (dS := l.toDistribMulAction.toDistribSMul) (dM := z)
    letI := Module.intModule_smulCommClass
      (dS := r.toDistribMulAction.toDistribSMul) (dM := z)
    letI := TensorProduct.Balanced.rightModule ℤ S S P C
    mk ℤ S (TensorProduct.Balanced ℤ S P C) Q (mk ℤ S P C p x) q
  have compare : ∀ (z z' : Module ℤ C) (ez : z = z')
      (l l' : Module S C) (el : l = l') (r r' : Module Sᵐᵒᵖ C) (er : r = r')
      (c : letI := z; letI := l; letI := r; SMulCommClass S Sᵐᵒᵖ C)
      (c' : letI := z'; letI := l'; letI := r'; SMulCommClass S Sᵐᵒᵖ C)
      (t : @IsScalarTower ℤ S C
        (Algebra.toModule : Module ℤ S).toSMul l.toSMul z.toSMul)
      (t' : @IsScalarTower ℤ S C
        (Algebra.toModule : Module ℤ S).toSMul l'.toSMul z'.toSMul)
      (u : @IsScalarTower ℤ Sᵐᵒᵖ C
        (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul r.toSMul z.toSMul)
      (u' : @IsScalarTower ℤ Sᵐᵒᵖ C
        (Algebra.toModule : Module ℤ Sᵐᵒᵖ).toSMul r'.toSMul z'.toSMul),
      {e : K z l r c t u ≅ K z' l' r' c' t' u' //
        ∀ (p : P) (x : C) (q : Q), e.hom.hom (g z l r c t u p x q) =
          g z' l' r' c' t' u' p x q} := by
    intro z z' ez l l' el r r' er c c' t t' u u'
    subst z'
    subst l'
    subst r'
    exact ⟨Iso.refl _, fun _ _ _ => rfl⟩
  exact compare z₀ z₁ hz l₀ l₁ hl r₀ r₁ hr c₀ c₁ t₀ t₁ u₀ u₁

include P Q in
/-- Let R,S be rings in independent universes r,s, P an (R,S)-bimodule and Q an (S,R)-bimodule with
carriers in v. Write F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q for the enveloping-module tensor
functors. For X∈ModuleCat_v(R⊗_ℤRᵒᵖ), the coordinate comparison is an R-enveloping module
isomorphism G(FX)≅T(X), where T(X)=(P⊗_S((Q⊗_R X)⊗_R P))⊗_S Q. Its forward map preserves each
ordered outer tensor class and the inner coefficient c∈F(X). -/
def returnCoordinates (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    letI := ModuleCat.Bimodule.leftModule R X
    letI := ModuleCat.Bimodule.rightModule R X
    letI := ModuleCat.Bimodule.commute R X
    ((tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)).obj X ≅
      rawReturnObject R S P Q X :=
  (returnCoordinateData R S P Q X).1

@[simp, nolint simpNF] -- composite-functor form for rw; Functor.comp_obj simplifies LHS
theorem returnCoordinates_mk (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ))
    (p₀ : P) (c : tensorObj R S P Q X) (q₁ : Q) :
    letI := ModuleCat.Bimodule.leftModule R X
    letI := ModuleCat.Bimodule.rightModule R X
    letI := ModuleCat.Bimodule.commute R X
    (returnCoordinates R S P Q X).hom.hom (returnOuterMk R S P Q X p₀ c q₁) =
      rawReturnOuterMk R S P Q X p₀ c q₁ :=
  (returnCoordinateData R S P Q X).2 p₀ c q₁

end ModuleCat.Bimodule.Morita
