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
# Relative tensor return coordinates and morphism values

Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with carriers p,q. Choose W=max(p,q,v) for enveloping-module objects. The tensor
functors F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q preserve this common height.

An outer return class is (p₀⊗_S c)⊗_S q₁ with c∈F(X). Composite morphisms act as
(p₀⊗c)⊗q₁↦(p₀⊗F(f)(c))⊗q₁. The same formula holds for G applied to a morphism of S-enveloping
modules with an arbitrary carrier universe a.

The composite object G(FX) is isomorphic to its raw return coefficient object with the same
ordered tensors. Ground k-action and both endpoint actions are recovered from the relative
enveloping action; these identifications give the coordinate isomorphism and its outer-class
formula. Agreement on all five-factor classes determines any additive map from the composite.
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

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k),
p₀∈P,c∈F(X),q₁∈Q, the outer class is (p₀⊗_S c)⊗_S q₁ in G(FX). Its middle coefficient c may be
any element of F(X). -/
def returnOuterMk (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) (p₀ : P)
    (c : tensorObj k R S P Q X) (q₁ : Q) :
    ((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X :=
  tensorMk k S R Q P (tensorObj k R S P Q X) p₀ c q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k) and an additive
commutative monoid C' in any universe, additive maps h₁,h₂:G(FX)→C' are equal if they agree on
every (p₀⊗_S((q₀⊗_R x)⊗_R p₁))⊗_S q₁. The hypothesis ranges over all P,Q,X,P,Q coefficients. -/
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

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. For A,B∈ModuleCat_a(E_S^k), E_S^k=S⊗_kSᵒᵖ, and g:A→B,
put G(Z)=(P⊗_S Z)⊗_S Q. The three-argument function is (p₀,c,q₁)↦G(g)((p₀⊗_S c)⊗_S q₁). Its
target G(B) has carrier height max(p,q,a). -/
def outerTensorMapValue {A B : ModuleCat.{a} (S ⊗[k] Sᵐᵒᵖ)} (g : A ⟶ B) :
    P → A → Q → tensorObj k S R Q P B := by
  let A' := tensorObj k S R Q P A
  let B' := tensorObj k S R Q P B
  let L : A' →ₗ[R ⊗[k] Rᵐᵒᵖ] B' :=
    @ModuleCat.Hom.hom (R ⊗[k] Rᵐᵒᵖ) _ A' B' (tensorMap k S R Q P g)
  exact fun p₀ c q₁ => L (tensorMk k S R Q P A p₀ c q₁)

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. For A,B∈ModuleCat_a(S⊗_kSᵒᵖ) and g:A→B, the function
(p₀,c,q₁)↦(p₀⊗_S g(c))⊗_S q₁ takes values in G(B)=(P⊗_S B)⊗_S Q. The outer P and Q factors are
retained. -/
def outerTensorMappedValue {A B : ModuleCat.{a} (S ⊗[k] Sᵐᵒᵖ)} (g : A ⟶ B) :
    P → A → Q → tensorObj k S R Q P B := by
  let L : A →ₗ[S ⊗[k] Sᵐᵒᵖ] B :=
    @ModuleCat.Hom.hom (S ⊗[k] Sᵐᵒᵖ) _ A B g
  exact fun p₀ c q₁ => tensorMk k S R Q P B p₀ (L c) q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. For g:A→B in ModuleCat_a(S⊗_kSᵒᵖ), write G(Z)=(P⊗_S
Z)⊗_S Q. The functions P→A→Q→G(B) satisfy G(g)((p₀⊗c)⊗q₁)=(p₀⊗g(c))⊗q₁ for every p₀,c,q₁.
Equality holds for the complete three-argument functions. -/
theorem outerTensorMapValue_eq {A B : ModuleCat.{a} (S ⊗[k] Sᵐᵒᵖ)} (g : A ⟶ B) :
    outerTensorMapValue k R S P Q g = outerTensorMappedValue k R S P Q g := by
  funext p₀ c q₁
  exact tensorMap_mk k S R Q P (X := A) (Y := B) g p₀ c q₁

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), the
intermediate carrier is the underlying type of F(X). It lies in W and consists of balanced
tensor coefficients (Q⊗_R X)⊗_R P. -/
def returnIntermediateCarrier (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    Type (max p q v) :=
  (tensorObj k R S P Q X).carrier

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), the composite
carrier is the underlying type of G(FX) in W. It consists of the nested balanced coefficients
(P⊗_S((Q⊗_R X)⊗_R P))⊗_S Q. -/
def returnCompositeCarrier (X : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)) :
    Type (max p q v) :=
  (((tensorFunctor k R S P Q) ⋙ (tensorFunctor k S R Q P)).obj X).carrier

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y in ModuleCat_W(E_R^k), the
value function P→F(X)→Q→G(FY) is (p₀,c,q₁)↦(GF)(f)((p₀⊗_S c)⊗_S q₁). It is the outer tensor-map
function applied to g=F(f). -/
def returnOuterMapValue {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      returnCompositeCarrier k R S P Q Y := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let A : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj X
  let B : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj Y
  let g : A ⟶ B := F.map f
  exact outerTensorMapValue k R S P Q (A := A) (B := B) g

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y, the function P→F(X)→Q→G(FY)
is (p₀,c,q₁)↦(p₀⊗_S F(f)(c))⊗_S q₁. It retains the outer factors and maps the full intermediate
coefficient. -/
def returnOuterMappedValue {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    P → returnIntermediateCarrier k R S P Q X → Q →
      returnCompositeCarrier k R S P Q Y := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let A : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj X
  let B : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj Y
  let g : A ⟶ B := F.map f
  exact outerTensorMappedValue k R S P Q (A := A) (B := B) g

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y in ModuleCat_W(E_R^k),
(GF)(f)=G(F(f)). The right side is the tensor map with coefficient order P–F(X)–Q applied to
F(f):F(X)→F(Y), and both sides are E_R^k-linear maps G(FX)→G(FY). -/
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

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y, the two functions
P→F(X)→Q→G(FY) satisfy (GF)(f)((p₀⊗c)⊗q₁)=(p₀⊗F(f)(c))⊗q₁ for every outer triple. This is
equality of the full value functions at the fixed common height W. -/
theorem returnOuterMapValue_eq
    {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y) :
    returnOuterMapValue k R S P Q f = returnOuterMappedValue k R S P Q f := by
  let F : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ) ⥤
      ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := tensorFunctor k R S P Q
  let A : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj X
  let B : ModuleCat.{max p q v} (S ⊗[k] Sᵐᵒᵖ) := F.obj Y
  let g : A ⟶ B := F.map f
  exact outerTensorMapValue_eq k R S P Q (A := A) (B := B) g

/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For f:X→Y, p₀∈P,c∈F(X),q₁∈Q, the
composite map satisfies (GF)(f)((p₀⊗_S c)⊗_S q₁)=(p₀⊗_S F(f)(c))⊗_S q₁. The identity is in the
carrier of G(FY). -/
@[simp]
theorem returnOuterMap_mk {X Y : ModuleCat.{max p q v} (R ⊗[k] Rᵐᵒᵖ)} (f : X ⟶ Y)
    (p₀ : P) (c : returnIntermediateCarrier k R S P Q X) (q₁ : Q) :
    returnOuterMapValue k R S P Q f p₀ c q₁ =
      returnOuterMappedValue k R S P Q f p₀ c q₁ :=
  congrFun (congrFun (congrFun (returnOuterMapValue_eq k R S P Q f) p₀) c) q₁

include P Q in
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), let T(X) be
the raw return object with the ground and endpoint actions extracted from X. There is an
isomorphism e_X:G(FX)≅T(X), together with e_X((p₀⊗c)⊗q₁)=(p₀⊗c)⊗q₁ in raw coefficient
coordinates for every p₀,c,q₁. -/
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
/-- Let k be a commutative ring in u, R,S k-algebra rings in r,s, and P:(R,S), Q:(S,R) k-compatible
bimodules with independent carriers p,q. Put W=max(p,q,v), E_R^k=R⊗_kRᵒᵖ, E_S^k=S⊗_kSᵒᵖ. At
height W let F(X)=(Q⊗_R X)⊗_R P and G(Y)=(P⊗_S Y)⊗_S Q. For X∈ModuleCat_W(E_R^k), the
isomorphism G(FX)≅T(X), where T(X)=(P⊗_S((Q⊗_R X)⊗_R P))⊗_S Q, preserves the ground k-action and
both outer R-actions. Its forward map retains every ordered outer class with arbitrary c∈F(X). -/
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
