/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import MathlibExt.Algebra.Category.Grp.ZModuleEquivalenceCompat

/-!
# Comparing monads induced by adjunctions

Let C,D be arbitrary categories with independent object and morphism universes. Natural
isomorphisms e:L≅L' and s:R≅R' compare the endofunctors RL and R'L' by i_X=R(e_X)≫s_{L'X}. For
adjunctions L⊣R and L'⊣R', compatibility with their units and counits makes i an isomorphism of
the induced monads.

The same construction gives the monad isomorphism associated to uniqueness of right adjoints to
a fixed left functor. A monad is also isomorphic to its transport along an isomorphism of the
underlying endofunctor. The component and multiplication formulas retain the order of
composition.

Further composition lemmas determine an adjoint arrow from its counit characteristic, combine
natural comparison squares, and transport monad multiplication equations along equal arrows. The
integer tensor lemma states composition of tensor maps for arbitrary abelian groups.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace CategoryTheory.Adjunction

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). For
L,L':C→D and R,R':D→C, natural isomorphisms e:L≅L' and s:R≅R' induce i:RL≅R'L'. Its component at
X is R(e_X)≫s_{L'X}:R(LX)→R'(L'X). This construction requires functor isomorphisms, without an
adjunction hypothesis. -/
def comparisonEndofunctorIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (e : L ≅ L') (s : R ≅ R') :
    L ⋙ R ≅ L' ⋙ R' :=
  Functor.isoWhiskerRight e R ≪≫ Functor.isoWhiskerLeft L' s

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). Let a:L⊣R
and b:L'⊣R' be adjunctions, with natural isomorphisms e:L≅L' and s:R≅R'. Write T=RL, S=R'L', and
i_X=R(e_X)≫s_{L'X}:TX→SX. Assume η^a_X≫R(e_X)≫s_{L'X}=η^b_X for every X∈C. Then the induced
monad units satisfy η^T_X≫i_X=η^S_X at every object X. -/
theorem comparisonEndofunctorIso_unit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ≅ L') (s : R ≅ R')
    (hη : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) ≫ s.hom.app (L'.obj X) = b.unit.app X)
    (X : C) :
    a.toMonad.η.app X ≫ (comparisonEndofunctorIso e s).hom.app X = b.toMonad.η.app X :=
  hη X

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). Let a:L⊣R
and b:L'⊣R' be adjunctions, with natural isomorphisms e:L≅L' and s:R≅R'. Write T=RL, S=R'L', and
i_X=R(e_X)≫s_{L'X}:TX→SX. Assume L'(s_Y)≫ε^b_Y=e^{-1}_{RY}≫ε^a_Y for every Y∈D. Then
μ^T_X≫i_X=(T(i_X)≫i_{SX})≫μ^S_X for every X∈C. Both composites have source T(TX) and target SX. -/
theorem comparisonEndofunctorIso_mul
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ≅ L') (s : R ≅ R')
    (hε : ∀ Y : D, L'.map (s.hom.app Y) ≫ b.counit.app Y =
      e.inv.app (R.obj Y) ≫ a.counit.app Y)
    (X : C) :
    a.toMonad.μ.app X ≫ (comparisonEndofunctorIso e s).hom.app X =
      (a.toMonad.map ((comparisonEndofunctorIso e s).hom.app X) ≫
        (comparisonEndofunctorIso e s).hom.app (b.toMonad.obj X)) ≫ b.toMonad.μ.app X := by
  let i := comparisonEndofunctorIso e s
  let Y := L'.obj X
  let c := R.map (e.hom.app X) ≫ s.hom.app Y
  have hnε : e.hom.app (R.obj Y) ≫ L'.map (s.hom.app Y) ≫ b.counit.app Y =
      a.counit.app Y := by
    rw [hε, Iso.hom_inv_id_app_assoc]
  have hnL := e.hom.naturality c
  have hinside : L.map c ≫ e.hom.app (R'.obj Y) ≫ b.counit.app Y =
      a.counit.app (L.obj X) ≫ e.hom.app X := by
    rw [← Category.assoc, hnL]
    dsimp only [c]
    rw [L'.map_comp]
    have hnE := e.hom.naturality (R.map (e.hom.app X))
    rw [← Category.assoc, ← hnE, Category.assoc, Category.assoc, hnε]
    exact a.counit.naturality (e.hom.app X)
  change R.map (a.counit.app (L.obj X)) ≫
      (R.map (e.hom.app X) ≫ s.hom.app (L'.obj X)) =
    (R.map (L.map (R.map (e.hom.app X) ≫ s.hom.app (L'.obj X))) ≫
      (R.map (e.hom.app (R'.obj (L'.obj X))) ≫ s.hom.app (L'.obj (R'.obj (L'.obj X))))) ≫
      R'.map (b.counit.app (L'.obj X))
  symm
  calc
    _ = R.map (L.map c) ≫ (R.map (e.hom.app (R'.obj Y)) ≫
        (s.hom.app (L'.obj (R'.obj Y)) ≫ R'.map (b.counit.app Y))) := by
      rw [Category.assoc, Category.assoc]
    _ = R.map (L.map c) ≫ (R.map (e.hom.app (R'.obj Y)) ≫
        (R.map (b.counit.app Y) ≫ s.hom.app Y)) := by
      have hn := s.hom.naturality (b.counit.app Y)
      dsimp only [Functor.id_obj, Functor.comp_obj] at hn
      rw [← hn]
    _ = R.map (L.map c ≫ e.hom.app (R'.obj Y) ≫ b.counit.app Y) ≫ s.hom.app Y := by
      rw [R.map_comp, R.map_comp, Category.assoc, Category.assoc]
    _ = R.map (a.counit.app (L.obj X) ≫ e.hom.app X) ≫ s.hom.app Y := by rw [hinside]
    _ = R.map (a.counit.app (L.obj X)) ≫ (R.map (e.hom.app X) ≫ s.hom.app Y) := by
      rw [R.map_comp, Category.assoc]

/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). Let a:L⊣R
and b:L'⊣R' be adjunctions, with natural isomorphisms e:L≅L' and s:R≅R'. Write T=RL, S=R'L', and
i_X=R(e_X)≫s_{L'X}:TX→SX. If η^a_X≫R(e_X)≫s_{L'X}=η^b_X for every X and
L'(s_Y)≫ε^b_Y=e^{-1}_{RY}≫ε^a_Y for every Y, then the induced monads T and S are isomorphic. The
forward component is i_X, and it preserves both unit and multiplication. -/
def comparisonMonadIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ≅ L') (s : R ≅ R')
    (hη : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) ≫ s.hom.app (L'.obj X) = b.unit.app X)
    (hε : ∀ Y : D, L'.map (s.hom.app Y) ≫ b.counit.app Y =
      e.inv.app (R.obj Y) ≫ a.counit.app Y) : a.toMonad ≅ b.toMonad :=
  MonadIso.mk (comparisonEndofunctorIso e s)
    (comparisonEndofunctorIso_unit a b e s hη)
    (comparisonEndofunctorIso_mul a b e s hε)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). Let L⊣R,
X,Y∈C, M,V,W∈D, k:X→RM, f:X→Y, b:Y→RM, m:LX→V, n:LY→W, t:V→W, c:W→M, and d:V→M. If L(k)≫ε_M=m≫d,
L(b)≫ε_M=n≫c, L(f)≫n=m≫t, and t≫c=d, then k=f≫b. The adjunction identifies the two arrows
through their equal counit characteristics. -/
theorem hom_eq_comp_of_counit_square
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {X Y : C} {M V W : D}
    (k : X ⟶ R.obj M) (f : X ⟶ Y) (b : Y ⟶ R.obj M)
    (m : L.obj X ⟶ V) (n : L.obj Y ⟶ W) (t : V ⟶ W) (c : W ⟶ M) (d : V ⟶ M)
    (hk : L.map k ≫ a.counit.app M = m ≫ d)
    (hb : L.map b ≫ a.counit.app M = n ≫ c)
    (hf : L.map f ≫ n = m ≫ t) (ht : t ≫ c = d) : k = f ≫ b := by
  apply (a.homEquiv _ _).symm.injective
  rw [a.homEquiv_counit, a.homEquiv_counit]
  rw [L.map_comp, Category.assoc, hb, ← Category.assoc, hf, Category.assoc, ht, hk]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let A,B,C,D,E,F be abelian groups in universe u₁. For additive maps a:A→B, b:B→C, c:A→C, d:D→E,
e:E→F, and f:D→F satisfying a≫b=c and d≫e=f, the integer tensor maps satisfy (a⊗d)≫(b⊗e)=c⊗f.
These are maps A⊗_ℤD→C⊗_ℤF, with each tensor map induced by the corresponding integer-linear
coefficient maps. -/
theorem integerTensorMap_comp_of_comp_eq
    {A B C D E F : AddCommGrpCat.{u₁}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (ha : a ≫ b = c)
    (d : D ⟶ E) (e : E ⟶ F) (f : D ⟶ F) (hd : d ≫ e = f) :
    AddCommGrpCat.ofHom
        (TensorProduct.map a.hom.toIntLinearMap d.hom.toIntLinearMap).toAddMonoidHom ≫
      AddCommGrpCat.ofHom
          (TensorProduct.map b.hom.toIntLinearMap e.hom.toIntLinearMap).toAddMonoidHom =
        AddCommGrpCat.ofHom
            (TensorProduct.map c.hom.toIntLinearMap f.hom.toIntLinearMap).toAddMonoidHom := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  refine TensorProduct.inductionOn x ?_ ?_
  · intro x y
    change b (a x) ⊗ₜ[ℤ] e (d y) = c x ⊗ₜ[ℤ] f y
    exact congrArg₂ (fun x y => x ⊗ₜ[ℤ] y)
      (ConcreteCategory.congr_hom ha x) (ConcreteCategory.congr_hom hd y)
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). Let
F,H:D→C and α:F⇒H. Take X,Y,Z∈C, M,N,P,Q∈D, c:X→FM, c₀:Y→HM, c':Z→HN, a:M→P, d:P→Q, t:M→N,
b:N→Q, f:X→Y, and g:Y→Z. If c≫α_M=f≫c₀, c₀≫H(t)=g≫c', and a≫d=t≫b, then
(c≫F(a))≫(α_P≫H(d))=(f≫g)≫(c'≫H(b)). -/
theorem pairing_comparison_comp
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (A B : D ⥤ C) (s : A ⟶ B)
    {X Y Z : C} {M N P Q : D}
    (c : X ⟶ A.obj M) (c₀ : Y ⟶ B.obj M) (c' : Z ⟶ B.obj N)
    (a : M ⟶ P) (d : P ⟶ Q) (t : M ⟶ N) (b : N ⟶ Q)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hp : c ≫ s.app M = f ≫ c₀)
    (hc : c₀ ≫ B.map t = g ≫ c') (ht : a ≫ d = t ≫ b) :
    (c ≫ A.map a) ≫ (s.app P ≫ B.map d) = (f ≫ g) ≫ (c' ≫ B.map b) := by
  rw [Category.assoc, ← Category.assoc (A.map a), s.naturality,
    Category.assoc, ← B.map_comp, ← Category.assoc, hp, Category.assoc,
    ht, B.map_comp, ← Category.assoc c₀, hc]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be a category with independent object and morphism universes u₁,v₁. For a monad T on C, an
endofunctor F, and a natural isomorphism i:T≅F of underlying functors, T is isomorphic as a
monad to the transported monad on F. The forward monad morphism has components i_X; the
transported unit is η^T_X≫i_X, and multiplication is transported through the two inverse
comparison factors. -/
def monadTransportIso
    {C : Type u₁} [Category.{v₁} C] (T : Monad C) {F : C ⥤ C}
    (i : T.toFunctor ≅ F) : T ≅ T.transport i :=
  MonadIso.mk i (fun X => by rfl) (fun X => by
    change T.μ.app X ≫ i.hom.app X =
      (T.map (i.hom.app X) ≫ i.hom.app (F.obj X)) ≫
        ((i.inv ◫ i.inv).app X ≫ T.μ.app X ≫ i.hom.app X)
    rw [NatTrans.hcomp_app, Category.assoc, Category.assoc]
    rw [Iso.hom_inv_id_app_assoc, ← T.map_comp_assoc, Iso.hom_inv_id_app,
      T.map_id, Category.id_comp])

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). For
adjunctions a:L⊣R and b:L⊣R' with the same left functor, uniqueness of right adjoints gives
s:R≅R'. The induced monads RL and R'L are canonically isomorphic, with forward component
s_{LX}:R(LX)→R'(LX). The adjunction unit and counit comparison identities supply the monad laws. -/
def rightAdjointMonadIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L ⊣ R') : a.toMonad ≅ b.toMonad :=
  comparisonMonadIso a b (Iso.refl _) (Adjunction.rightAdjointUniq a b)
    (fun X => by
      change a.unit.app X ≫ R.map (𝟙 (L.obj X)) ≫
        (Adjunction.rightAdjointUniq a b).hom.app (L.obj X) = b.unit.app X
      rw [R.map_id]
      exact (congrArg (fun f => a.unit.app X ≫ f)
        (Category.id_comp ((Adjunction.rightAdjointUniq a b).hom.app (L.obj X)))).trans
          (Adjunction.unit_rightAdjointUniq_hom_app a b X))
    (fun Y => by
      change L.map ((Adjunction.rightAdjointUniq a b).hom.app Y) ≫ b.counit.app Y =
        (𝟙 (L.obj (R.obj Y))) ≫ a.counit.app Y
      rw [Category.id_comp]
      exact Adjunction.rightAdjointUniq_hom_app_counit a b Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C,D be categories with independent object and morphism universes (u₁,v₁),(u₂,v₂). For a:L⊣R
and b:L⊣R', let s:R≅R' be their canonical right-adjoint uniqueness isomorphism. At X∈C, the
forward component of the induced monad isomorphism RL≅R'L equals s_{LX}. Its source and target
are R(LX) and R'(LX). -/
theorem rightAdjointMonadIso_hom_app
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L ⊣ R') (X : C) :
    (rightAdjointMonadIso a b).hom.app X =
      (Adjunction.rightAdjointUniq a b).hom.app (L.obj X) := by
  change R.map (𝟙 (L.obj X)) ≫ (Adjunction.rightAdjointUniq a b).hom.app (L.obj X) = _
  rw [R.map_id, Category.id_comp]

/-- Let C be a category with independent object and morphism universes u₁,v₁. For a monad T, an
endofunctor F, and a natural isomorphism i:T≅F of underlying functors, the canonical monad
isomorphism T≅transport_i(T) has forward component i_X:TX→FX at every X∈C. -/
theorem monadTransportIso_hom_app
    {C : Type u₁} [Category.{v₁} C] (T : Monad C) {F : C ⥤ C}
    (i : T.toFunctor ≅ F) (X : C) : (monadTransportIso T i).hom.app X = i.hom.app X := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be a category with independent object and morphism universes u₁,v₁. For monads T,S and a
monad morphism i:T→S, the multiplication identity at X is μ^T_X≫i_X=(i_{TX}≫S(i_X))≫μ^S_X. Both
sides map T(TX)→SX. Naturality of i identifies this order with T(i_X)≫i_{SX}≫μ^S_X. -/
theorem monadHom_mul_natural
    {C : Type u₁} [Category.{v₁} C] {T S : Monad C} (i : T ⟶ S) (X : C) :
    T.μ.app X ≫ i.app X = (i.app (T.obj X) ≫ S.map (i.app X)) ≫ S.μ.app X :=
  (i.app_μ X).trans
    (congrArg (fun f => f ≫ S.μ.app X) (i.toNatTrans.naturality (i.app X)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be a category with independent object and morphism universes u₁,v₁. Let S be a monad,
X,Y,Z objects, m,m':X→Y, a,a':Y→SZ, and b,b':X→SY. If m=m', a=a', b=b', and
m'≫a'=(b'≫S(a'))≫μ^S_Z, then m≫a=(b≫S(a))≫μ^S_Z. The conclusion uses the same source, target,
and multiplication morphism. -/
theorem monad_mul_square_of_arrow_eq
    {C : Type u₁} [Category.{v₁} C] (S : Monad C)
    {X Y Z : C} (m m' : X ⟶ Y) (a a' : Y ⟶ S.obj Z) (b b' : X ⟶ S.obj Y)
    (hm : m = m') (ha : a = a') (hb : b = b')
    (h : m' ≫ a' = (b' ≫ S.map a') ≫ S.μ.app Z) :
    m ≫ a = (b ≫ S.map a) ≫ S.μ.app Z := by
  rw [hm, ha, hb]
  exact h

end CategoryTheory.Adjunction

universe uMul vMul

namespace CategoryTheory.Adjunction

/-- Let C be a category with independent object and morphism universes uMul,vMul. For a monad S,
objects X,Y,Z, and arrows m:X→Y, a:Y→SZ, b:X→SY, this property is the equation
m≫a=(b≫S(a))≫μ^S_Z. Both sides have source X and target SZ. -/
def monadMulSquareProperty {C : Type uMul} [Category.{vMul} C]
    (S : Monad C) {X Y Z : C} (m : X ⟶ Y) (a : Y ⟶ S.obj Z) (b : X ⟶ S.obj Y) : Prop :=
  m ≫ a = (b ≫ S.map a) ≫ S.μ.app Z

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be a category with independent object and morphism universes uMul,vMul and S a monad. For
m,m':X→Y, a,a':Y→SZ, and b,b':X→SY, assume m=m', a=a', b=b', and m'≫a'=(b'≫S(a'))≫μ^S_Z. Then
the multiplication-square property holds for m,a,b, namely m≫a=(b≫S(a))≫μ^S_Z. -/
theorem monadMulSquareProperty_of_arrow_eq
    {C : Type uMul} [Category.{vMul} C] (S : Monad C)
    {X Y Z : C} (m m' : X ⟶ Y) (a a' : Y ⟶ S.obj Z) (b b' : X ⟶ S.obj Y)
    (hm : m = m') (ha : a = a') (hb : b = b')
    (h : m' ≫ a' = (b' ≫ S.map a') ≫ S.μ.app Z) :
    monadMulSquareProperty S m a b :=
  monad_mul_square_of_arrow_eq S m m' a a' b b' hm ha hb h

end CategoryTheory.Adjunction
