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
# Monad comparison from actual adjunction isomorphisms

Natural left and right comparisons with their original unit and counit
squares induce a monad isomorphism by direct naturality and composition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace CategoryTheory.Adjunction

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual left/right adjunction comparisons give the induced endofunctor comparison. -/
def comparisonEndofunctorIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (e : L ≅ L') (s : R ≅ R') :
    L ⋙ R ≅ L' ⋙ R' :=
  Functor.isoWhiskerRight e R ≪≫ Functor.isoWhiskerLeft L' s

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original unit square is the unit square of the induced monad comparison. -/
theorem comparisonEndofunctorIso_unit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ≅ L') (s : R ≅ R')
    (hη : ∀ X : C, a.unit.app X ≫ R.map (e.hom.app X) ≫ s.hom.app (L'.obj X) = b.unit.app X)
    (X : C) :
    a.toMonad.η.app X ≫ (comparisonEndofunctorIso e s).hom.app X = b.toMonad.η.app X :=
  hη X

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual counit square implies multiplication compatibility for the induced monad
comparison. -/
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

/-- Actual adjunction unit/counit comparison squares construct the induced monad isomorphism. -/
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
/-- Equal actual counit characteristics determine an adjoint comparison after composition. -/
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
/-- Tensoring two actual additive composition squares preserves their literal integer tensor map. -/
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
/-- Compose actual binary pairing, coefficient and final comparison squares through one natural
right-adjoint map. -/
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
/-- The actual original monad and its transport along a functor isomorphism are isomorphic. -/
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
/-- Actual uniqueness of right adjoints identifies their induced monads on the same left functor. -/
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
/-- The actual right-adjoint monad comparison component is the original right-adjoint uniqueness
component. -/
theorem rightAdjointMonadIso_hom_app
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L ⊣ R') (X : C) :
    (rightAdjointMonadIso a b).hom.app X =
      (Adjunction.rightAdjointUniq a b).hom.app (L.obj X) := by
  change R.map (𝟙 (L.obj X)) ≫ (Adjunction.rightAdjointUniq a b).hom.app (L.obj X) = _
  rw [R.map_id, Category.id_comp]

/-- The actual monad transport isomorphism component is its original functor isomorphism
component. -/
theorem monadTransportIso_hom_app
    {C : Type u₁} [Category.{v₁} C] (T : Monad C) {F : C ⥤ C}
    (i : T.toFunctor ≅ F) (X : C) : (monadTransportIso T i).hom.app X = i.hom.app X := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- A genuine monad morphism preserves multiplication in the source-first naturality orientation. -/
theorem monadHom_mul_natural
    {C : Type u₁} [Category.{v₁} C] {T S : Monad C} (i : T ⟶ S) (X : C) :
    T.μ.app X ≫ i.app X = (i.app (T.obj X) ≫ S.map (i.app X)) ≫ S.μ.app X :=
  (i.app_μ X).trans
    (congrArg (fun f => f ≫ S.μ.app X) (i.toNatTrans.naturality (i.app X)))

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport a genuine monad multiplication square along equal actual source and comparison
arrows. -/
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

/-- The genuine multiplication square with the original source and comparison arrows. -/
def monadMulSquareProperty {C : Type uMul} [Category.{vMul} C]
    (S : Monad C) {X Y Z : C} (m : X ⟶ Y) (a : Y ⟶ S.obj Z) (b : X ⟶ S.obj Y) : Prop :=
  m ≫ a = (b ≫ S.map a) ≫ S.μ.app Z

set_option backward.isDefEq.respectTransparency.types false in
/-- Equal actual comparison arrows transport a genuine monad multiplication law. -/
theorem monadMulSquareProperty_of_arrow_eq
    {C : Type uMul} [Category.{vMul} C] (S : Monad C)
    {X Y Z : C} (m m' : X ⟶ Y) (a a' : Y ⟶ S.obj Z) (b b' : X ⟶ S.obj Y)
    (hm : m = m') (ha : a = a') (hb : b = b')
    (h : m' ≫ a' = (b' ≫ S.map a') ≫ S.μ.app Z) :
    monadMulSquareProperty S m a b :=
  monad_mul_square_of_arrow_eq S m m' a a' b b' hm ha hb h

end CategoryTheory.Adjunction
