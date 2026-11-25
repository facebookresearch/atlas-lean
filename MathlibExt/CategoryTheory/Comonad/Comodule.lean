/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Left and right comodule functors for a comonad

Formal categorical dual of `Monad.Module` left/right modules, with action
arrows reversed to coactions. These are the comodule inputs for the cobar
dual in `Comonad.Cobar` (see there for the May source and the
coface/codegeneracy orientation).

For a comonad `G` on `C` we construct the two ordinary-Cat comodule comonads:

* the comonad on `C ⥤ D` given by precomposition `R ↦ G ⋙ R`, i.e. `R` after `G`
  in diagrammatic order (`R.comp G`);
* the comonad on `A ⥤ C` given by postcomposition `L ↦ L ⋙ G`, i.e. `G` after `L`
  (`G.comp L` diagrammatically written `L ⋙ G`).

A right `G`-comodule functor `R : C ⥤ D` is a coalgebra for the first comonad,
with coaction `R ⟶ G ⋙ R`. A left `G`-comodule functor `L : A ⥤ C` is a
coalgebra for the second comonad, with coaction `L ⟶ L ⋙ G`. The definitions
re-use `Comonad.Coalgebra` and do not duplicate its structure; in particular the
hom types, identity, composition, and `Category` instances are inherited from
the coalgebra API, giving the minimal bundling needed for comodule
functoriality.

We provide documented underlying-functor and coaction accessors with `simp`
rfl-lemmas, ordinary component lemmas for the counit and coassociativity laws
in comodule form, a `mk` constructor, and the correctly oriented hom
compatibility equations.

This file provides no cobar objects or operators, no cosimplicial identities,
and no monoidal, differential-graded, derived, or bicategorical APIs.
Change-of-comonad corestriction is provided by the generic coalgebra
transport/corestriction API used by `ComoduleChange`; this file itself defines
the fixed-comonad comodule structures and accessors.
-/

@[expose] public section

namespace CategoryTheory

namespace Comonad

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- The comonad on `C ⥤ D` given by precomposition with `G`.

The underlying functor sends `R` to `G ⋙ R`; the counit and comultiplication
are `G.ε` and `G.δ` whiskered on the right. The laws follow componentwise from
the comonad laws of `G`. -/
abbrev precompComonad {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (G : Comonad C) : Comonad (C ⥤ D) where
  toFunctor :=
    { obj := fun R => G ⋙ R
      map := fun f => Functor.whiskerLeft G.toFunctor f
      map_id := fun _ => by ext X; simp
      map_comp := fun _ _ => by ext X; simp
    }
  ε :=
    { app := fun R => Functor.whiskerRight G.ε R
      naturality := fun R S f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact (f.naturality (G.ε.app X)).symm
    }
  δ :=
    { app := fun R => Functor.whiskerRight G.δ R
      naturality := fun R S f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact (f.naturality (G.δ.app X)).symm
    }
  coassoc R := by
    ext X : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map]
    change R.map (G.δ.app X) ≫ R.map (G.δ.app (G.obj X)) =
      R.map (G.δ.app X) ≫ R.map (G.toFunctor.map (G.δ.app X))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact (G.coassoc X).symm
  left_counit R := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.comp_obj]
    rw [← Functor.map_comp]
    rw [G.right_counit X]
    exact R.map_id _
  right_counit R := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← Functor.map_comp]
    rw [G.left_counit X]
    exact R.map_id _

/-- Objects of the precomposition comonad are computed pointwise. -/
@[simp]
lemma precompComonad_obj_obj {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {G : Comonad C} (R : C ⥤ D) (X : C) :
    ((precompComonad G).toFunctor.obj R).obj X = R.obj (G.obj X) := rfl

/-- The comonad on `A ⥤ C` given by postcomposition with `G`.

The underlying functor sends `L` to `L ⋙ G`; the counit and comultiplication
are `G.ε` and `G.δ` whiskered on the left. The laws follow componentwise from
the comonad laws of `G`. -/
abbrev postcompComonad {C : Type u₁} [Category.{v₁} C] {A : Type u₃}
    [Category.{v₃} A] (G : Comonad C) : Comonad (A ⥤ C) where
  toFunctor :=
    { obj := fun L => L ⋙ G
      map := fun f => Functor.whiskerRight f G.toFunctor
      map_id := fun _ => by ext X; simp
      map_comp := fun _ _ => by ext X; simp
    }
  ε :=
    { app := fun L => Functor.whiskerLeft L G.ε
      naturality := fun L M f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact G.ε.naturality (f.app X)
    }
  δ :=
    { app := fun L => Functor.whiskerLeft L G.δ
      naturality := fun L M f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact G.δ.naturality (f.app X)
    }
  coassoc L := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    exact G.coassoc (L.obj X)
  left_counit L := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    exact G.left_counit (L.obj X)
  right_counit L := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    exact G.right_counit (L.obj X)

/-- Objects of the postcomposition comonad are computed pointwise. -/
@[simp]
lemma postcompComonad_obj_obj {C : Type u₁} [Category.{v₁} C] {A : Type u₃}
    [Category.{v₃} A] {G : Comonad C} (L : A ⥤ C) (X : A) :
    ((postcompComonad G).toFunctor.obj L).obj X = G.obj (L.obj X) := rfl

/-- The comonad morphism on `C ⥤ D` induced by `h : G ⟶ H`, via whiskering on
the right. Dual of `Monad.precompMonadHom`. -/
def precompComonadHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {G H : Comonad C} (h : G ⟶ H) :
    precompComonad (D := D) G ⟶ precompComonad (D := D) H where
  toNatTrans :=
    { app := fun R => Functor.whiskerRight h.toNatTrans R
      naturality := fun R₁ R₂ f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact (f.naturality (h.app X)).symm
    }
  app_ε := fun R => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, precompComonad]
    rw [← Functor.map_comp, h.app_ε X]
  app_δ := fun R => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.comp_map, precompComonad]
    have key : h.app X ≫ H.δ.app X =
        G.δ.app X ≫ G.map (h.app X) ≫ h.app (H.obj X) := by
      calc
        h.app X ≫ H.δ.app X
            = G.δ.app X ≫ h.app (G.obj X) ≫ H.map (h.app X) := h.app_δ X
        _ = G.δ.app X ≫ (h.app (G.obj X) ≫ H.map (h.app X)) := rfl
        _ = G.δ.app X ≫ (G.map (h.app X) ≫ h.app (H.obj X)) := by
              rw [← h.toNatTrans.naturality (h.app X)]
        _ = G.δ.app X ≫ G.map (h.app X) ≫ h.app (H.obj X) := rfl
    calc
      R.map (h.app X) ≫ R.map (H.δ.app X)
          = R.map (h.app X ≫ H.δ.app X) := by rw [← Functor.map_comp]
      _ = R.map (G.δ.app X ≫ G.map (h.app X) ≫ h.app (H.obj X)) := by rw [key]
      _ = R.map (G.δ.app X) ≫ R.map (G.map (h.app X)) ≫ R.map (h.app (H.obj X)) := by
              rw [Functor.map_comp, Functor.map_comp]

@[simp]
lemma precompComonadHom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {G H : Comonad C} (h : G ⟶ H) (R : C ⥤ D) :
    (precompComonadHom (D := D) h).toNatTrans.app R =
      Functor.whiskerRight h.toNatTrans R := rfl

@[simp]
lemma precompComonadHom_app_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {G H : Comonad C} (h : G ⟶ H) (R : C ⥤ D) (X : C) :
    ((precompComonadHom (D := D) h).toNatTrans.app R).app X =
      R.map (h.app X) := rfl

/-- The comonad morphism on `A ⥤ C` induced by `h : G ⟶ H`, via whiskering on
the left. Dual of `Monad.postcompMonadHom`. -/
def postcompComonadHom {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {G H : Comonad C} (h : G ⟶ H) :
    postcompComonad (A := A) G ⟶ postcompComonad (A := A) H where
  toNatTrans :=
    { app := fun L => Functor.whiskerLeft L h.toNatTrans
      naturality := fun L₁ L₂ f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact h.toNatTrans.naturality (f.app X)
    }
  app_ε := fun L => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, postcompComonad]
    exact h.app_ε (L.obj X)
  app_δ := fun L => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      postcompComonad]
    exact h.app_δ (L.obj X)

@[simp]
lemma postcompComonadHom_app {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {G H : Comonad C} (h : G ⟶ H) (L : A ⥤ C) :
    (postcompComonadHom (A := A) h).toNatTrans.app L =
      Functor.whiskerLeft L h.toNatTrans := rfl

@[simp]
lemma postcompComonadHom_app_app {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {G H : Comonad C} (h : G ⟶ H) (L : A ⥤ C) (X : A) :
    ((postcompComonadHom (A := A) h).toNatTrans.app L).app X =
      h.app (L.obj X) := rfl

/-- Given a comonad morphism `h : G ⟶ H`, push coalgebras for `G` forward to
coalgebras for `H`. Covariant dual of Mathlib `Monad.algebraFunctorOfMonadHom`. -/
def coalgebraFunctorOfComonadHom {C : Type u₁} [Category.{v₁} C] {G H : Comonad C}
    (h : G ⟶ H) : Coalgebra G ⥤ Coalgebra H where
  obj A :=
    { A := A.A
      a := A.a ≫ h.app A.A
      counit := by
        have : (A.a ≫ h.app A.A) ≫ H.ε.app A.A = A.a ≫ G.ε.app A.A := by
          rw [Category.assoc, h.app_ε]
        rw [this]
        exact A.counit
      coassoc := by
        have hδ : h.app A.A ≫ H.δ.app A.A =
            G.δ.app A.A ≫ h.app (G.obj A.A) ≫ H.map (h.app A.A) :=
          h.app_δ A.A
        have hco : A.a ≫ G.δ.app A.A = A.a ≫ G.map A.a := A.coassoc
        have hnat : G.map A.a ≫ h.app (G.obj A.A) =
            h.app A.A ≫ H.map A.a :=
          h.toNatTrans.naturality A.a
        calc
          (A.a ≫ h.app A.A) ≫ H.δ.app A.A
              = A.a ≫ (h.app A.A ≫ H.δ.app A.A) := by
                rw [Category.assoc]
          _ = A.a ≫ (G.δ.app A.A ≫ h.app (G.obj A.A) ≫ H.map (h.app A.A)) := by
                rw [hδ]
          _ = (A.a ≫ G.δ.app A.A) ≫ h.app (G.obj A.A) ≫ H.map (h.app A.A) := by
                rw [← Category.assoc, ← Category.assoc]
          _ = (A.a ≫ G.map A.a) ≫ h.app (G.obj A.A) ≫ H.map (h.app A.A) := by
                rw [hco]
          _ = A.a ≫ (G.map A.a ≫ h.app (G.obj A.A)) ≫ H.map (h.app A.A) := by
                rw [Category.assoc, Category.assoc]
          _ = A.a ≫ (h.app A.A ≫ H.map A.a) ≫ H.map (h.app A.A) := by
                rw [hnat]
          _ = (A.a ≫ h.app A.A) ≫ (H.map A.a ≫ H.map (h.app A.A)) := by
                simp only [Category.assoc]
          _ = (A.a ≫ h.app A.A) ≫ H.map (A.a ≫ h.app A.A) := by
                rw [Functor.map_comp] }
  map {X Y} f :=
    { f := f.f
      h := by
        have hnat : G.map f.f ≫ h.app Y.A = h.app X.A ≫ H.map f.f :=
          h.toNatTrans.naturality (f.f)
        calc
          (X.a ≫ h.app X.A) ≫ H.map f.f
              = X.a ≫ (h.app X.A ≫ H.map f.f) := by
                rw [Category.assoc]
          _ = X.a ≫ (G.map f.f ≫ h.app Y.A) := by
                rw [← hnat]
          _ = (X.a ≫ G.map f.f) ≫ h.app Y.A := by
                rw [← Category.assoc]
          _ = (f.f ≫ Y.a) ≫ h.app Y.A := by
                rw [f.h]
          _ = f.f ≫ (Y.a ≫ h.app Y.A) := by
                rw [Category.assoc] }

@[simp]
lemma coalgebraFunctorOfComonadHom_obj_A {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} (h : G ⟶ H) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHom h).obj A).A = A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHom_obj_a {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} (h : G ⟶ H) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHom h).obj A).a = A.a ≫ h.app A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHom_map_f {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} (h : G ⟶ H) {A B : Coalgebra G} (f : A ⟶ B) :
    ((coalgebraFunctorOfComonadHom h).map f).f = f.f := rfl

/-- The identity comonad morphism induces the identity functor on coalgebras.

Covariant dual of Mathlib `Monad.algebraFunctorOfMonadHomId`, with transparent
identity carrier components. -/
def coalgebraFunctorOfComonadHomId {C : Type u₁} [Category.{v₁} C]
    {G : Comonad C} :
    coalgebraFunctorOfComonadHom (𝟙 G) ≅ 𝟭 (Coalgebra G) :=
  NatIso.ofComponents
    (fun X => Coalgebra.isoMk (Iso.refl _) (by simp [coalgebraFunctorOfComonadHom]))
    (fun f => by ext; simp [coalgebraFunctorOfComonadHom])

/-- Composition of comonad morphisms gives the composition of the corresponding
coalgebra functors, in covariant order.

Covariant dual of Mathlib `Monad.algebraFunctorOfMonadHomComp`, which reverses
the order for contravariant restriction; pushforward here preserves the order. -/
def coalgebraFunctorOfComonadHomComp {C : Type u₁} [Category.{v₁} C]
    {G H K : Comonad C} (f : G ⟶ H) (g : H ⟶ K) :
    coalgebraFunctorOfComonadHom (f ≫ g) ≅
      coalgebraFunctorOfComonadHom f ⋙ coalgebraFunctorOfComonadHom g :=
  NatIso.ofComponents
    (fun X => Coalgebra.isoMk (Iso.refl _)
      (by simp [coalgebraFunctorOfComonadHom, Category.assoc]))
    (fun f => by ext; simp [coalgebraFunctorOfComonadHom])

/-- Equal comonad morphisms induce isomorphic coalgebra functors.

Covariant dual of Mathlib `Monad.algebraFunctorOfMonadHomEq`, with transparent
identity carrier components. -/
def coalgebraFunctorOfComonadHomEq {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} {f g : G ⟶ H} (h : f = g) :
    coalgebraFunctorOfComonadHom f ≅ coalgebraFunctorOfComonadHom g :=
  NatIso.ofComponents
    (fun X => Coalgebra.isoMk (Iso.refl _) (by simp [coalgebraFunctorOfComonadHom, h]))
    (fun f => by ext; simp [coalgebraFunctorOfComonadHom])

@[simp]
lemma coalgebraFunctorOfComonadHomId_hom_f {C : Type u₁} [Category.{v₁} C]
    {G : Comonad C} (A : Coalgebra G) :
    (coalgebraFunctorOfComonadHomId.hom.app A).f = 𝟙 A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHomId_inv_f {C : Type u₁} [Category.{v₁} C]
    {G : Comonad C} (A : Coalgebra G) :
    (coalgebraFunctorOfComonadHomId.inv.app A).f = 𝟙 A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHomComp_hom_f {C : Type u₁} [Category.{v₁} C]
    {G H K : Comonad C} (f : G ⟶ H) (g : H ⟶ K) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomComp f g).hom.app A).f = 𝟙 A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHomComp_inv_f {C : Type u₁} [Category.{v₁} C]
    {G H K : Comonad C} (f : G ⟶ H) (g : H ⟶ K) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomComp f g).inv.app A).f = 𝟙 A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHomEq_hom_f {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} {f g : G ⟶ H} (h : f = g) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomEq h).hom.app A).f = 𝟙 A.A := rfl

@[simp]
lemma coalgebraFunctorOfComonadHomEq_inv_f {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} {f g : G ⟶ H} (h : f = g) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomEq h).inv.app A).f = 𝟙 A.A := rfl

/-- A right `G`-comodule with values in `D`: a coalgebra for precomposition
with `G`, with underlying functor `R : C ⥤ D` and coaction `R ⟶ G ⋙ R`. -/
abbrev RightComodule {C : Type u₁} [Category.{v₁} C] (G : Comonad C) (D : Type u₂)
    [Category.{v₂} D] :=
  (precompComonad (D := D) G).Coalgebra

namespace RightComodule

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {G : Comonad C}

/-- The underlying functor of a right comodule. -/
abbrev functor (M : RightComodule G D) : C ⥤ D := M.A

/-- The coaction of a right comodule. -/
abbrev coaction (M : RightComodule G D) : M.functor ⟶ G ⋙ M.functor := M.a

/-- The underlying functor is computed pointwise. -/
@[simp]
lemma functor_obj (M : RightComodule G D) (X : C) : M.functor.obj X = M.A.obj X :=
  rfl

/-- The coaction is the coalgebra structure map. -/
@[simp]
lemma coaction_app (M : RightComodule G D) (X : C) :
    M.coaction.app X = M.a.app X := rfl

/-- Counit law of a right comodule, in components. -/
lemma counit_app (M : RightComodule G D) (X : C) :
    M.coaction.app X ≫ M.functor.map (G.ε.app X) = 𝟙 (M.functor.obj X) := by
  have h := congr_app M.counit X
  exact h

/-- Coassociativity law of a right comodule, in components. -/
lemma coassoc_app (M : RightComodule G D) (X : C) :
    M.coaction.app X ≫ M.functor.map (G.δ.app X) =
      M.coaction.app X ≫ M.coaction.app (G.obj X) := by
  have h := congr_app M.coassoc X
  exact h

/-- Constructor for right comodules from a functor, a coaction, and the two
component laws. -/
abbrev mk (R : C ⥤ D) (coact : R ⟶ G ⋙ R)
    (hcounit : ∀ X, coact.app X ≫ R.map (G.ε.app X) = 𝟙 (R.obj X))
    (hcoassoc : ∀ X, coact.app X ≫ R.map (G.δ.app X) =
      coact.app X ≫ coact.app (G.obj X)) :
    RightComodule G D where
  A := R
  a := coact
  counit := by ext X; exact hcounit X
  coassoc := by ext X; exact hcoassoc X

/-- Compatibility of a right comodule morphism with the coactions. -/
lemma hom_condition {M N : RightComodule G D} (f : M ⟶ N) :
    M.coaction ≫ Functor.whiskerLeft G.toFunctor f.f = f.f ≫ N.coaction :=
  f.h

/-- Compatibility of a right comodule morphism with the coactions, in
components. -/
lemma hom_condition_app {M N : RightComodule G D} (f : M ⟶ N) (X : C) :
    M.coaction.app X ≫ f.f.app (G.obj X) = f.f.app X ≫ N.coaction.app X := by
  have h := congr_app f.h X
  exact h

/-- Extensionality for right comodule morphisms. -/
@[ext]
lemma hom_ext {M N : RightComodule G D} {f g : M ⟶ N} (h : f.f = g.f) : f = g :=
  Coalgebra.Hom.ext' _ _ _ _ h

/-- Identity right comodule morphisms are identities underneath. -/
@[simp]
lemma id_f (M : RightComodule G D) : (𝟙 M : M ⟶ M).f = 𝟙 M.functor := rfl

/-- Composition of right comodule morphisms is composition underneath. -/
@[simp]
lemma comp_f {M N P : RightComodule G D} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).f = f.f ≫ g.f := rfl

end RightComodule

/-- A left `G`-comodule indexed by `A`: a coalgebra for postcomposition with
`G`, with underlying functor `L : A ⥤ C` and coaction `L ⟶ L ⋙ G`. -/
abbrev LeftComodule {C : Type u₁} [Category.{v₁} C] (A : Type u₃)
    [Category.{v₃} A] (G : Comonad C) :=
  (postcompComonad (A := A) G).Coalgebra

namespace LeftComodule

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₃} [Category.{v₃} A]
variable {G : Comonad C}

/-- The underlying functor of a left comodule. -/
abbrev functor (M : LeftComodule A G) : A ⥤ C := M.A

/-- The coaction of a left comodule. -/
abbrev coaction (M : LeftComodule A G) : M.functor ⟶ M.functor ⋙ G.toFunctor :=
  M.a

/-- The underlying functor is computed pointwise. -/
@[simp]
lemma functor_obj (M : LeftComodule A G) (X : A) : M.functor.obj X = M.A.obj X :=
  rfl

/-- The coaction is the coalgebra structure map. -/
@[simp]
lemma coaction_app (M : LeftComodule A G) (X : A) :
    M.coaction.app X = M.a.app X := rfl

/-- Counit law of a left comodule, in components. -/
lemma counit_app (M : LeftComodule A G) (X : A) :
    M.coaction.app X ≫ G.ε.app (M.functor.obj X) = 𝟙 (M.functor.obj X) := by
  have h := congr_app M.counit X
  exact h

/-- Coassociativity law of a left comodule, in components. -/
lemma coassoc_app (M : LeftComodule A G) (X : A) :
    M.coaction.app X ≫ G.δ.app (M.functor.obj X) =
      M.coaction.app X ≫ G.map (M.coaction.app X) := by
  have h := congr_app M.coassoc X
  exact h

/-- Constructor for left comodules from a functor, a coaction, and the two
component laws. -/
abbrev mk (L : A ⥤ C) (coact : L ⟶ L ⋙ G.toFunctor)
    (hcounit : ∀ X, coact.app X ≫ G.ε.app (L.obj X) = 𝟙 (L.obj X))
    (hcoassoc : ∀ X, coact.app X ≫ G.δ.app (L.obj X) =
      coact.app X ≫ G.map (coact.app X)) :
    LeftComodule A G where
  A := L
  a := coact
  counit := by ext X; exact hcounit X
  coassoc := by ext X; exact hcoassoc X

/-- Compatibility of a left comodule morphism with the coactions. -/
lemma hom_condition {M N : LeftComodule A G} (f : M ⟶ N) :
    M.coaction ≫ Functor.whiskerRight f.f G.toFunctor = f.f ≫ N.coaction :=
  f.h

/-- Compatibility of a left comodule morphism with the coactions, in
components. -/
lemma hom_condition_app {M N : LeftComodule A G} (f : M ⟶ N) (X : A) :
    M.coaction.app X ≫ G.map (f.f.app X) = f.f.app X ≫ N.coaction.app X := by
  have h := congr_app f.h X
  exact h

/-- Extensionality for left comodule morphisms. -/
@[ext]
lemma hom_ext {M N : LeftComodule A G} {f g : M ⟶ N} (h : f.f = g.f) : f = g :=
  Coalgebra.Hom.ext' _ _ _ _ h

/-- Identity left comodule morphisms are identities underneath. -/
@[simp]
lemma id_f (M : LeftComodule A G) : (𝟙 M : M ⟶ M).f = 𝟙 M.functor := rfl

/-- Composition of left comodule morphisms is composition underneath. -/
@[simp]
lemma comp_f {M N P : LeftComodule A G} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).f = f.f ≫ g.f := rfl

end LeftComodule

end Comonad

end CategoryTheory
