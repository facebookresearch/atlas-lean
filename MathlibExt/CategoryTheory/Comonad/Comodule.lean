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

Let `G` be a comonad on `C`. Precomposition defines a comonad on `C ⥤ D` by `R ↦ G ⋙ R`;
postcomposition defines one on `A ⥤ C` by `L ↦ L ⋙ G`.

A right comodule is a coalgebra for the first comonad, with coaction `R ⟶ G ⋙ R`. A left
comodule is a coalgebra for the second, with coaction `L ⟶ L ⋙ G`. Their component counit and
coassociativity laws describe the two endpoint coactions of a two-sided cobar construction.
Morphisms are natural transformations commuting with these coactions.

A comonad morphism `G → H` transports coalgebras covariantly by composing their coactions with
its carrier components. Identity, composition, and equality comparisons have identity carrier
maps. All three categories and their morphism universes are independent.
-/

@[expose] public section

namespace CategoryTheory

namespace Comonad

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- The comonad on functors given by precomposition.

For a comonad `G` on `C`, the functor-category comonad on `C ⥤ D` sends `R` to `G ⋙ R`; its
counit and comultiplication are `R` applied to those of `G`. -/
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

/-- The object formula for the precomposition comonad.

At a functor `R` and object `X`, its value is `R(G(X))`. -/
@[simp]
lemma precompComonad_obj_obj {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {G : Comonad C} (R : C ⥤ D) (X : C) :
    ((precompComonad G).toFunctor.obj R).obj X = R.obj (G.obj X) := rfl

/-- The comonad on functors given by postcomposition.

For a comonad `G` on `C`, the functor-category comonad on `A ⥤ C` sends `L` to `L ⋙ G`, with
counit and comultiplication evaluated at `L(a)`. -/
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

/-- The object formula for the postcomposition comonad.

At a functor `L` and object `a`, its value is `G(L(a))`. -/
@[simp]
lemma postcompComonad_obj_obj {C : Type u₁} [Category.{v₁} C] {A : Type u₃}
    [Category.{v₃} A] {G : Comonad C} (L : A ⥤ C) (X : A) :
    ((postcompComonad G).toFunctor.obj L).obj X = G.obj (L.obj X) := rfl

/-- The precomposition comonad morphism of a comonad transformation.

For `h : G → H`, applying each functor `R : C ⥤ D` to the components of `h` gives a morphism
between the precomposition comonads. -/
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

/-- The functor component of a precomposition comonad morphism.

At `R`, the induced transformation is `h` whiskered on the right by `R`. -/
@[simp]
lemma precompComonadHom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {G H : Comonad C} (h : G ⟶ H) (R : C ⥤ D) :
    (precompComonadHom (D := D) h).toNatTrans.app R =
      Functor.whiskerRight h.toNatTrans R := rfl

/-- The object component of a precomposition comonad morphism.

At `R` and `X`, the induced map is `R.map(h.app X)`. -/
@[simp]
lemma precompComonadHom_app_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {G H : Comonad C} (h : G ⟶ H) (R : C ⥤ D) (X : C) :
    ((precompComonadHom (D := D) h).toNatTrans.app R).app X =
      R.map (h.app X) := rfl

/-- The postcomposition comonad morphism of a comonad transformation.

For `h : G → H`, evaluating `h` on every value of `L : A ⥤ C` gives a morphism between the
postcomposition comonads. -/
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

/-- The functor component of a postcomposition comonad morphism.

At `L`, the induced transformation is `h` whiskered on the left by `L`. -/
@[simp]
lemma postcompComonadHom_app {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {G H : Comonad C} (h : G ⟶ H) (L : A ⥤ C) :
    (postcompComonadHom (A := A) h).toNatTrans.app L =
      Functor.whiskerLeft L h.toNatTrans := rfl

/-- The object component of a postcomposition comonad morphism.

At `L` and `a`, the induced map is `h.app(L(a))`. -/
@[simp]
lemma postcompComonadHom_app_app {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {G H : Comonad C} (h : G ⟶ H) (L : A ⥤ C) (X : A) :
    ((postcompComonadHom (A := A) h).toNatTrans.app L).app X =
      h.app (L.obj X) := rfl

/-- Covariant transport of coalgebras along a comonad morphism.

For `h : G → H`, a `G`-coalgebra `(X,a)` becomes an `H`-coalgebra with the same carrier and
coaction `a ≫ h.app X`. Morphisms retain their underlying carrier maps. -/
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

/-- The carrier of a transported comonad coalgebra.

Transport along a comonad morphism retains the coalgebra's underlying category object. -/
@[simp]
lemma coalgebraFunctorOfComonadHom_obj_A {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} (h : G ⟶ H) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHom h).obj A).A = A.A := rfl

/-- The coaction of a transported comonad coalgebra.

The transported coaction is the given coaction followed by the comonad morphism component at
the carrier. -/
@[simp]
lemma coalgebraFunctorOfComonadHom_obj_a {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} (h : G ⟶ H) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHom h).obj A).a = A.a ≫ h.app A.A := rfl

/-- The carrier map of a transported coalgebra morphism.

Coalgebra transport along a comonad morphism retains the underlying morphism. -/
@[simp]
lemma coalgebraFunctorOfComonadHom_map_f {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} (h : G ⟶ H) {A B : Coalgebra G} (f : A ⟶ B) :
    ((coalgebraFunctorOfComonadHom h).map f).f = f.f := rfl

/-- The identity comparison of comonad coalgebra transport.

Transport along the identity comonad morphism is naturally isomorphic to the identity functor
on its coalgebra category. -/
def coalgebraFunctorOfComonadHomId {C : Type u₁} [Category.{v₁} C]
    {G : Comonad C} :
    coalgebraFunctorOfComonadHom (𝟙 G) ≅ 𝟭 (Coalgebra G) :=
  NatIso.ofComponents
    (fun X => Coalgebra.isoMk (Iso.refl _) (by simp [coalgebraFunctorOfComonadHom]))
    (fun f => by ext; simp [coalgebraFunctorOfComonadHom])

/-- The composition comparison of comonad coalgebra transport.

Transport along `G → H → K` is naturally isomorphic to first transporting along `G → H` and
then along `H → K`. -/
def coalgebraFunctorOfComonadHomComp {C : Type u₁} [Category.{v₁} C]
    {G H K : Comonad C} (f : G ⟶ H) (g : H ⟶ K) :
    coalgebraFunctorOfComonadHom (f ≫ g) ≅
      coalgebraFunctorOfComonadHom f ⋙ coalgebraFunctorOfComonadHom g :=
  NatIso.ofComponents
    (fun X => Coalgebra.isoMk (Iso.refl _)
      (by simp [coalgebraFunctorOfComonadHom, Category.assoc]))
    (fun f => by ext; simp [coalgebraFunctorOfComonadHom])

/-- The comparison of coalgebra transports along equal comonad morphisms.

Equal comonad morphisms induce naturally isomorphic coalgebra transport functors, with
identity maps on the carriers. -/
def coalgebraFunctorOfComonadHomEq {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} {f g : G ⟶ H} (h : f = g) :
    coalgebraFunctorOfComonadHom f ≅ coalgebraFunctorOfComonadHom g :=
  NatIso.ofComponents
    (fun X => Coalgebra.isoMk (Iso.refl _) (by simp [coalgebraFunctorOfComonadHom, h]))
    (fun f => by ext; simp [coalgebraFunctorOfComonadHom])

/-- The forward carrier map of identity coalgebra transport comparison.

The forward component is the identity on each coalgebra carrier. -/
@[simp]
lemma coalgebraFunctorOfComonadHomId_hom_f {C : Type u₁} [Category.{v₁} C]
    {G : Comonad C} (A : Coalgebra G) :
    (coalgebraFunctorOfComonadHomId.hom.app A).f = 𝟙 A.A := rfl

/-- The inverse carrier map of identity coalgebra transport comparison.

The inverse component is the identity on each coalgebra carrier. -/
@[simp]
lemma coalgebraFunctorOfComonadHomId_inv_f {C : Type u₁} [Category.{v₁} C]
    {G : Comonad C} (A : Coalgebra G) :
    (coalgebraFunctorOfComonadHomId.inv.app A).f = 𝟙 A.A := rfl

/-- The forward carrier map of composite coalgebra transport comparison.

The forward composition comparison is the identity on each coalgebra carrier. -/
@[simp]
lemma coalgebraFunctorOfComonadHomComp_hom_f {C : Type u₁} [Category.{v₁} C]
    {G H K : Comonad C} (f : G ⟶ H) (g : H ⟶ K) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomComp f g).hom.app A).f = 𝟙 A.A := rfl

/-- The inverse carrier map of composite coalgebra transport comparison.

The inverse composition comparison is the identity on each coalgebra carrier. -/
@[simp]
lemma coalgebraFunctorOfComonadHomComp_inv_f {C : Type u₁} [Category.{v₁} C]
    {G H K : Comonad C} (f : G ⟶ H) (g : H ⟶ K) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomComp f g).inv.app A).f = 𝟙 A.A := rfl

/-- The forward carrier map for equal coalgebra transports.

The comparison of transports along equal comonad morphisms has identity forward carrier maps. -/
@[simp]
lemma coalgebraFunctorOfComonadHomEq_hom_f {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} {f g : G ⟶ H} (h : f = g) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomEq h).hom.app A).f = 𝟙 A.A := rfl

/-- The inverse carrier map for equal coalgebra transports.

The comparison of transports along equal comonad morphisms has identity inverse carrier maps. -/
@[simp]
lemma coalgebraFunctorOfComonadHomEq_inv_f {C : Type u₁} [Category.{v₁} C]
    {G H : Comonad C} {f g : G ⟶ H} (h : f = g) (A : Coalgebra G) :
    ((coalgebraFunctorOfComonadHomEq h).inv.app A).f = 𝟙 A.A := rfl

/-- The category of right comodule functors for a comonad.

For `G` on `C`, a right comodule with values in `D` is a coalgebra for the precomposition
comonad on `C ⥤ D`, with coaction `R → G ⋙ R`. -/
abbrev RightComodule {C : Type u₁} [Category.{v₁} C] (G : Comonad C) (D : Type u₂)
    [Category.{v₂} D] :=
  (precompComonad (D := D) G).Coalgebra

namespace RightComodule

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {G : Comonad C}

/-- The underlying functor of a right comonad comodule.

A right `G`-comodule with values in `D` has underlying functor `R : C ⥤ D`. -/
abbrev functor (M : RightComodule G D) : C ⥤ D := M.A

/-- The right-comodule coaction transformation.

The coaction is a natural transformation `R ⟶ G ⋙ R`, with component `R(X) → R(G(X))`. -/
abbrev coaction (M : RightComodule G D) : M.functor ⟶ G ⋙ M.functor := M.a

/-- The pointwise carrier of a right comodule functor.

The underlying functor accessor has the same object values as the functor-category coalgebra
carrier. -/
@[simp]
lemma functor_obj (M : RightComodule G D) (X : C) : M.functor.obj X = M.A.obj X :=
  rfl

/-- The pointwise coalgebra map of a right comodule.

The right coaction component equals the coalgebra structure-map component. -/
@[simp]
lemma coaction_app (M : RightComodule G D) (X : C) :
    M.coaction.app X = M.a.app X := rfl

/-- The component counit law of a right comodule.

The coaction at `X` followed by `R.map(ε_X)` is the identity on `R(X)`. -/
lemma counit_app (M : RightComodule G D) (X : C) :
    M.coaction.app X ≫ M.functor.map (G.ε.app X) = 𝟙 (M.functor.obj X) := by
  have h := congr_app M.counit X
  exact h

/-- The component coassociativity law of a right comodule.

The coaction at `X` followed by `R.map(δ_X)` equals the coaction at `X` followed by the
coaction at `G(X)`. -/
lemma coassoc_app (M : RightComodule G D) (X : C) :
    M.coaction.app X ≫ M.functor.map (G.δ.app X) =
      M.coaction.app X ≫ M.coaction.app (G.obj X) := by
  have h := congr_app M.coassoc X
  exact h

/-- A right comodule from a functor and coaction laws.

A functor `R : C ⥤ D` and coaction `R → G ⋙ R` satisfying the component counit and
coassociativity equations define a right comodule. -/
abbrev mk (R : C ⥤ D) (coact : R ⟶ G ⋙ R)
    (hcounit : ∀ X, coact.app X ≫ R.map (G.ε.app X) = 𝟙 (R.obj X))
    (hcoassoc : ∀ X, coact.app X ≫ R.map (G.δ.app X) =
      coact.app X ≫ coact.app (G.obj X)) :
    RightComodule G D where
  A := R
  a := coact
  counit := by ext X; exact hcounit X
  coassoc := by ext X; exact hcoassoc X

/-- The coaction equation of a right comodule morphism.

A transformation `f : M → N` satisfies the square from the source coaction and
`G`-precomposition of `f` to `f` followed by the target coaction. -/
lemma hom_condition {M N : RightComodule G D} (f : M ⟶ N) :
    M.coaction ≫ Functor.whiskerLeft G.toFunctor f.f = f.f ≫ N.coaction :=
  f.h

/-- The component equation of a right comodule morphism.

At `X`, one has `coact_M(X) ≫ f(G(X)) = f(X) ≫ coact_N(X)`. -/
lemma hom_condition_app {M N : RightComodule G D} (f : M ⟶ N) (X : C) :
    M.coaction.app X ≫ f.f.app (G.obj X) = f.f.app X ≫ N.coaction.app X := by
  have h := congr_app f.h X
  exact h

/-- Extensionality of right comodule morphisms.

Two right comodule morphisms are equal if their underlying natural transformations are equal. -/
@[ext]
lemma hom_ext {M N : RightComodule G D} {f g : M ⟶ N} (h : f.f = g.f) : f = g :=
  Coalgebra.Hom.ext' _ _ _ _ h

/-- The underlying identity of a right comodule.

The identity comodule morphism has the identity transformation of the underlying functor. -/
@[simp]
lemma id_f (M : RightComodule G D) : (𝟙 M : M ⟶ M).f = 𝟙 M.functor := rfl

/-- The underlying composite of right comodule morphisms.

Composition of right comodule morphisms is composition of their underlying natural
transformations. -/
@[simp]
lemma comp_f {M N P : RightComodule G D} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).f = f.f ≫ g.f := rfl

end RightComodule

/-- The category of left comodule functors for a comonad.

For `G` on `C`, a left comodule indexed by `A` is a coalgebra for the postcomposition comonad
on `A ⥤ C`, with coaction `L → L ⋙ G`. -/
abbrev LeftComodule {C : Type u₁} [Category.{v₁} C] (A : Type u₃)
    [Category.{v₃} A] (G : Comonad C) :=
  (postcompComonad (A := A) G).Coalgebra

namespace LeftComodule

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₃} [Category.{v₃} A]
variable {G : Comonad C}

/-- The underlying functor of a left comonad comodule.

A left `G`-comodule indexed by `A` has underlying functor `L : A ⥤ C`. -/
abbrev functor (M : LeftComodule A G) : A ⥤ C := M.A

/-- The left-comodule coaction transformation.

The coaction is a natural transformation `L ⟶ L ⋙ G`, with component `L(a) → G(L(a))`. -/
abbrev coaction (M : LeftComodule A G) : M.functor ⟶ M.functor ⋙ G.toFunctor :=
  M.a

/-- The pointwise carrier of a left comodule functor.

The underlying functor accessor retains the object values of the functor-category coalgebra
carrier. -/
@[simp]
lemma functor_obj (M : LeftComodule A G) (X : A) : M.functor.obj X = M.A.obj X :=
  rfl

/-- The pointwise coalgebra map of a left comodule.

The left coaction component equals the coalgebra structure-map component. -/
@[simp]
lemma coaction_app (M : LeftComodule A G) (X : A) :
    M.coaction.app X = M.a.app X := rfl

/-- The component counit law of a left comodule.

The coaction at `a` followed by `ε_(L(a))` is the identity on `L(a)`. -/
lemma counit_app (M : LeftComodule A G) (X : A) :
    M.coaction.app X ≫ G.ε.app (M.functor.obj X) = 𝟙 (M.functor.obj X) := by
  have h := congr_app M.counit X
  exact h

/-- The component coassociativity law of a left comodule.

The coaction at `a` followed by `δ_(L(a))` equals the coaction followed by `G` of that
coaction. -/
lemma coassoc_app (M : LeftComodule A G) (X : A) :
    M.coaction.app X ≫ G.δ.app (M.functor.obj X) =
      M.coaction.app X ≫ G.map (M.coaction.app X) := by
  have h := congr_app M.coassoc X
  exact h

/-- A left comodule from a functor and coaction laws.

A functor `L : A ⥤ C` and coaction `L → L ⋙ G` satisfying the component counit and
coassociativity equations define a left comodule. -/
abbrev mk (L : A ⥤ C) (coact : L ⟶ L ⋙ G.toFunctor)
    (hcounit : ∀ X, coact.app X ≫ G.ε.app (L.obj X) = 𝟙 (L.obj X))
    (hcoassoc : ∀ X, coact.app X ≫ G.δ.app (L.obj X) =
      coact.app X ≫ G.map (coact.app X)) :
    LeftComodule A G where
  A := L
  a := coact
  counit := by ext X; exact hcounit X
  coassoc := by ext X; exact hcoassoc X

/-- The coaction equation of a left comodule morphism.

A natural transformation of left comodules intertwines the source coaction with its
postcomposition by `G` and the target coaction. -/
lemma hom_condition {M N : LeftComodule A G} (f : M ⟶ N) :
    M.coaction ≫ Functor.whiskerRight f.f G.toFunctor = f.f ≫ N.coaction :=
  f.h

/-- The component equation of a left comodule morphism.

At `a`, one has `coact_M(a) ≫ G.map(f(a)) = f(a) ≫ coact_N(a)`. -/
lemma hom_condition_app {M N : LeftComodule A G} (f : M ⟶ N) (X : A) :
    M.coaction.app X ≫ G.map (f.f.app X) = f.f.app X ≫ N.coaction.app X := by
  have h := congr_app f.h X
  exact h

/-- Extensionality of left comodule morphisms.

Two left comodule morphisms are equal if their underlying natural transformations are equal. -/
@[ext]
lemma hom_ext {M N : LeftComodule A G} {f g : M ⟶ N} (h : f.f = g.f) : f = g :=
  Coalgebra.Hom.ext' _ _ _ _ h

/-- The underlying identity of a left comodule.

The identity comodule morphism has the identity transformation of its underlying functor. -/
@[simp]
lemma id_f (M : LeftComodule A G) : (𝟙 M : M ⟶ M).f = 𝟙 M.functor := rfl

/-- The underlying composite of left comodule morphisms.

Composition of left comodule morphisms is composition of their underlying natural
transformations. -/
@[simp]
lemma comp_f {M N P : LeftComodule A G} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).f = f.f ≫ g.f := rfl

end LeftComodule

end Comonad

end CategoryTheory
