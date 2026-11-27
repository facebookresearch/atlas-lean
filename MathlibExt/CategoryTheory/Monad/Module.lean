/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Left and right module functors for a monad

For a monad `T` on `C` we construct the two ordinary-Cat module monads:

* the monad on `C ⥤ D` given by precomposition `R ↦ T ⋙ R`, i.e. `R` after `T`
  in diagrammatic order (`R.comp T`);
* the monad on `A ⥤ C` given by postcomposition `L ↦ L ⋙ T`, i.e. `T` after `L`
  (`T.comp L` diagrammatically written `L ⋙ T`).

A right `T`-module functor `R : C ⥤ D` is an algebra for the first monad,
with action `T ⋙ R ⟶ R`.  A left `T`-module functor `L : A ⥤ C` is an algebra
for the second monad, with action `L ⋙ T ⟶ L`.  The definitions re-use
`Monad.Algebra` and do not duplicate its structure.

We provide documented underlying-functor and action accessors, stable `simp`
lemmas for components, and the inherited unit/associativity laws in the
expected module form.  The regular module carried by `T` itself and the free
left-module functor `X ↦ X ⋙ T` (needed later for `B(R,T,T X)`) are included.

We then extend the API with outer-category whiskering:

* postcomposition of a right `T`-module `R : C ⥤ D` along `K : D ⥤ E`,
  yielding a right module `R ⋙ K : C ⥤ E`;
* precomposition of a left `T`-module `L : A ⥤ C` along `K : B ⥤ A`,
  yielding a left module `K ⋙ L : B ⥤ C`.

Both operations induce functors between the Eilenberg–Moore module categories,
with `simp`/component lemmas and identity/composition comparison isomorphisms.
-/

@[expose] public section

namespace CategoryTheory

namespace Monad

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/--
Monad on `C ⥤ D` lifting precomposition with `T`, sending `R` to `T ⋙ R`,
with unit and multiplication from `T` whiskered on the right.
-/
abbrev precompMonad {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (T : Monad C) : Monad (C ⥤ D) where
  toFunctor :=
    { obj := fun R => T ⋙ R
      map := fun f => Functor.whiskerLeft T.toFunctor f
      map_id := fun _ => by ext X; simp
      map_comp := fun _ _ => by ext X; simp
    }
  η :=
    { app := fun R => Functor.whiskerRight T.η R
      naturality := fun R S f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact (f.naturality (T.η.app X)).symm
    }
  μ :=
    { app := fun R => Functor.whiskerRight T.μ R
      naturality := fun R S f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact (f.naturality (T.μ.app X)).symm
    }
  assoc R := by
    ext X : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map]
    change R.map (T.μ.app (T.obj X)) ≫ R.map (T.μ.app X) =
      R.map (T.toFunctor.map (T.μ.app X)) ≫ R.map (T.μ.app X)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact (T.assoc X).symm
  left_unit R := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj]
    rw [← Functor.map_comp]
    rw [T.right_unit X]
    simp
  right_unit R := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← Functor.map_comp]
    rw [T.left_unit X]
    simp

/--
Monad on `A ⥤ C` lifting postcomposition with `T`, sending `L` to `L ⋙ T`,
with unit and multiplication from `T` whiskered on the left.
-/
abbrev postcompMonad {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    (T : Monad C) : Monad (A ⥤ C) where
  toFunctor :=
    { obj := fun L => L ⋙ T
      map := fun f => Functor.whiskerRight f T.toFunctor
      map_id := fun _ => by ext X; simp
      map_comp := fun _ _ => by ext X; simp
    }
  η :=
    { app := fun L => Functor.whiskerLeft L T.η
      naturality := fun L M f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact T.η.naturality (f.app X)
    }
  μ :=
    { app := fun L => Functor.whiskerLeft L T.μ
      naturality := fun L M f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact T.μ.naturality (f.app X)
    }
  assoc L := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    exact T.assoc (L.obj X)
  left_unit L := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    exact T.left_unit (L.obj X)
  right_unit L := by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    exact T.right_unit (L.obj X)

@[simp]
lemma precompMonad_obj_obj {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {T : Monad C} (R : C ⥤ D) (X : C) :
    ((precompMonad T).toFunctor.obj R).obj X = R.obj (T.obj X) := rfl

@[simp]
lemma postcompMonad_obj_obj {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {T : Monad C} (L : A ⥤ C) (X : A) :
    ((postcompMonad T).toFunctor.obj L).obj X = T.obj (L.obj X) := rfl

/-- The monad morphism on `C ⥤ D` induced by `h : T ⟶ S`, via whiskering on the right. -/
def precompMonadHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {T S : Monad C} (h : T ⟶ S) : precompMonad (D := D) T ⟶ precompMonad (D := D) S where
  toNatTrans :=
    { app := fun R => Functor.whiskerRight h.toNatTrans R
      naturality := fun R₁ R₂ f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact (f.naturality (h.app X)).symm
    }
  app_η := fun R => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, precompMonad]
    rw [← Functor.map_comp, h.app_η X]
  app_μ := fun R => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj, Functor.comp_map, precompMonad]
    have eq1 : T.μ.app X ≫ h.app X =
        h.app (T.obj X) ≫ S.map (h.app X) ≫ S.μ.app X := by
      rw [h.app_μ X, h.toNatTrans.naturality (h.app X), Category.assoc]
    calc
      R.map (T.μ.app X) ≫ R.map (h.app X)
          = R.map (T.μ.app X ≫ h.app X) := by rw [← Functor.map_comp]
      _ = R.map (h.app (T.obj X) ≫ S.map (h.app X) ≫ S.μ.app X) := by rw [eq1]
      _ = R.map (h.app (T.obj X)) ≫ R.map (S.map (h.app X) ≫ S.μ.app X) := by
            rw [Functor.map_comp]
      _ = R.map (h.app (T.obj X)) ≫ (R.map (S.map (h.app X)) ≫ R.map (S.μ.app X)) := by
            rw [Functor.map_comp]
      _ = (R.map (h.app (T.obj X)) ≫ R.map (S.map (h.app X))) ≫ R.map (S.μ.app X) := by
            rw [← Category.assoc]

@[simp]
lemma precompMonadHom_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {T S : Monad C} (h : T ⟶ S) (R : C ⥤ D) :
    (precompMonadHom (D := D) h).toNatTrans.app R = Functor.whiskerRight h.toNatTrans R := rfl

@[simp]
lemma precompMonadHom_app_app {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {T S : Monad C} (h : T ⟶ S) (R : C ⥤ D) (X : C) :
    ((precompMonadHom (D := D) h).toNatTrans.app R).app X = R.map (h.app X) := rfl

/-- The monad morphism on `A ⥤ C` induced by `h : T ⟶ S`, via whiskering on the left. -/
def postcompMonadHom {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {T S : Monad C} (h : T ⟶ S) : postcompMonad (A := A) T ⟶ postcompMonad (A := A) S where
  toNatTrans :=
    { app := fun L => Functor.whiskerLeft L h.toNatTrans
      naturality := fun L₁ L₂ f => by
        ext X
        simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
        exact h.toNatTrans.naturality (f.app X)
    }
  app_η := fun L => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, postcompMonad]
    exact h.app_η (L.obj X)
  app_μ := fun L => by
    ext X
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      postcompMonad]
    exact h.app_μ (L.obj X)

@[simp]
lemma postcompMonadHom_app {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {T S : Monad C} (h : T ⟶ S) (L : A ⥤ C) :
    (postcompMonadHom (A := A) h).toNatTrans.app L = Functor.whiskerLeft L h.toNatTrans := rfl

@[simp]
lemma postcompMonadHom_app_app {C : Type u₁} [Category.{v₁} C] {A : Type u₃} [Category.{v₃} A]
    {T S : Monad C} (h : T ⟶ S) (L : A ⥤ C) (X : A) :
    ((postcompMonadHom (A := A) h).toNatTrans.app L).app X = h.app (L.obj X) := rfl

/--
Right `T`-module functor `R : C ⥤ D`: an algebra for the precomposition
  monad `precompMonad T` (`R ↦ T ⋙ R`), with action `T ⋙ R ⟶ R`.
  Reuses `Monad.Algebra`.
-/
abbrev RightModule {C : Type u₁} [Category.{v₁} C] (T : Monad C) (D : Type u₂)
    [Category.{v₂} D] :=
  (precompMonad (D := D) T).Algebra

/--
Left `T`-module functor `L : A ⥤ C`: an algebra for the postcomposition
  monad `postcompMonad T` (`L ↦ L ⋙ T`), with action `L ⋙ T ⟶ L`.
  Reuses `Monad.Algebra`.
-/
abbrev LeftModule {C : Type u₁} [Category.{v₁} C] (A : Type u₃) [Category.{v₃} A]
    (T : Monad C) :=
  (postcompMonad (A := A) T).Algebra

namespace RightModule

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {T : Monad C}

abbrev functor (M : RightModule T D) : C ⥤ D := M.A

abbrev action (M : RightModule T D) : T.toFunctor ⋙ M.functor ⟶ M.functor := M.a

@[simp]
lemma functor_obj (M : RightModule T D) (X : C) : M.functor.obj X = M.A.obj X := rfl

@[simp]
lemma action_app (M : RightModule T D) (X : C) : M.action.app X = M.a.app X := rfl

lemma unit_app (M : RightModule T D) (X : C) :
    M.functor.map (T.η.app X) ≫ M.action.app X = 𝟙 (M.functor.obj X) := by
  have h := congr_app M.unit X
  exact h

lemma assoc_app (M : RightModule T D) (X : C) :
    M.functor.map (T.μ.app X) ≫ M.action.app X =
      M.action.app (T.obj X) ≫ M.action.app X := by
  have h := congr_app M.assoc X
  exact h

abbrev mk (R : C ⥤ D) (act : T.toFunctor ⋙ R ⟶ R)
    (hunit : ∀ X, R.map (T.η.app X) ≫ act.app X = 𝟙 (R.obj X))
    (hassoc : ∀ X, R.map (T.μ.app X) ≫ act.app X = act.app (T.obj X) ≫ act.app X) :
    RightModule T D where
  A := R
  a := act
  unit := by ext X; exact hunit X
  assoc := by ext X; exact hassoc X

lemma hom_condition {M N : RightModule T D} (f : M ⟶ N) :
    Functor.whiskerLeft T.toFunctor f.f ≫ N.action = M.action ≫ f.f :=
  f.h

lemma hom_condition_app {M N : RightModule T D} (f : M ⟶ N) (X : C) :
    f.f.app (T.obj X) ≫ N.action.app X = M.action.app X ≫ f.f.app X := by
  have h := congr_app f.h X
  exact h

/--
Regular right `T`-module on `T` itself for `precompMonad T`: underlying
  functor `T` with action `T ⋙ T ⟶ T` by multiplication `T.μ`.
-/
def regular (T : Monad C) : RightModule T C where
  A := T.toFunctor
  a := T.μ
  unit := by ext X; exact T.right_unit X
  assoc := by ext X; exact T.assoc X

@[simp]
lemma regular_functor (T : Monad C) : (regular T).functor = T.toFunctor := rfl

@[simp]
lemma regular_action (T : Monad C) : (regular T).action = T.μ := rfl

/-! ## Postcomposition / whiskering in the outer target -/

variable {E : Type u₄} [Category.{v₄} E]
variable {F : Type u₅} [Category.{v₅} F]

/-- Postcomposition of a right `T`-module `R : C ⥤ D` along `K : D ⥤ E`. -/
abbrev postcomp (M : RightModule T D) (K : D ⥤ E) : RightModule T E :=
  RightModule.mk (M.A ⋙ K)
    { app := fun X => K.map (M.action.app X)
      naturality := fun X Y f => by
        have h : M.functor.map (T.map f) ≫ M.action.app Y =
            M.action.app X ≫ M.functor.map f := by
          simpa [Functor.comp_map] using M.action.naturality f
        simp only [Functor.comp_map] at *
        rw [← K.map_comp, h, K.map_comp]
    }
    (fun X => by
      simp only [Functor.comp_map] at *
      rw [← K.map_comp, M.unit_app X]
      exact K.map_id (M.functor.obj X)
    )
    (fun X => by
      simp only [Functor.comp_map] at *
      rw [← K.map_comp, M.assoc_app X, K.map_comp]
    )

@[simp]
lemma postcomp_functor (M : RightModule T D) (K : D ⥤ E) :
    (M.postcomp K).functor = M.functor ⋙ K := rfl

@[simp]
lemma postcomp_functor_obj (M : RightModule T D) (K : D ⥤ E) (X : C) :
    (M.postcomp K).functor.obj X = K.obj (M.functor.obj X) := rfl

@[simp]
lemma postcomp_functor_map (M : RightModule T D) (K : D ⥤ E) {X Y : C} (f : X ⟶ Y) :
    (M.postcomp K).functor.map f = K.map (M.functor.map f) := rfl

@[simp]
lemma postcomp_action_app (M : RightModule T D) (K : D ⥤ E) (X : C) :
    (M.postcomp K).action.app X = K.map (M.action.app X) := rfl

lemma postcomp_action_eq_whiskerRight (M : RightModule T D) (K : D ⥤ E) :
    (M.postcomp K).action = Functor.whiskerRight M.action K := by
  ext X
  rfl

@[simp]
lemma postcomp_regular_action_app (K : C ⥤ E) (X : C) :
    ((regular T).postcomp K).action.app X = K.map (T.μ.app X) := rfl

/-- Identity comparison: postcomposition with `𝟭 D` is isomorphic to the module. -/
def postcompIdIso (M : RightModule T D) : M.postcomp (𝟭 D) ≅ M :=
  Iso.refl _

/-- Composition comparison: `(M ⋙ K) ⋙ L ≅ M ⋙ (K ⋙ L)` as right `T`-modules. -/
def postcompCompIso (M : RightModule T D) (K : D ⥤ E) (L : E ⥤ F) :
    (M.postcomp K).postcomp L ≅ M.postcomp (K ⋙ L) :=
  Iso.refl _

/-- Functorial postcomposition on the Eilenberg–Moore category of right `T`-modules. -/
abbrev postcompFunctor (K : D ⥤ E) : RightModule T D ⥤ RightModule T E where
  obj M := M.postcomp K
  map {M N} f :=
    { f := Functor.whiskerRight f.f K
      h := by
        ext X
        have hX := congr_app f.h X
        simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          precompMonad] at hX ⊢
        rw [← K.map_comp, hX, K.map_comp]
    }
  map_id M := by
    ext X
    simp only [Functor.whiskerRight_app]
    exact K.map_id (M.A.obj X)
  map_comp {M₁ M₂ M₃} f g := by
    ext X
    simp only [Functor.whiskerRight_app, NatTrans.comp_app, Algebra.comp_f,
      Functor.map_comp]

@[simp]
lemma postcompFunctor_map_f (K : D ⥤ E) {M N : RightModule T D} (f : M ⟶ N) :
    ((postcompFunctor (T := T) K).map f).f = Functor.whiskerRight f.f K := rfl

/--
Identity coherence for outer target whiskering as a natural isomorphism. The right-module variable
is covariant and the left-module argument is held fixed/transported separately by `Iso.refl`.
Reuses the functor and the objectwise `postcompIdIso` (definitionally the unitor); no
pseudofunctor is built.
-/
def postcompId :
    (postcompFunctor (T := T) (D := D) (E := D) (𝟭 D) : RightModule T D ⥤ RightModule T D) ≅
    𝟭 (RightModule T D) :=
  NatIso.ofComponents (fun M => postcompIdIso M) (by
    intro M N f
    ext X
    simp only [postcompIdIso, Iso.refl_hom, Algebra.comp_f]
    change (Functor.whiskerRight f.f (𝟭 D)).app X ≫ 𝟙 _ = 𝟙 _ ≫ f.f.app X
    simp)

@[simp]
lemma postcompId_hom_f (M : RightModule T D) :
    ((postcompId (D := D) (T := T)).hom.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma postcompId_inv_f (M : RightModule T D) :
    ((postcompId (D := D) (T := T)).inv.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma postcompId_hom_f_app (M : RightModule T D) (X : C) :
    (((postcompId (D := D) (T := T)).hom.app M).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma postcompId_inv_f_app (M : RightModule T D) (X : C) :
    (((postcompId (D := D) (T := T)).inv.app M).f).app X = 𝟙 _ :=
  rfl

/--
Composition coherence for outer target whiskering as a natural isomorphism. Reuses the functors
and the objectwise `postcompCompIso` (definitionally the associator); only the coherence needed by
the bar consumer is packaged.
-/
def postcompComp (K : D ⥤ E) (L : E ⥤ F) :
    (postcompFunctor (T := T) (D := D) (E := E) K ⋙ postcompFunctor (T := T) (D := E) (E := F) L :
      RightModule T D ⥤ RightModule T F) ≅
      (postcompFunctor (T := T) (D := D) (E := F) (K ⋙ L) : RightModule T D ⥤ RightModule T F) :=
  NatIso.ofComponents (fun M => postcompCompIso M K L) (by
    intro M N f
    ext X
    simp only [postcompCompIso, Iso.refl_hom, Algebra.comp_f,
      Functor.comp_map]
    change (Functor.whiskerRight (Functor.whiskerRight f.f K) L).app X ≫ 𝟙 _ =
      𝟙 _ ≫ (Functor.whiskerRight f.f (K ⋙ L)).app X
    simp [Functor.whiskerRight_app])

@[simp]
lemma postcompComp_hom_f (M : RightModule T D) (K : D ⥤ E) (L : E ⥤ F) :
    (((postcompComp (T := T) K L).hom.app M)).f = 𝟙 _ :=
  rfl

@[simp]
lemma postcompComp_inv_f (M : RightModule T D) (K : D ⥤ E) (L : E ⥤ F) :
    (((postcompComp (T := T) K L).inv.app M)).f = 𝟙 _ :=
  rfl

@[simp]
lemma postcompComp_hom_f_app (M : RightModule T D) (K : D ⥤ E) (L : E ⥤ F) (X : C) :
    ((((postcompComp (T := T) K L).hom.app M)).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma postcompComp_inv_f_app (M : RightModule T D) (K : D ⥤ E) (L : E ⥤ F) (X : C) :
    ((((postcompComp (T := T) K L).inv.app M)).f).app X = 𝟙 _ :=
  rfl

/-! ## Restriction of scalars along a monad morphism (same carrier) -/

variable {S : Monad C}

/-- Restriction of right modules along `h : T ⟶ S`. -/
abbrev restrictAlongHom (h : T ⟶ S) : RightModule S D ⥤ RightModule T D :=
  Monad.algebraFunctorOfMonadHom (Monad.precompMonadHom (D := D) h)

@[simp]
lemma restrictAlongHom_obj_A (h : T ⟶ S) (M : RightModule S D) :
    ((restrictAlongHom h).obj M).A = M.A := rfl

@[simp]
lemma restrictAlongHom_obj_functor (h : T ⟶ S) (M : RightModule S D) :
    ((restrictAlongHom h).obj M).functor = M.functor := rfl

@[simp]
lemma restrictAlongHom_obj_functor_obj (h : T ⟶ S) (M : RightModule S D) (X : C) :
    ((restrictAlongHom h).obj M).functor.obj X = M.functor.obj X := rfl

@[simp]
lemma restrictAlongHom_obj_functor_map (h : T ⟶ S) (M : RightModule S D) {X Y : C}
    (f : X ⟶ Y) :
    ((restrictAlongHom h).obj M).functor.map f = M.functor.map f := rfl

@[simp]
lemma restrictAlongHom_obj_a (h : T ⟶ S) (M : RightModule S D) :
    ((restrictAlongHom h).obj M).a =
      (Monad.precompMonadHom (D := D) h).toNatTrans.app M.A ≫ M.a := rfl

@[simp]
lemma restrictAlongHom_obj_action (h : T ⟶ S) (M : RightModule S D) :
    ((restrictAlongHom h).obj M).action =
      (Monad.precompMonadHom (D := D) h).toNatTrans.app M.A ≫ M.action := rfl

@[simp]
lemma restrictAlongHom_obj_action_app (h : T ⟶ S) (M : RightModule S D) (X : C) :
    ((restrictAlongHom h).obj M).action.app X =
      M.functor.map (h.app X) ≫ M.action.app X := rfl

@[simp]
lemma restrictAlongHom_map_f {S : Monad C} (h : T ⟶ S) {M N : RightModule S D}
    (f : M ⟶ N) :
    ((restrictAlongHom (T := T) h).map f).f = f.f := rfl

/-! ### Identity action equalities -/

@[simp]
lemma restrictAlongHom_id_action_app (M : RightModule T D) (X : C) :
    ((restrictAlongHom (𝟙 T)).obj M).action.app X = M.action.app X := by
  simp [MonadHom.id_toNatTrans]

lemma restrictAlongHom_id_action (M : RightModule T D) :
    ((restrictAlongHom (𝟙 T)).obj M).action = M.action := by
  ext X
  simp

def restrictAlongHomIdIsoComponent (M : RightModule T D) :
    (restrictAlongHom (𝟙 T)).obj M ≅ M :=
  Algebra.isoMk (Iso.refl _)
    (by
      ext X
      simp)

@[simp]
lemma restrictAlongHomIdIsoComponent_hom_f (M : RightModule T D) :
    (restrictAlongHomIdIsoComponent M).hom.f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIsoComponent_inv_f (M : RightModule T D) :
    (restrictAlongHomIdIsoComponent M).inv.f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIsoComponent_hom_f_app (M : RightModule T D) (X : C) :
    ((restrictAlongHomIdIsoComponent M).hom.f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIsoComponent_inv_f_app (M : RightModule T D) (X : C) :
    ((restrictAlongHomIdIsoComponent M).inv.f).app X = 𝟙 _ :=
  rfl

def restrictAlongHomIdIso :
    (restrictAlongHom (D := D) (𝟙 T) : RightModule T D ⥤ RightModule T D) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => restrictAlongHomIdIsoComponent M) (by
    intro X Y f
    ext Z
    simp only [restrictAlongHom_map_f, restrictAlongHomIdIsoComponent_hom_f, Algebra.comp_f]
    change f.f.app Z ≫ 𝟙 _ = 𝟙 _ ≫ f.f.app Z
    simp)

@[simp]
lemma restrictAlongHomIdIso_hom_f (M : RightModule T D) :
    ((restrictAlongHomIdIso (D := D) (T := T)).hom.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIso_inv_f (M : RightModule T D) :
    ((restrictAlongHomIdIso (D := D) (T := T)).inv.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIso_hom_f_app (M : RightModule T D) (X : C) :
    (((restrictAlongHomIdIso (D := D) (T := T)).hom.app M).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIso_inv_f_app (M : RightModule T D) (X : C) :
    (((restrictAlongHomIdIso (D := D) (T := T)).inv.app M).f).app X = 𝟙 _ :=
  rfl

variable {U : Monad C}

/-! ### Composition action equalities -/

@[simp]
lemma restrictAlongHom_comp_action_app (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) (X : C) :
    ((restrictAlongHom (h ≫ k)).obj M).action.app X =
      M.functor.map (h.app X) ≫ M.functor.map (k.app X) ≫ M.action.app X := by
  simp

@[simp]
lemma restrictAlongHom_comp_iter_action_app (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U)
    (X : C) :
    ((restrictAlongHom h).obj ((restrictAlongHom k).obj M)).action.app X =
      M.functor.map (h.app X) ≫ M.functor.map (k.app X) ≫ M.action.app X := by
  simp

@[simp]
lemma restrictAlongHom_comp_action_app_eq (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U)
    (X : C) :
    ((restrictAlongHom (h ≫ k)).obj M).action.app X =
      ((restrictAlongHom h).obj ((restrictAlongHom k).obj M)).action.app X := by
  simp

lemma restrictAlongHom_comp_action (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) :
    ((restrictAlongHom (h ≫ k)).obj M).action =
      ((restrictAlongHom h).obj ((restrictAlongHom k).obj M)).action := by
  ext X
  simp

def restrictAlongHomCompIsoComponent (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) :
    (restrictAlongHom (h ≫ k)).obj M ≅
      (restrictAlongHom k ⋙ restrictAlongHom h).obj M :=
  Algebra.isoMk (Iso.refl _)
    (by
      ext X
      simp)

@[simp]
lemma restrictAlongHomCompIsoComponent_hom_f (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) :
    (restrictAlongHomCompIsoComponent M h k).hom.f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIsoComponent_inv_f (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) :
    (restrictAlongHomCompIsoComponent M h k).inv.f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIsoComponent_hom_f_app (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U)
    (X : C) :
    ((restrictAlongHomCompIsoComponent M h k).hom.f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIsoComponent_inv_f_app (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U)
    (X : C) :
    ((restrictAlongHomCompIsoComponent M h k).inv.f).app X = 𝟙 _ :=
  rfl

def restrictAlongHomCompIso (h : T ⟶ S) (k : S ⟶ U) :
    (restrictAlongHom (D := D) (h ≫ k) : RightModule U D ⥤ RightModule T D) ≅
      restrictAlongHom k ⋙ restrictAlongHom h :=
  NatIso.ofComponents (fun M => restrictAlongHomCompIsoComponent M h k) (by
    intro X Y f
    ext Z
    simp only [restrictAlongHom_map_f, restrictAlongHomCompIsoComponent_hom_f, Algebra.comp_f]
    change f.f.app Z ≫ 𝟙 _ = 𝟙 _ ≫ f.f.app Z
    simp)

@[simp]
lemma restrictAlongHomCompIso_hom_f (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) :
    ((restrictAlongHomCompIso (D := D) h k).hom.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIso_inv_f (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U) :
    ((restrictAlongHomCompIso (D := D) h k).inv.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIso_hom_f_app (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U)
    (X : C) :
    (((restrictAlongHomCompIso (D := D) h k).hom.app M).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIso_inv_f_app (M : RightModule U D) (h : T ⟶ S) (k : S ⟶ U)
    (X : C) :
    (((restrictAlongHomCompIso (D := D) h k).inv.app M).f).app X = 𝟙 _ :=
  rfl

end RightModule

namespace LeftModule

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₃} [Category.{v₃} A]
variable {T : Monad C}

abbrev functor (M : LeftModule A T) : A ⥤ C := M.A

abbrev action (M : LeftModule A T) : M.functor ⋙ T.toFunctor ⟶ M.functor := M.a

@[simp]
lemma functor_obj (M : LeftModule A T) (X : A) : M.functor.obj X = M.A.obj X := rfl

@[simp]
lemma action_app (M : LeftModule A T) (X : A) : M.action.app X = M.a.app X := rfl

lemma unit_app (M : LeftModule A T) (X : A) :
    T.η.app (M.functor.obj X) ≫ M.action.app X = 𝟙 (M.functor.obj X) := by
  have h := congr_app M.unit X
  exact h

lemma assoc_app (M : LeftModule A T) (X : A) :
    T.μ.app (M.functor.obj X) ≫ M.action.app X =
      T.map (M.action.app X) ≫ M.action.app X := by
  have h := congr_app M.assoc X
  exact h

abbrev mk (L : A ⥤ C) (act : L ⋙ T.toFunctor ⟶ L)
    (hunit : ∀ X, T.η.app (L.obj X) ≫ act.app X = 𝟙 (L.obj X))
    (hassoc : ∀ X, T.μ.app (L.obj X) ≫ act.app X = T.map (act.app X) ≫ act.app X) :
    LeftModule A T where
  A := L
  a := act
  unit := by ext X; exact hunit X
  assoc := by ext X; exact hassoc X

lemma hom_condition {M N : LeftModule A T} (f : M ⟶ N) :
    Functor.whiskerRight f.f T.toFunctor ≫ N.action = M.action ≫ f.f :=
  f.h

lemma hom_condition_app {M N : LeftModule A T} (f : M ⟶ N) (X : A) :
    T.map (f.f.app X) ≫ N.action.app X = M.action.app X ≫ f.f.app X := by
  have h := congr_app f.h X
  exact h

/--
Regular left `T`-module on `T` itself for `postcompMonad T`: underlying
  functor `T` with action `T ⋙ T ⟶ T` by multiplication `T.μ`.
-/
def regular (T : Monad C) : LeftModule C T where
  A := T.toFunctor
  a := T.μ
  unit := by ext X; exact T.left_unit X
  assoc := by ext X; exact (T.assoc X).symm

@[simp]
lemma regular_functor (T : Monad C) : (regular (T := T)).functor = T.toFunctor := rfl

@[simp]
lemma regular_action (T : Monad C) : (regular (T := T)).action = T.μ := rfl

/--
Free left module on `L : A ⥤ C`: underlying functor `L ⋙ T` with action
  `L`-whiskered `T.μ`; the free endpoint orientation for `B(R, T, _ ⋙ T)`.
-/
def freeObj (L : A ⥤ C) : LeftModule A T where
  A := L ⋙ T.toFunctor
  a := Functor.whiskerLeft L T.μ
  unit := by
    ext X
    exact T.left_unit (L.obj X)
  assoc := by
    ext X
    exact (T.assoc (L.obj X)).symm

@[simp]
lemma freeObj_functor (L : A ⥤ C) : (freeObj (T := T) L).functor = L ⋙ T.toFunctor := rfl

@[simp]
lemma freeObj_action (L : A ⥤ C) :
    (freeObj (T := T) L).action = Functor.whiskerLeft L T.μ := rfl

def freeFunctor : (A ⥤ C) ⥤ LeftModule A T :=
  (postcompMonad (A := A) T).free

@[simp]
lemma freeFunctor_obj_functor (L : A ⥤ C) :
    ((freeFunctor (A := A) (T := T)).obj L).functor = L ⋙ T.toFunctor :=
  rfl

@[simp]
lemma freeFunctor_obj_action (L : A ⥤ C) :
    ((freeFunctor (A := A) (T := T)).obj L).action = Functor.whiskerLeft L T.μ :=
  rfl

/-! ## Precomposition / whiskering in the outer indexing category -/

variable {B : Type u₄} [Category.{v₄} B]
variable {B₂ : Type u₅} [Category.{v₅} B₂]

/-- Precomposition of a left `T`-module `L : A ⥤ C` along `K : B ⥤ A`. -/
abbrev precomp (M : LeftModule A T) (K : B ⥤ A) : LeftModule B T :=
  LeftModule.mk (K ⋙ M.functor)
    { app := fun X => M.action.app (K.obj X)
      naturality := fun X Y f => by
        have h := M.action.naturality (K.map f)
        exact h
    }
    (fun X => by
      exact M.unit_app (K.obj X)
    )
    (fun X => by
      exact M.assoc_app (K.obj X)
    )

@[simp]
lemma precomp_functor (M : LeftModule A T) (K : B ⥤ A) :
    (M.precomp K).functor = K ⋙ M.functor := rfl

@[simp]
lemma precomp_functor_obj (M : LeftModule A T) (K : B ⥤ A) (X : B) :
    (M.precomp K).functor.obj X = M.functor.obj (K.obj X) := rfl

@[simp]
lemma precomp_functor_map (M : LeftModule A T) (K : B ⥤ A) {X Y : B} (f : X ⟶ Y) :
    (M.precomp K).functor.map f = M.functor.map (K.map f) := rfl

@[simp]
lemma precomp_action_app (M : LeftModule A T) (K : B ⥤ A) (X : B) :
    (M.precomp K).action.app X = M.action.app (K.obj X) := rfl

lemma precomp_action_eq_whiskerLeft (M : LeftModule A T) (K : B ⥤ A) :
    (M.precomp K).action = Functor.whiskerLeft K M.action := by
  ext X
  rfl

@[simp]
lemma precomp_regular_action_app (K : B ⥤ C) (X : B) :
    ((regular T).precomp K).action.app X = T.μ.app (K.obj X) := rfl

@[simp]
lemma precomp_freeObj_action_app (L : A ⥤ C) (K : B ⥤ A) (X : B) :
    ((freeObj (T := T) L).precomp K).action.app X = T.μ.app (L.obj (K.obj X)) := rfl

/-- Identity comparison: precomposition with `𝟭 A` is isomorphic to the module. -/
def precompIdIso (M : LeftModule A T) : M.precomp (𝟭 A) ≅ M :=
  Iso.refl _

/--
Composition comparison:
`(M ∘ K) ∘ H ≅ M ∘ (H ⋙ K)`.
-/
def precompCompIso (M : LeftModule A T) (K : B ⥤ A) (L : B₂ ⥤ B) :
    (M.precomp K).precomp L ≅ M.precomp (L ⋙ K) :=
  Iso.refl _

/-- Functorial precomposition on the Eilenberg–Moore category of left `T`-modules. -/
abbrev precompFunctor (K : B ⥤ A) : LeftModule A T ⥤ LeftModule B T where
  obj M := M.precomp K
  map {M N} f :=
    { f := Functor.whiskerLeft K f.f
      h := by
        ext X
        have hX := congr_app f.h (K.obj X)
        exact hX
    }
  map_id M := by
    ext X
    rfl
  map_comp {M₁ M₂ M₃} f g := by
    ext X
    rfl

@[simp]
lemma precompFunctor_map_f (K : B ⥤ A) {M N : LeftModule A T} (f : M ⟶ N) :
    ((precompFunctor (T := T) K).map f).f = Functor.whiskerLeft K f.f := rfl

/--
Identity coherence for outer source whiskering as a natural isomorphism. Source precomposition is
contravariant in its outer category. Reuses the functor and the objectwise `precompIdIso`
(definitionally the unitor).
-/
def precompId :
    (precompFunctor (T := T) (A := A) (B := A) (𝟭 A) : LeftModule A T ⥤ LeftModule A T) ≅
    𝟭 (LeftModule A T) :=
  NatIso.ofComponents (fun M => precompIdIso M) (by
    intro M N f
    ext X
    simp only [precompIdIso, Iso.refl_hom, Algebra.comp_f]
    change (Functor.whiskerLeft (𝟭 A) f.f).app X ≫ 𝟙 _ = 𝟙 _ ≫ f.f.app X
    simp)

@[simp]
lemma precompId_hom_f (M : LeftModule A T) :
    ((precompId (A := A) (T := T)).hom.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma precompId_inv_f (M : LeftModule A T) :
    ((precompId (A := A) (T := T)).inv.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma precompId_hom_f_app (M : LeftModule A T) (X : A) :
    (((precompId (A := A) (T := T)).hom.app M).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma precompId_inv_f_app (M : LeftModule A T) (X : A) :
    (((precompId (A := A) (T := T)).inv.app M).f).app X = 𝟙 _ :=
  rfl

/--
Composition coherence for outer source whiskering as a natural isomorphism. For `K : B ⥤ A` and `L
: B₂ ⥤ B`, this is `precomp K ⋙ precomp L ≅ precomp (L ⋙ K)`. Reuses the functors and the
objectwise `precompCompIso` (definitionally the associator pair); only the coherence needed by the
bar consumer is packaged.
-/
def precompComp (K : B ⥤ A) (L : B₂ ⥤ B) :
    (precompFunctor (T := T) (A := A) (B := B) K ⋙ precompFunctor (T := T) (A := B) (B := B₂) L :
      LeftModule A T ⥤ LeftModule B₂ T) ≅
      (precompFunctor (T := T) (A := A) (B := B₂) (L ⋙ K) : LeftModule A T ⥤ LeftModule B₂ T) :=
  NatIso.ofComponents (fun M => precompCompIso M K L) (by
    intro M N f
    ext X
    simp only [precompCompIso, Iso.refl_hom, Algebra.comp_f,
      Functor.comp_map]
    change (Functor.whiskerLeft L (Functor.whiskerLeft K f.f)).app X ≫ 𝟙 _ =
      𝟙 _ ≫ (Functor.whiskerLeft (L ⋙ K) f.f).app X
    simp [Functor.whiskerLeft_app])

@[simp]
lemma precompComp_hom_f (M : LeftModule A T) (K : B ⥤ A) (L : B₂ ⥤ B) :
    (((precompComp (T := T) K L).hom.app M)).f = 𝟙 _ :=
  rfl

@[simp]
lemma precompComp_inv_f (M : LeftModule A T) (K : B ⥤ A) (L : B₂ ⥤ B) :
    (((precompComp (T := T) K L).inv.app M)).f = 𝟙 _ :=
  rfl

@[simp]
lemma precompComp_hom_f_app (M : LeftModule A T) (K : B ⥤ A) (L : B₂ ⥤ B) (X : B₂) :
    ((((precompComp (T := T) K L).hom.app M)).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma precompComp_inv_f_app (M : LeftModule A T) (K : B ⥤ A) (L : B₂ ⥤ B) (X : B₂) :
    ((((precompComp (T := T) K L).inv.app M)).f).app X = 𝟙 _ :=
  rfl

/-! ## Restriction of scalars along a monad morphism (same carrier) -/

variable {S : Monad C}

/-- Restriction of left modules along `h : T ⟶ S`. -/
abbrev restrictAlongHom (h : T ⟶ S) : LeftModule A S ⥤ LeftModule A T :=
  Monad.algebraFunctorOfMonadHom (Monad.postcompMonadHom (A := A) h)

@[simp]
lemma restrictAlongHom_obj_A (h : T ⟶ S) (M : LeftModule A S) :
    ((restrictAlongHom h).obj M).A = M.A := rfl

@[simp]
lemma restrictAlongHom_obj_functor (h : T ⟶ S) (M : LeftModule A S) :
    ((restrictAlongHom h).obj M).functor = M.functor := rfl

@[simp]
lemma restrictAlongHom_obj_functor_obj (h : T ⟶ S) (M : LeftModule A S) (X : A) :
    ((restrictAlongHom h).obj M).functor.obj X = M.functor.obj X := rfl

@[simp]
lemma restrictAlongHom_obj_functor_map (h : T ⟶ S) (M : LeftModule A S) {X Y : A}
    (f : X ⟶ Y) :
    ((restrictAlongHom h).obj M).functor.map f = M.functor.map f := rfl

@[simp]
lemma restrictAlongHom_obj_a (h : T ⟶ S) (M : LeftModule A S) :
    ((restrictAlongHom h).obj M).a =
      (Monad.postcompMonadHom (A := A) h).toNatTrans.app M.A ≫ M.a := rfl

@[simp]
lemma restrictAlongHom_obj_action (h : T ⟶ S) (M : LeftModule A S) :
    ((restrictAlongHom h).obj M).action =
      (Monad.postcompMonadHom (A := A) h).toNatTrans.app M.A ≫ M.action := rfl

@[simp]
lemma restrictAlongHom_obj_action_app (h : T ⟶ S) (M : LeftModule A S) (X : A) :
    ((restrictAlongHom h).obj M).action.app X =
      h.app (M.functor.obj X) ≫ M.action.app X := rfl

@[simp]
lemma restrictAlongHom_map_f {S : Monad C} (h : T ⟶ S) {M N : LeftModule A S}
    (f : M ⟶ N) :
    ((restrictAlongHom (T := T) h).map f).f = f.f := rfl

/-! ### Identity action equalities -/

@[simp]
lemma restrictAlongHom_id_action_app (M : LeftModule A T) (X : A) :
    ((restrictAlongHom (𝟙 T)).obj M).action.app X = M.action.app X := by
  simp [MonadHom.id_toNatTrans]

lemma restrictAlongHom_id_action (M : LeftModule A T) :
    ((restrictAlongHom (𝟙 T)).obj M).action = M.action := by
  ext X
  simp

def restrictAlongHomIdIsoComponent (M : LeftModule A T) :
    (restrictAlongHom (𝟙 T)).obj M ≅ M :=
  Algebra.isoMk (Iso.refl _)
    (by
      ext X
      simp)

def restrictAlongHomIdIso :
    (restrictAlongHom (A := A) (𝟙 T) : LeftModule A T ⥤ LeftModule A T) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => restrictAlongHomIdIsoComponent M) (by
    intro X Y f
    ext Z
    have hY : (Y.restrictAlongHomIdIsoComponent).hom.f = 𝟙 _ := rfl
    have hX : (X.restrictAlongHomIdIsoComponent).hom.f = 𝟙 _ := rfl
    simp only [hY, hX, restrictAlongHom_map_f, Algebra.comp_f]
    change f.f.app Z ≫ 𝟙 _ = 𝟙 _ ≫ f.f.app Z
    simp)

@[simp]
lemma restrictAlongHomIdIso_hom_f (M : LeftModule A T) :
    ((restrictAlongHomIdIso (A := A) (T := T)).hom.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIso_inv_f (M : LeftModule A T) :
    ((restrictAlongHomIdIso (A := A) (T := T)).inv.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIso_hom_f_app (M : LeftModule A T) (X : A) :
    (((restrictAlongHomIdIso (A := A) (T := T)).hom.app M).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomIdIso_inv_f_app (M : LeftModule A T) (X : A) :
    (((restrictAlongHomIdIso (A := A) (T := T)).inv.app M).f).app X = 𝟙 _ :=
  rfl

variable {U : Monad C}

@[simp]
lemma restrictAlongHom_comp_action_app (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U) (X : A) :
    ((restrictAlongHom (h ≫ k)).obj M).action.app X =
      h.app (M.functor.obj X) ≫ k.app (M.functor.obj X) ≫ M.action.app X := by
  simp

@[simp]
lemma restrictAlongHom_comp_iter_action_app (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U)
    (X : A) :
    ((restrictAlongHom h).obj ((restrictAlongHom k).obj M)).action.app X =
      h.app (M.functor.obj X) ≫ k.app (M.functor.obj X) ≫ M.action.app X := by
  simp

@[simp]
lemma restrictAlongHom_comp_action_app_eq (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U)
    (X : A) :
    ((restrictAlongHom (h ≫ k)).obj M).action.app X =
      ((restrictAlongHom h).obj ((restrictAlongHom k).obj M)).action.app X := by
  simp

lemma restrictAlongHom_comp_action (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U) :
    ((restrictAlongHom (h ≫ k)).obj M).action =
      ((restrictAlongHom h).obj ((restrictAlongHom k).obj M)).action := by
  ext X
  simp

def restrictAlongHomCompIsoComponent (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U) :
    (restrictAlongHom (h ≫ k)).obj M ≅
      (restrictAlongHom k ⋙ restrictAlongHom h).obj M :=
  Algebra.isoMk (Iso.refl _)
    (by
      ext X
      simp)

def restrictAlongHomCompIso (h : T ⟶ S) (k : S ⟶ U) :
    (restrictAlongHom (A := A) (h ≫ k) : LeftModule A U ⥤ LeftModule A T) ≅
      restrictAlongHom k ⋙ restrictAlongHom h :=
  NatIso.ofComponents (fun M => restrictAlongHomCompIsoComponent M h k) (by
    intro X Y f
    ext Z
    have hY : (Y.restrictAlongHomCompIsoComponent h k).hom.f = 𝟙 _ := rfl
    have hX : (X.restrictAlongHomCompIsoComponent h k).hom.f = 𝟙 _ := rfl
    simp only [hY, hX, restrictAlongHom_map_f, Algebra.comp_f]
    change f.f.app Z ≫ 𝟙 _ = 𝟙 _ ≫ f.f.app Z
    simp)

@[simp]
lemma restrictAlongHomCompIso_hom_f (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U) :
    ((restrictAlongHomCompIso (A := A) h k).hom.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIso_inv_f (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U) :
    ((restrictAlongHomCompIso (A := A) h k).inv.app M).f = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIso_hom_f_app (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U)
    (X : A) :
    (((restrictAlongHomCompIso (A := A) h k).hom.app M).f).app X = 𝟙 _ :=
  rfl

@[simp]
lemma restrictAlongHomCompIso_inv_f_app (M : LeftModule A U) (h : T ⟶ S) (k : S ⟶ U)
    (X : A) :
    (((restrictAlongHomCompIso (A := A) h k).inv.app M).f).app X = 𝟙 _ :=
  rfl

end LeftModule

/-- Generic restriction of right modules along `h : T ⟶ S` (same carrier). -/
abbrev rightModuleRestrictAlongHom {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {T S : Monad C} (h : T ⟶ S) :
    RightModule S D ⥤ RightModule T D :=
  algebraFunctorOfMonadHom (precompMonadHom (D := D) h)

/-- Generic restriction of left modules along `h : T ⟶ S` (same carrier). -/
abbrev leftModuleRestrictAlongHom {C : Type u₁} [Category.{v₁} C] {A : Type u₃}
    [Category.{v₃} A] {T S : Monad C} (h : T ⟶ S) :
    LeftModule A S ⥤ LeftModule A T :=
  algebraFunctorOfMonadHom (postcompMonadHom (A := A) h)

@[simp]
lemma rightModuleRestrictAlongHom_obj_functor {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {T S : Monad C} (h : T ⟶ S)
    (M : RightModule S D) :
    (rightModuleRestrictAlongHom (D := D) h |>.obj M).functor = M.functor := rfl

@[simp]
lemma rightModuleRestrictAlongHom_obj_action_app {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {T S : Monad C} (h : T ⟶ S)
    (M : RightModule S D) (X : C) :
    (rightModuleRestrictAlongHom (D := D) h |>.obj M).action.app X =
      M.functor.map (h.app X) ≫ M.action.app X := rfl

@[simp]
lemma leftModuleRestrictAlongHom_obj_functor {C : Type u₁} [Category.{v₁} C]
    {A : Type u₃} [Category.{v₃} A] {T S : Monad C} (h : T ⟶ S)
    (M : LeftModule A S) :
    (leftModuleRestrictAlongHom (A := A) h |>.obj M).functor = M.functor := rfl

@[simp]
lemma leftModuleRestrictAlongHom_obj_action_app {C : Type u₁} [Category.{v₁} C]
    {A : Type u₃} [Category.{v₃} A] {T S : Monad C} (h : T ⟶ S)
    (M : LeftModule A S) (X : A) :
    (leftModuleRestrictAlongHom (A := A) h |>.obj M).action.app X =
      h.app (M.functor.obj X) ≫ M.action.app X := rfl

end Monad

end CategoryTheory
