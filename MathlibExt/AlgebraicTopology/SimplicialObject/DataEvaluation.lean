/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial

/-!
# Evaluation of functor-valued simplicial data

Objectwise evaluation of `Data (A ⥤ D)` at an indexing object `a : A`,
functorial in `a` through degreewise whiskering and in `Data` morphisms
through componentwise evaluation. The two directions are organized as the
currying functor into `A ⥤ Data D` and the uncurrying functor back.
-/

@[expose] public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.SimplicialObject.Data

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]

/-- Objectwise evaluation of `Data (A ⥤ D)` at `a : A` into `Data D`. -/
def evalObj (a : A) (X : Data (A ⥤ D)) : Data D where
  obj n := (X.obj n).obj a
  δ i := (X.δ i).app a
  σ i := (X.σ i).app a
  δ_comp_δ h := by
    exact congrArg (fun f => f.app a) (X.δ_comp_δ h)
  δ_comp_σ_of_le h := by
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_of_le h)
  δ_comp_σ_self := by
    intro n i
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_self (i := i))
  δ_comp_σ_succ := by
    intro n i
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_succ (i := i))
  δ_comp_σ_of_gt h := by
    exact congrArg (fun f => f.app a) (X.δ_comp_σ_of_gt h)
  σ_comp_σ h := by
    exact congrArg (fun f => f.app a) (X.σ_comp_σ h)

@[simp]
theorem evalObj_obj (a : A) (X : Data (A ⥤ D)) (n : ℕ) :
    (evalObj a X).obj n = (X.obj n).obj a :=
  rfl

@[simp]
theorem evalObj_δ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 2)) :
    (evalObj a X).δ i = (X.δ i).app a :=
  rfl

@[simp]
theorem evalObj_σ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 1)) :
    (evalObj a X).σ i = (X.σ i).app a :=
  rfl

/-- Evaluation of a morphism at `a`. -/
def evalHom (a : A) {X Y : Data (A ⥤ D)} (f : X ⟶ Y) :
    evalObj a X ⟶ evalObj a Y where
  app n := (f.app n).app a
  w_δ := by
    intro n i
    exact congrArg (fun g => g.app a) (f.w_δ i)
  w_σ := by
    intro n i
    exact congrArg (fun g => g.app a) (f.w_σ i)

@[simp]
theorem evalHom_app (a : A) {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (n : ℕ) :
    (evalHom a f).app n = (f.app n).app a :=
  rfl

theorem evalHom_id (a : A) (X : Data (A ⥤ D)) :
    evalHom a (𝟙 X) = 𝟙 (evalObj a X) := by
  apply Hom.ext
  intro n
  rfl

theorem evalHom_comp {X Y Z : Data (A ⥤ D)} (a : A) (f : X ⟶ Y) (g : Y ⟶ Z) :
    evalHom a (f ≫ g) = evalHom a f ≫ evalHom a g := by
  apply Hom.ext
  intro n
  rfl

/-- Evaluation functor at `a`. -/
def evalFunctor (a : A) : Data (A ⥤ D) ⥤ Data D where
  obj X := evalObj a X
  map f := evalHom a f
  map_id X := evalHom_id a X
  map_comp f g := evalHom_comp a f g

@[simp]
theorem evalFunctor_obj_obj (a : A) (X : Data (A ⥤ D)) (n : ℕ) :
    ((evalFunctor a).obj X).obj n = (X.obj n).obj a :=
  rfl

@[simp]
theorem evalFunctor_obj_δ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 2)) :
    ((evalFunctor a).obj X).δ i = (X.δ i).app a :=
  rfl

@[simp]
theorem evalFunctor_obj_σ (a : A) (X : Data (A ⥤ D)) {n : ℕ} (i : Fin (n + 1)) :
    ((evalFunctor a).obj X).σ i = (X.σ i).app a :=
  rfl

@[simp]
theorem evalFunctor_map_app (a : A) {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (n : ℕ) :
    ((evalFunctor a).map f).app n = (f.app n).app a :=
  rfl

/-- Degreewise whiskering of `X.obj` on a morphism `f : a ⟶ b`. -/
def evalObjMap (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) :
    evalObj a X ⟶ evalObj b X where
  app n := (X.obj n).map f
  w_δ := by
    intro n i
    exact (X.δ i).naturality f
  w_σ := by
    intro n i
    exact (X.σ i).naturality f

@[simp]
theorem evalObjMap_app (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (evalObjMap X f).app n = (X.obj n).map f :=
  rfl

theorem evalObjMap_id (X : Data (A ⥤ D)) (a : A) :
    evalObjMap X (𝟙 a) = 𝟙 (evalObj a X) := by
  apply Hom.ext
  intro n
  simp

theorem evalObjMap_comp (X : Data (A ⥤ D)) {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    evalObjMap X (f ≫ g) = evalObjMap X f ≫ evalObjMap X g := by
  apply Hom.ext
  intro n
  simp

/-- Curried object `A ⥤ Data D` attached to `X`. -/
def curryObj (X : Data (A ⥤ D)) : A ⥤ Data D where
  obj a := evalObj a X
  map f := evalObjMap X f
  map_id a := by
    apply Hom.ext
    intro n
    simp
  map_comp f g := by
    apply Hom.ext
    intro n
    simp

@[simp]
theorem curryObj_obj (X : Data (A ⥤ D)) (a : A) :
    (curryObj X).obj a = evalObj a X :=
  rfl

@[simp]
theorem curryObj_map_app (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) (n : ℕ) :
    ((curryObj X).map f).app n = (X.obj n).map f :=
  rfl

/-- Curried map as natural transformation. -/
def curryMap {X Y : Data (A ⥤ D)} (f : X ⟶ Y) : curryObj X ⟶ curryObj Y where
  app a :=
    { app n := (f.app n).app a
      w_δ := by
        intro n i
        exact congrArg (fun g => g.app a) (f.w_δ i)
      w_σ := by
        intro n i
        exact congrArg (fun g => g.app a) (f.w_σ i) }
  naturality a b g := by
    apply Hom.ext
    intro n
    exact (f.app n).naturality g

@[simp]
theorem curryMap_app_app {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (a : A) (n : ℕ) :
    ((curryMap f).app a).app n = (f.app n).app a :=
  rfl

/-- Currying functor `Data (A ⥤ D) ⥤ (A ⥤ Data D)`. -/
def curryFunctor : Data (A ⥤ D) ⥤ (A ⥤ Data D) where
  obj X := curryObj X
  map f := curryMap f
  map_id X := by
    ext a
    apply Hom.ext
    intro n
    rfl
  map_comp := by
    intro X Y Z f g
    ext a
    apply Hom.ext
    intro n
    rfl

@[simp]
theorem curryFunctor_obj_obj (X : Data (A ⥤ D)) (a : A) :
    ((curryFunctor (A := A) (D := D)).obj X).obj a = evalObj a X :=
  rfl

@[simp]
theorem curryFunctor_obj_map_app (X : Data (A ⥤ D)) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (((curryFunctor (A := A) (D := D)).obj X).map f).app n = (X.obj n).map f :=
  rfl

@[simp]
theorem curryFunctor_map_app_app {X Y : Data (A ⥤ D)} (f : X ⟶ Y) (a : A) (n : ℕ) :
    (((curryFunctor (A := A) (D := D)).map f).app a).app n = (f.app n).app a := by
  rfl

/-- The functor `a ↦ (X.obj a).obj n` for `X : A ⥤ Data D`. -/
def uncurryObjObj (X : A ⥤ Data D) (n : ℕ) : A ⥤ D where
  obj a := (X.obj a).obj n
  map f := (X.map f).app n
  map_id a := by
    have h := X.map_id a
    have h_app : (X.map (𝟙 a)).app n = (𝟙 (X.obj a) : Data.Hom _ _).app n := by
      rw [h]
    calc
      (X.map (𝟙 a)).app n = (𝟙 (X.obj a) : Data.Hom _ _).app n := h_app
      _ = 𝟙 _ := rfl
  map_comp f g := by
    have h := X.map_comp f g
    calc
      (X.map (f ≫ g)).app n = (X.map f ≫ X.map g).app n := by rw [h]
      _ = (X.map f).app n ≫ (X.map g).app n := rfl

@[simp]
theorem uncurryObjObj_obj (X : A ⥤ Data D) (n : ℕ) (a : A) :
    (uncurryObjObj X n).obj a = (X.obj a).obj n :=
  rfl

@[simp]
theorem uncurryObjObj_map (X : A ⥤ Data D) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (uncurryObjObj X n).map f = (X.map f).app n :=
  rfl

/-- Face as a natural transformation `(X.obj _).obj (n+1) ⟶ (X.obj _).obj n`. -/
def uncurryObjδ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) :
    uncurryObjObj X (n + 1) ⟶ uncurryObjObj X n where
  app a := (X.obj a).δ i
  naturality _ _ f := (X.map f).w_δ i

@[simp]
theorem uncurryObjδ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    (uncurryObjδ X i).app a = (X.obj a).δ i :=
  rfl

/-- Degeneracy as a natural transformation. -/
def uncurryObjσ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) :
    uncurryObjObj X n ⟶ uncurryObjObj X (n + 1) where
  app a := (X.obj a).σ i
  naturality _ _ f := (X.map f).w_σ i

@[simp]
theorem uncurryObjσ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    (uncurryObjσ X i).app a = (X.obj a).σ i :=
  rfl

/-- Uncurried object: `Data (A ⥤ D)` assembled from `X : A ⥤ Data D`. -/
def uncurryObj (X : A ⥤ Data D) : Data (A ⥤ D) where
  obj n := uncurryObjObj X n
  δ i := uncurryObjδ X i
  σ i := uncurryObjσ X i
  δ_comp_δ := by
    intro n i j h
    ext a
    exact (X.obj a).δ_comp_δ h
  δ_comp_σ_of_le := by
    intro n i j h
    ext a
    exact (X.obj a).δ_comp_σ_of_le h
  δ_comp_σ_self := by
    intro n i
    ext a
    exact (X.obj a).δ_comp_σ_self
  δ_comp_σ_succ := by
    intro n i
    ext a
    exact (X.obj a).δ_comp_σ_succ
  δ_comp_σ_of_gt := by
    intro n i j h
    ext a
    exact (X.obj a).δ_comp_σ_of_gt h
  σ_comp_σ := by
    intro n i j h
    ext a
    exact (X.obj a).σ_comp_σ h

@[simp]
theorem uncurryObj_obj (X : A ⥤ Data D) (n : ℕ) :
    (uncurryObj X).obj n = uncurryObjObj X n :=
  rfl

@[simp]
theorem uncurryObj_obj_obj (X : A ⥤ Data D) (n : ℕ) (a : A) :
    ((uncurryObj X).obj n).obj a = (X.obj a).obj n :=
  rfl

@[simp]
theorem uncurryObj_obj_map (X : A ⥤ Data D) {a b : A} (f : a ⟶ b) (n : ℕ) :
    ((uncurryObj X).obj n).map f = (X.map f).app n :=
  rfl

@[simp]
theorem uncurryObj_δ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) :
    (uncurryObj X).δ i = uncurryObjδ X i :=
  rfl

@[simp]
theorem uncurryObj_δ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    ((uncurryObj X).δ i).app a = (X.obj a).δ i :=
  rfl

@[simp]
theorem uncurryObj_σ (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) :
    (uncurryObj X).σ i = uncurryObjσ X i :=
  rfl

@[simp]
theorem uncurryObj_σ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    ((uncurryObj X).σ i).app a = (X.obj a).σ i :=
  rfl

/-- Componentwise natural transformation for `uncurry`. -/
def uncurryMapApp (X Y : A ⥤ Data D) (α : X ⟶ Y) (n : ℕ) :
    uncurryObjObj X n ⟶ uncurryObjObj Y n where
  app a := (α.app a).app n
  naturality a b f := by
    have h := α.naturality f
    calc
      (X.map f).app n ≫ (α.app b).app n
          = (X.map f ≫ α.app b).app n := rfl
      _ = (α.app a ≫ Y.map f).app n := by rw [h]
      _ = (α.app a).app n ≫ (Y.map f).app n := rfl

@[simp]
theorem uncurryMapApp_app (X Y : A ⥤ Data D) (α : X ⟶ Y) (n : ℕ) (a : A) :
    (uncurryMapApp X Y α n).app a = (α.app a).app n :=
  rfl

/-- Morphism part of uncurrying. -/
def uncurryMap {X Y : A ⥤ Data D} (α : X ⟶ Y) :
    uncurryObj X ⟶ uncurryObj Y where
  app n := uncurryMapApp X Y α n
  w_δ := by
    intro n i
    ext a
    exact (α.app a).w_δ i
  w_σ := by
    intro n i
    ext a
    exact (α.app a).w_σ i

@[simp]
theorem uncurryMap_app (X Y : A ⥤ Data D) (α : X ⟶ Y) (n : ℕ) :
    (uncurryMap α).app n = uncurryMapApp X Y α n :=
  rfl

@[simp]
theorem uncurryMap_app_app {X Y : A ⥤ Data D} (α : X ⟶ Y) (n : ℕ) (a : A) :
    ((uncurryMap α).app n).app a = (α.app a).app n :=
  rfl

theorem uncurryMap_id (X : A ⥤ Data D) :
    uncurryMap (𝟙 X) = 𝟙 (uncurryObj X) := by
  apply Hom.ext
  intro n
  ext a
  rfl

theorem uncurryMap_comp {X Y Z : A ⥤ Data D} (α : X ⟶ Y) (β : Y ⟶ Z) :
    uncurryMap (α ≫ β) = uncurryMap α ≫ uncurryMap β := by
  apply Hom.ext
  intro n
  ext a
  rfl

/-- Uncurrying functor `(A ⥤ Data D) ⥤ Data (A ⥤ D)`. -/
def uncurryFunctor : (A ⥤ Data D) ⥤ Data (A ⥤ D) where
  obj X := uncurryObj X
  map α := uncurryMap α
  map_id X := uncurryMap_id X
  map_comp α β := uncurryMap_comp α β

@[simp]
theorem uncurryFunctor_obj_obj (X : A ⥤ Data D) (n : ℕ) :
    ((uncurryFunctor (A := A) (D := D)).obj X).obj n = uncurryObjObj X n :=
  rfl

@[simp]
theorem uncurryFunctor_obj_obj_obj (X : A ⥤ Data D) (n : ℕ) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).obj X).obj n).obj a = (X.obj a).obj n :=
  rfl

@[simp]
theorem uncurryFunctor_obj_obj_map (X : A ⥤ Data D) {a b : A} (f : a ⟶ b) (n : ℕ) :
    (((uncurryFunctor (A := A) (D := D)).obj X).obj n).map f = (X.map f).app n :=
  rfl

@[simp]
theorem uncurryFunctor_obj_δ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 2)) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).obj X).δ i).app a = (X.obj a).δ i :=
  rfl

@[simp]
theorem uncurryFunctor_obj_σ_app (X : A ⥤ Data D) {n : ℕ} (i : Fin (n + 1)) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).obj X).σ i).app a = (X.obj a).σ i :=
  rfl

@[simp]
theorem uncurryFunctor_map_app_app {X Y : A ⥤ Data D} (α : X ⟶ Y) (n : ℕ) (a : A) :
    (((uncurryFunctor (A := A) (D := D)).map α).app n).app a = (α.app a).app n :=
  rfl

/-- Evaluation commutes with promotion on arbitrary morphisms: for any
`f : m ⟶ n` in `SimplexCategory`, the two routes agree.

Specialization of the generic `toSimplicialObject_mapObj_map` to the
evaluation functor; `mapObj ((evaluation A D).obj a) X` is definitionally
`(evalFunctor a).obj X`. -/
theorem evalToSimplicial_map_eq (X : Data (A ⥤ D)) (a : A)
    {m n : SimplexCategory} (f : m ⟶ n) :
    (X.toSimplicialObject ⋙ (evaluation A D).obj a).map f.op =
      (((evalFunctor a).obj X).toSimplicialObject).map f.op :=
  (toSimplicialObject_mapObj_map ((evaluation A D).obj a) X (f := f.op)).symm

/-- Identity-component comparison between evaluation after promotion and
promotion after evaluation.

Evaluation component of the generic `toSimplicialFunctor_mapFunctorIso`;
orientation `(X.toSimplicialObject ⋙ (evaluation A D).obj a) ≅
(((evalFunctor a).obj X).toSimplicialObject)` is preserved. -/
noncomputable def evalToSimplicialIso (X : Data (A ⥤ D)) (a : A) :
    (X.toSimplicialObject ⋙ (evaluation A D).obj a) ≅
      (((evalFunctor a).obj X).toSimplicialObject) :=
  (toSimplicialFunctor_mapFunctorIso ((evaluation A D).obj a)).app X

/-- Hom component of `evalToSimplicialIso` at an arbitrary simplex. -/
@[simp]
theorem evalToSimplicialIso_hom_app (X : Data (A ⥤ D)) (a : A)
    (Δ : SimplexCategoryᵒᵖ) :
    (evalToSimplicialIso X a).hom.app Δ = 𝟙 _ :=
  rfl

/-- Inverse component of `evalToSimplicialIso` at an arbitrary simplex. -/
@[simp]
theorem evalToSimplicialIso_inv_app (X : Data (A ⥤ D)) (a : A)
    (Δ : SimplexCategoryᵒᵖ) :
    (evalToSimplicialIso X a).inv.app Δ = 𝟙 _ :=
  rfl

end CategoryTheory.SimplicialObject.Data

end
