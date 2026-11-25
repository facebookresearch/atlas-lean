/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Simplicial data to simplicial objects

Converts simplicial `Data` to genuine simplicial objects via the generators-and-relations
simplex category `SimplexCategoryGenRel`.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory

namespace SimplicialObject

structure Data (C : Type u) [Category.{v} C] where
  obj : ℕ → C
  δ : ∀ {n : ℕ}, Fin (n + 2) → (obj (n + 1) ⟶ obj n)
  σ : ∀ {n : ℕ}, Fin (n + 1) → (obj n ⟶ obj (n + 1))
  δ_comp_δ :
    ∀ {n : ℕ} {i j : Fin (n + 2)} (_h : i ≤ j),
      δ j.succ ≫ δ i = δ i.castSucc ≫ δ j
  δ_comp_σ_of_le :
    ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (_h : i ≤ j.castSucc),
      σ j.succ ≫ δ i.castSucc = δ i ≫ σ j
  δ_comp_σ_self : ∀ {n : ℕ} {i : Fin (n + 1)}, σ i ≫ δ i.castSucc = 𝟙 (obj n)
  δ_comp_σ_succ : ∀ {n : ℕ} {i : Fin (n + 1)}, σ i ≫ δ i.succ = 𝟙 (obj n)
  δ_comp_σ_of_gt :
    ∀ {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (_h : j.castSucc < i),
      σ j.castSucc ≫ δ i.succ = δ i ≫ σ j
  σ_comp_σ :
    ∀ {n : ℕ} {i j : Fin (n + 1)} (_h : i ≤ j),
      σ j ≫ σ i.castSucc = σ i ≫ σ j.succ

namespace Data

variable {C : Type u} [Category.{v} C]

def preFunctorOp (data : Data (C := C)) : FreeSimplexQuiver ⥤q Cᵒᵖ where
  obj n := op (data.obj n)
  map f :=
    match f with
    | .δ (n := n) i => (data.δ (n := n) i).op
    | .σ (n := n) i => (data.σ (n := n) i).op

@[simp]
theorem preFunctorOp_obj (data : Data (C := C)) (n : ℕ) :
    data.preFunctorOp.obj n = op (data.obj n) :=
  rfl

theorem preFunctorOp_map_δ (data : Data (C := C)) {n : ℕ} (i : Fin (n + 2)) :
    data.preFunctorOp.map (FreeSimplexQuiver.δ (n := n) i) = (data.δ i).op :=
  rfl

theorem preFunctorOp_map_σ (data : Data (C := C)) {n : ℕ} (i : Fin (n + 1)) :
    data.preFunctorOp.map (FreeSimplexQuiver.σ (n := n) i) = (data.σ i).op :=
  rfl

def pathsFunctorOp (data : Data (C := C)) : Paths FreeSimplexQuiver ⥤ Cᵒᵖ :=
  Paths.lift data.preFunctorOp

theorem pathsFunctorOp_map_of_δ (data : Data (C := C)) {n : ℕ} (i : Fin (n + 2)) :
    data.pathsFunctorOp.map ((Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.δ (n := n) i)) =
      (data.δ i).op := by
  have h : (Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.δ (n := n) i) =
      Quiver.Hom.toPath (FreeSimplexQuiver.δ (n := n) i) := rfl
  rw [h]
  exact Paths.lift_toPath (φ := data.preFunctorOp) (f := FreeSimplexQuiver.δ i)

theorem pathsFunctorOp_map_of_σ (data : Data (C := C)) {n : ℕ} (i : Fin (n + 1)) :
    data.pathsFunctorOp.map ((Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.σ (n := n) i)) =
      (data.σ i).op := by
  have h : (Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.σ (n := n) i) =
      Quiver.Hom.toPath (FreeSimplexQuiver.σ (n := n) i) := rfl
  rw [h]
  exact Paths.lift_toPath (φ := data.preFunctorOp) (f := FreeSimplexQuiver.σ i)

theorem respectsHomRel (data : Data (C := C)) {x y : Paths FreeSimplexQuiver}
    {f g : x ⟶ y} (h : FreeSimplexQuiver.homRel f g) :
    data.pathsFunctorOp.map f = data.pathsFunctorOp.map g := by
  cases h with
  | @δ_comp_δ n i j H =>
    simp only [Functor.map_comp, pathsFunctorOp_map_of_δ]
    change (data.δ j.succ ≫ data.δ i).op = (data.δ i.castSucc ≫ data.δ j).op
    rw [data.δ_comp_δ H]
  | @δ_comp_σ_of_le n i j H =>
    simp only [Functor.map_comp, pathsFunctorOp_map_of_δ, pathsFunctorOp_map_of_σ]
    change (data.σ j.succ ≫ data.δ i.castSucc).op = (data.δ i ≫ data.σ j).op
    rw [data.δ_comp_σ_of_le H]
  | @δ_comp_σ_self n i =>
    simp only [Functor.map_comp, pathsFunctorOp_map_of_δ, pathsFunctorOp_map_of_σ]
    change (data.σ i ≫ data.δ i.castSucc).op = 𝟙 (op (data.obj n))
    rw [data.δ_comp_σ_self, op_id]
  | @δ_comp_σ_succ n i =>
    simp only [Functor.map_comp, pathsFunctorOp_map_of_δ, pathsFunctorOp_map_of_σ]
    change (data.σ i ≫ data.δ i.succ).op = 𝟙 (op (data.obj n))
    rw [data.δ_comp_σ_succ, op_id]
  | @δ_comp_σ_of_gt n i j H =>
    simp only [Functor.map_comp, pathsFunctorOp_map_of_δ, pathsFunctorOp_map_of_σ]
    change (data.σ j.castSucc ≫ data.δ i.succ).op = (data.δ i ≫ data.σ j).op
    rw [data.δ_comp_σ_of_gt H]
  | @σ_comp_σ n i j H =>
    simp only [Functor.map_comp, pathsFunctorOp_map_of_σ]
    change (data.σ j ≫ data.σ i.castSucc).op = (data.σ i ≫ data.σ j.succ).op
    rw [data.σ_comp_σ H]

/-- Intermediate opposite functor `SimplexCategoryGenRel ⥤ Cᵒᵖ` induced by `Data`. -/
def toOpFunctor (data : Data (C := C)) : SimplexCategoryGenRel ⥤ Cᵒᵖ :=
  Quotient.lift _ data.pathsFunctorOp fun _ _ _ _ h => data.respectsHomRel h

@[simp]
theorem toOpFunctor_obj_mk (data : Data (C := C)) (n : ℕ) :
    data.toOpFunctor.obj (SimplexCategoryGenRel.mk n) = op (data.obj n) :=
  rfl

theorem toOpFunctor_map_δ (data : Data (C := C)) {n : ℕ} (i : Fin (n + 2)) :
    data.toOpFunctor.map (SimplexCategoryGenRel.δ (n := n) i) = (data.δ i).op := by
  have : data.toOpFunctor.map (SimplexCategoryGenRel.δ i) =
      data.pathsFunctorOp.map ((Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.δ i)) := rfl
  rw [this, pathsFunctorOp_map_of_δ]

theorem toOpFunctor_map_σ (data : Data (C := C)) {n : ℕ} (i : Fin (n + 1)) :
    data.toOpFunctor.map (SimplexCategoryGenRel.σ (n := n) i) = (data.σ i).op := by
  have : data.toOpFunctor.map (SimplexCategoryGenRel.σ i) =
      data.pathsFunctorOp.map ((Paths.of FreeSimplexQuiver).map (FreeSimplexQuiver.σ i)) := rfl
  rw [this, pathsFunctorOp_map_of_σ]

/-- Simplicial object `SimplexCategoryGenRelᵒᵖ ⥤ C` from `Data` via `toOpFunctor`. -/
noncomputable def toGenRelFunctor (data : Data (C := C)) : SimplexCategoryGenRelᵒᵖ ⥤ C :=
  data.toOpFunctor.leftOp

@[simp]
theorem toGenRelFunctor_obj_op_mk (data : Data (C := C)) (n : ℕ) :
    data.toGenRelFunctor.obj (op (SimplexCategoryGenRel.mk n)) = data.obj n :=
  rfl

theorem toGenRelFunctor_obj (data : Data (C := C)) (x : SimplexCategoryGenRelᵒᵖ) :
    data.toGenRelFunctor.obj x = data.obj (unop x).len := by
  cases x with
  | op _ => rfl

theorem toGenRelFunctor_map_δ_op (data : Data (C := C)) {n : ℕ} (i : Fin (n + 2)) :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) i).op = data.δ i := by
  have h1 : data.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op =
      (data.toOpFunctor.map ((SimplexCategoryGenRel.δ i).op.unop)).unop := rfl
  have h2 : (SimplexCategoryGenRel.δ (n := n) i).op.unop = SimplexCategoryGenRel.δ i :=
    Quiver.Hom.unop_op _
  rw [h1, h2, data.toOpFunctor_map_δ]
  exact Quiver.Hom.unop_op _

theorem toGenRelFunctor_map_σ_op (data : Data (C := C)) {n : ℕ} (i : Fin (n + 1)) :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) i).op = data.σ i := by
  have h1 : data.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op =
      (data.toOpFunctor.map ((SimplexCategoryGenRel.σ i).op.unop)).unop := rfl
  have h2 : (SimplexCategoryGenRel.σ (n := n) i).op.unop = SimplexCategoryGenRel.σ i :=
    Quiver.Hom.unop_op _
  rw [h1, h2, data.toOpFunctor_map_σ]
  exact Quiver.Hom.unop_op _

@[simp]
theorem toGenRelFunctor_map_id (data : Data (C := C)) (x : SimplexCategoryGenRelᵒᵖ) :
    data.toGenRelFunctor.map (𝟙 x) = 𝟙 (data.toGenRelFunctor.obj x) :=
  data.toGenRelFunctor.map_id x

theorem toGenRelFunctor_map_comp (data : Data (C := C)) {x y z : SimplexCategoryGenRelᵒᵖ}
    (f : x ⟶ y) (g : y ⟶ z) :
    data.toGenRelFunctor.map (f ≫ g) =
      data.toGenRelFunctor.map f ≫ data.toGenRelFunctor.map g :=
  data.toGenRelFunctor.map_comp f g

@[simp]
theorem toGenRelFunctor_map_δ_comp_δ (data : Data (C := C)) {n : ℕ}
    {i j : Fin (n + 2)} (h : i ≤ j) :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n + 1) j.succ).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) i).op =
      data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n + 1) i.castSucc).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) j).op := by
  rw [toGenRelFunctor_map_δ_op, toGenRelFunctor_map_δ_op,
    toGenRelFunctor_map_δ_op, toGenRelFunctor_map_δ_op]
  exact data.δ_comp_δ h

@[simp]
theorem toGenRelFunctor_map_σ_comp_σ (data : Data (C := C)) {n : ℕ}
    {i j : Fin (n + 1)} (h : i ≤ j) :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) j).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n + 1) i.castSucc).op =
      data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) i).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n + 1) j.succ).op := by
  rw [toGenRelFunctor_map_σ_op, toGenRelFunctor_map_σ_op,
    toGenRelFunctor_map_σ_op, toGenRelFunctor_map_σ_op]
  exact data.σ_comp_σ h

@[simp]
theorem toGenRelFunctor_δ_comp_σ_of_le (data : Data (C := C)) {n : ℕ}
    {i : Fin (n + 2)} {j : Fin (n + 1)} (h : i ≤ j.castSucc) :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n + 1) j.succ).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n + 1) i.castSucc).op =
      data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) i).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) j).op := by
  rw [toGenRelFunctor_map_σ_op, toGenRelFunctor_map_δ_op,
    toGenRelFunctor_map_δ_op, toGenRelFunctor_map_σ_op]
  exact data.δ_comp_σ_of_le h

@[simp]
theorem toGenRelFunctor_δ_comp_σ_of_gt (data : Data (C := C)) {n : ℕ}
    {i : Fin (n + 2)} {j : Fin (n + 1)} (h : j.castSucc < i) :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n + 1) j.castSucc).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n + 1) i.succ).op =
      data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) i).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) j).op := by
  rw [toGenRelFunctor_map_σ_op, toGenRelFunctor_map_δ_op,
    toGenRelFunctor_map_δ_op, toGenRelFunctor_map_σ_op]
  exact data.δ_comp_σ_of_gt h

@[simp]
theorem toGenRelFunctor_δ_comp_σ_self (data : Data (C := C)) {n : ℕ}
    {i : Fin (n + 1)} :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) i).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) i.castSucc).op =
      𝟙 (data.obj n) := by
  rw [toGenRelFunctor_map_σ_op, toGenRelFunctor_map_δ_op]
  exact data.δ_comp_σ_self

@[simp]
theorem toGenRelFunctor_δ_comp_σ_succ (data : Data (C := C)) {n : ℕ}
    {i : Fin (n + 1)} :
    data.toGenRelFunctor.map (SimplexCategoryGenRel.σ (n := n) i).op ≫
        data.toGenRelFunctor.map (SimplexCategoryGenRel.δ (n := n) i.succ).op =
      𝟙 (data.obj n) := by
  rw [toGenRelFunctor_map_σ_op, toGenRelFunctor_map_δ_op]
  exact data.δ_comp_σ_succ

/--
A morphism of `Data C` is a family of maps in degree `n` commuting with
all face and degeneracy maps.
-/
structure Hom (X Y : Data C) where
  app : ∀ (n : ℕ), X.obj n ⟶ Y.obj n
  w_δ : ∀ {n : ℕ} (i : Fin (n + 2)), app (n + 1) ≫ Y.δ i = X.δ i ≫ app n
  w_σ : ∀ {n : ℕ} (i : Fin (n + 1)), app n ≫ Y.σ i = X.σ i ≫ app (n + 1)

@[ext]
theorem Hom.ext {X Y : Data C} {f g : Hom X Y} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f with
  | mk app₁ wδ₁ wσ₁ =>
    cases g with
    | mk app₂ wδ₂ wσ₂ =>
      have h_eq : app₁ = app₂ := funext h
      subst h_eq
      rfl

def Hom.id (X : Data C) : Hom X X where
  app _ := 𝟙 _
  w_δ := by
    intro n i
    simp
  w_σ := by
    intro n i
    simp

@[simp]
theorem Hom.id_app (X : Data C) (n : ℕ) : (Hom.id X).app n = 𝟙 _ :=
  rfl

def Hom.comp {X Y Z : Data C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  app n := f.app n ≫ g.app n
  w_δ := by
    intro n i
    calc
      (f.app (n + 1) ≫ g.app (n + 1)) ≫ Z.δ i
          = f.app (n + 1) ≫ (g.app (n + 1) ≫ Z.δ i) := by
            rw [Category.assoc]
      _ = f.app (n + 1) ≫ (Y.δ i ≫ g.app n) := by
            rw [g.w_δ i]
      _ = (f.app (n + 1) ≫ Y.δ i) ≫ g.app n := by
            rw [← Category.assoc]
      _ = (X.δ i ≫ f.app n) ≫ g.app n := by
            rw [f.w_δ i]
      _ = X.δ i ≫ (f.app n ≫ g.app n) := by
            rw [Category.assoc]
  w_σ := by
    intro n i
    calc
      (f.app n ≫ g.app n) ≫ Z.σ i
          = f.app n ≫ (g.app n ≫ Z.σ i) := by
            rw [Category.assoc]
      _ = f.app n ≫ (Y.σ i ≫ g.app (n + 1)) := by
            rw [g.w_σ i]
      _ = (f.app n ≫ Y.σ i) ≫ g.app (n + 1) := by
            rw [← Category.assoc]
      _ = (X.σ i ≫ f.app (n + 1)) ≫ g.app (n + 1) := by
            rw [f.w_σ i]
      _ = X.σ i ≫ (f.app (n + 1) ≫ g.app (n + 1)) := by
            rw [Category.assoc]

@[simp]
theorem Hom.comp_app {X Y Z : Data C} (f : Hom X Y) (g : Hom Y Z) (n : ℕ) :
    (Hom.comp f g).app n = f.app n ≫ g.app n :=
  rfl

end Data

instance {C : Type u} [Category.{v} C] : Category (Data C) where
  Hom := Data.Hom
  id := Data.Hom.id
  comp := Data.Hom.comp
  id_comp := by
    intro X Y f
    apply Data.Hom.ext
    intro n
    simp
  comp_id := by
    intro X Y f
    apply Data.Hom.ext
    intro n
    simp
  assoc := by
    intro W X Y Z f g h
    apply Data.Hom.ext
    intro n
    simp [Category.assoc]

@[simp]
theorem id_app {C : Type u} [Category.{v} C] (X : SimplicialObject.Data C) (n : ℕ) :
    (𝟙 X : Data.Hom X X).app n = 𝟙 _ :=
  rfl

@[simp]
theorem comp_app {C : Type u} [Category.{v} C] {X Y Z : SimplicialObject.Data C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n :=
  rfl

@[simp]
theorem comp_app_assoc {C : Type u} [Category.{v} C] {W X Y Z : SimplicialObject.Data C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ) :
    (f ≫ g ≫ h).app n = f.app n ≫ g.app n ≫ h.app n :=
  rfl

def mkData {C : Type u} [Category.{v} C] (obj : ℕ → C)
    (δ : ∀ {n}, Fin (n + 2) → (obj (n + 1) ⟶ obj n))
    (σ : ∀ {n}, Fin (n + 1) → (obj n ⟶ obj (n + 1)))
    (δ_comp_δ : ∀ {n} {i j : Fin (n + 2)} (_ : i ≤ j),
      δ j.succ ≫ δ i = δ i.castSucc ≫ δ j)
    (δ_comp_σ_of_le : ∀ {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (_ : i ≤ j.castSucc),
      σ j.succ ≫ δ i.castSucc = δ i ≫ σ j)
    (δ_comp_σ_self : ∀ {n} {i : Fin (n + 1)}, σ i ≫ δ i.castSucc = 𝟙 _)
    (δ_comp_σ_succ : ∀ {n} {i : Fin (n + 1)}, σ i ≫ δ i.succ = 𝟙 _)
    (δ_comp_σ_of_gt : ∀ {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (_ : j.castSucc < i),
      σ j.castSucc ≫ δ i.succ = δ i ≫ σ j)
    (σ_comp_σ : ∀ {n} {i j : Fin (n + 1)} (_ : i ≤ j),
      σ j ≫ σ i.castSucc = σ i ≫ σ j.succ) :
    Data C :=
  { obj := obj
    δ := δ
    σ := σ
    δ_comp_δ := δ_comp_δ
    δ_comp_σ_of_le := δ_comp_σ_of_le
    δ_comp_σ_self := δ_comp_σ_self
    δ_comp_σ_succ := δ_comp_σ_succ
    δ_comp_σ_of_gt := δ_comp_σ_of_gt
    σ_comp_σ := σ_comp_σ }

namespace Data

variable {C : Type u} [Category.{v} C] {X Y : Data C}

/--
Component family whose type is exactly `X.toGenRelFunctor.obj q ⟶ Y.toGenRelFunctor.obj q`,
eliminating `q : SimplexCategoryGenRelᵒᵖ` to `op (mk n)` and returning `f.app n`.
-/
def toGenRelNatTransApp (f : Hom X Y) (q : SimplexCategoryGenRelᵒᵖ) :
    X.toGenRelFunctor.obj q ⟶ Y.toGenRelFunctor.obj q :=
  match q with
  | op x => SimplexCategoryGenRel.rec (fun n => f.app n) x

@[simp]
theorem toGenRelNatTransApp_op_mk (f : Hom X Y) (n : ℕ) :
    toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n)) = f.app n :=
  rfl

theorem toGenRelNatTransApp_len (f : Hom X Y) (q : SimplexCategoryGenRelᵒᵖ) :
    toGenRelNatTransApp f q = f.app (unop q).len := by
  cases q with
  | op x =>
    rfl

/-- Naturality for a face generator, retaining the functor object types. -/
theorem toGenRelNatTransApp_naturality_δ (f : Hom X Y) {n : ℕ} (i : Fin (n + 2)) :
    X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
      toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n)) =
    toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (n + 1))) ≫
      Y.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op := by
  simp only [toGenRelFunctor_map_δ_op, toGenRelNatTransApp_op_mk]
  exact (f.w_δ i).symm

/-- Naturality for a degeneracy generator, retaining the functor object types. -/
theorem toGenRelNatTransApp_naturality_σ (f : Hom X Y) {n : ℕ} (i : Fin (n + 1)) :
    X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
      toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (n + 1))) =
    toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n)) ≫
      Y.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op := by
  simp only [toGenRelFunctor_map_σ_op, toGenRelNatTransApp_op_mk]
  exact (f.w_σ i).symm

/--
Correctly typed naturality predicate on `SimplexCategoryGenRel` morphisms.
It keeps `toGenRelFunctor.obj` types, not raw `X.obj len`.
-/
def genRelNatProp (f : Hom X Y) : MorphismProperty SimplexCategoryGenRel :=
  fun {a b} (h : a ⟶ b) =>
    X.toGenRelFunctor.map h.op ≫ toGenRelNatTransApp f (op a) =
    toGenRelNatTransApp f (op b) ≫ Y.toGenRelFunctor.map h.op

theorem genRelNatProp_id (f : Hom X Y) (n : ℕ) :
    (genRelNatProp f) (𝟙 (SimplexCategoryGenRel.mk n)) := by
  dsimp only [genRelNatProp]
  simp

theorem genRelNatProp_comp_δ (f : Hom X Y) {n m : ℕ}
    {u : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk m}
    {i : Fin (m + 2)} (hu : genRelNatProp f u) :
    genRelNatProp f (u ≫ SimplexCategoryGenRel.δ i) := by
  dsimp only [genRelNatProp] at *
  have h_map : X.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.δ i).op =
      X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
      X.toGenRelFunctor.map u.op := by
    rw [op_comp, X.toGenRelFunctor.map_comp]
  have h_mapY : Y.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.δ i).op =
      Y.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
      Y.toGenRelFunctor.map u.op := by
    rw [op_comp, Y.toGenRelFunctor.map_comp]
  calc
    X.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.δ i).op ≫
        toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n))
        = (X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
          X.toGenRelFunctor.map u.op) ≫
          toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n)) := by
          rw [h_map]
    _ = X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
          (X.toGenRelFunctor.map u.op ≫
            toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n))) := by
            rw [Category.assoc]
    _ = X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
          (toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk m)) ≫
            Y.toGenRelFunctor.map u.op) := by
            rw [hu]
    _ = (X.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
          toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk m))) ≫
          Y.toGenRelFunctor.map u.op := by
          rw [← Category.assoc]
    _ = (toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (m + 1))) ≫
          Y.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op) ≫
          Y.toGenRelFunctor.map u.op := by
          rw [toGenRelNatTransApp_naturality_δ f i]
    _ = toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (m + 1))) ≫
          (Y.toGenRelFunctor.map (SimplexCategoryGenRel.δ i).op ≫
            Y.toGenRelFunctor.map u.op) := by
            rw [Category.assoc]
    _ = toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (m + 1))) ≫
          Y.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.δ i).op := by
          rw [h_mapY]

theorem genRelNatProp_comp_σ (f : Hom X Y) {n m : ℕ}
    {u : SimplexCategoryGenRel.mk n ⟶ SimplexCategoryGenRel.mk (m + 1)}
    {i : Fin (m + 1)} (hu : genRelNatProp f u) :
    genRelNatProp f (u ≫ SimplexCategoryGenRel.σ i) := by
  dsimp only [genRelNatProp] at *
  have h_map : X.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.σ i).op =
      X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
      X.toGenRelFunctor.map u.op := by
    rw [op_comp, X.toGenRelFunctor.map_comp]
  have h_mapY : Y.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.σ i).op =
      Y.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
      Y.toGenRelFunctor.map u.op := by
    rw [op_comp, Y.toGenRelFunctor.map_comp]
  calc
    X.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.σ i).op ≫
        toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n))
        = (X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
          X.toGenRelFunctor.map u.op) ≫
          toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n)) := by
          rw [h_map]
    _ = X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
          (X.toGenRelFunctor.map u.op ≫
            toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk n))) := by
            rw [Category.assoc]
    _ = X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
          (toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (m + 1))) ≫
            Y.toGenRelFunctor.map u.op) := by
            rw [hu]
    _ = (X.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
          toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk (m + 1)))) ≫
          Y.toGenRelFunctor.map u.op := by
          rw [← Category.assoc]
    _ = (toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk m)) ≫
          Y.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op) ≫
          Y.toGenRelFunctor.map u.op := by
          rw [toGenRelNatTransApp_naturality_σ f i]
    _ = toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk m)) ≫
          (Y.toGenRelFunctor.map (SimplexCategoryGenRel.σ i).op ≫
            Y.toGenRelFunctor.map u.op) := by
            rw [Category.assoc]
    _ = toGenRelNatTransApp f (op (SimplexCategoryGenRel.mk m)) ≫
          Y.toGenRelFunctor.map (u ≫ SimplexCategoryGenRel.σ i).op := by
          rw [h_mapY]

theorem genRelNatProp_hom (f : Hom X Y) {a b : SimplexCategoryGenRel} (h : a ⟶ b) :
    genRelNatProp f h :=
  SimplexCategoryGenRel.hom_induction (genRelNatProp f)
    (fun {n} => genRelNatProp_id f n)
    (fun {_n _m} _u i hu => genRelNatProp_comp_δ (f := f) (i := i) hu)
    (fun {_n _m} _u i hu => genRelNatProp_comp_σ (f := f) (i := i) hu) h

/-- Naturality square for the correctly typed component family. -/
theorem toGenRelNatTransApp_naturality (f : Hom X Y)
    {A B : SimplexCategoryGenRelᵒᵖ} (p : A ⟶ B) :
    X.toGenRelFunctor.map p ≫ toGenRelNatTransApp f B =
    toGenRelNatTransApp f A ≫ Y.toGenRelFunctor.map p := by
  obtain ⟨a⟩ := A
  obtain ⟨b⟩ := B
  have h := genRelNatProp_hom f p.unop
  dsimp only [genRelNatProp] at h
  have h_eq : (p.unop).op = p := by
    simp
  rw [h_eq] at h
  exact h

/--
The natural transformation induced by `f : Data.Hom X Y` on
`SimplexCategoryGenRelᵒᵖ ⥤ C`.
-/
noncomputable def toGenRelNatTrans (f : Hom X Y) :
    X.toGenRelFunctor ⟶ Y.toGenRelFunctor where
  app := toGenRelNatTransApp f
  naturality := by
    intro _ _ p
    exact toGenRelNatTransApp_naturality f p

@[simp]
theorem toGenRelNatTrans_app (f : Hom X Y) (q : SimplexCategoryGenRelᵒᵖ) :
    (toGenRelNatTrans f).app q = toGenRelNatTransApp f q :=
  rfl

@[simp]
theorem toGenRelNatTrans_app_op_mk (f : Hom X Y) (n : ℕ) :
    (toGenRelNatTrans f).app (op (SimplexCategoryGenRel.mk n)) = f.app n :=
  rfl

@[simp]
theorem toGenRelNatTrans_app_len (f : Hom X Y) (q : SimplexCategoryGenRelᵒᵖ) :
    (toGenRelNatTrans f).app q = f.app (unop q).len := by
  rw [toGenRelNatTrans_app, toGenRelNatTransApp_len]

end Data

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Data

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Functorial action of `F : C ⥤ D` on `Data C`, degreewise by `F`. -/
def mapObj (F : C ⥤ D) (X : Data C) : Data D where
  obj n := F.obj (X.obj n)
  δ i := F.map (X.δ i)
  σ i := F.map (X.σ i)
  δ_comp_δ := by
    intro n i j h
    calc
      F.map (X.δ j.succ) ≫ F.map (X.δ i)
          = F.map (X.δ j.succ ≫ X.δ i) := (F.map_comp _ _).symm
      _ = F.map (X.δ i.castSucc ≫ X.δ j) := by rw [X.δ_comp_δ h]
      _ = F.map (X.δ i.castSucc) ≫ F.map (X.δ j) := F.map_comp _ _
  δ_comp_σ_of_le := by
    intro n i j h
    calc
      F.map (X.σ j.succ) ≫ F.map (X.δ i.castSucc)
          = F.map (X.σ j.succ ≫ X.δ i.castSucc) := (F.map_comp _ _).symm
      _ = F.map (X.δ i ≫ X.σ j) := by rw [X.δ_comp_σ_of_le h]
      _ = F.map (X.δ i) ≫ F.map (X.σ j) := F.map_comp _ _
  δ_comp_σ_self := by
    intro n i
    calc
      F.map (X.σ i) ≫ F.map (X.δ i.castSucc)
          = F.map (X.σ i ≫ X.δ i.castSucc) := (F.map_comp _ _).symm
      _ = F.map (𝟙 _) := by rw [X.δ_comp_σ_self]
      _ = 𝟙 _ := F.map_id _
  δ_comp_σ_succ := by
    intro n i
    calc
      F.map (X.σ i) ≫ F.map (X.δ i.succ)
          = F.map (X.σ i ≫ X.δ i.succ) := (F.map_comp _ _).symm
      _ = F.map (𝟙 _) := by rw [X.δ_comp_σ_succ]
      _ = 𝟙 _ := F.map_id _
  δ_comp_σ_of_gt := by
    intro n i j h
    calc
      F.map (X.σ j.castSucc) ≫ F.map (X.δ i.succ)
          = F.map (X.σ j.castSucc ≫ X.δ i.succ) := (F.map_comp _ _).symm
      _ = F.map (X.δ i ≫ X.σ j) := by rw [X.δ_comp_σ_of_gt h]
      _ = F.map (X.δ i) ≫ F.map (X.σ j) := F.map_comp _ _
  σ_comp_σ := by
    intro n i j h
    calc
      F.map (X.σ j) ≫ F.map (X.σ i.castSucc)
          = F.map (X.σ j ≫ X.σ i.castSucc) := (F.map_comp _ _).symm
      _ = F.map (X.σ i ≫ X.σ j.succ) := by rw [X.σ_comp_σ h]
      _ = F.map (X.σ i) ≫ F.map (X.σ j.succ) := F.map_comp _ _

@[simp]
theorem mapObj_obj (F : C ⥤ D) (X : Data C) (n : ℕ) :
    (mapObj F X).obj n = F.obj (X.obj n) :=
  rfl

@[simp]
theorem mapObj_δ (F : C ⥤ D) (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    (mapObj F X).δ i = F.map (X.δ i) :=
  rfl

@[simp]
theorem mapObj_σ (F : C ⥤ D) (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    (mapObj F X).σ i = F.map (X.σ i) :=
  rfl

@[simp]
theorem mapObj_id_obj (X : Data C) (n : ℕ) :
    (mapObj (𝟭 C) X).obj n = X.obj n :=
  rfl

@[simp]
theorem mapObj_id_δ (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    (mapObj (𝟭 C) X).δ i = X.δ i :=
  rfl

@[simp]
theorem mapObj_id_σ (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    (mapObj (𝟭 C) X).σ i = X.σ i :=
  rfl

@[simp]
theorem mapObj_comp_obj (F : C ⥤ D) (G : D ⥤ E) (X : Data C) (n : ℕ) :
    (mapObj (F ⋙ G) X).obj n = (mapObj G (mapObj F X)).obj n :=
  rfl

@[simp]
theorem mapObj_comp_δ (F : C ⥤ D) (G : D ⥤ E) (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    (mapObj (F ⋙ G) X).δ i = (mapObj G (mapObj F X)).δ i :=
  rfl

@[simp]
theorem mapObj_comp_σ (F : C ⥤ D) (G : D ⥤ E) (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    (mapObj (F ⋙ G) X).σ i = (mapObj G (mapObj F X)).σ i :=
  rfl

/-- Componentwise action on morphisms. -/
def mapHom {X Y : Data C} (F : C ⥤ D) (f : Hom X Y) :
    Hom (mapObj F X) (mapObj F Y) where
  app n := F.map (f.app n)
  w_δ := by
    intro n i
    calc
      F.map (f.app (n + 1)) ≫ F.map (Y.δ i)
          = F.map (f.app (n + 1) ≫ Y.δ i) := (F.map_comp _ _).symm
      _ = F.map (X.δ i ≫ f.app n) := by rw [f.w_δ i]
      _ = F.map (X.δ i) ≫ F.map (f.app n) := F.map_comp _ _
  w_σ := by
    intro n i
    calc
      F.map (f.app n) ≫ F.map (Y.σ i)
          = F.map (f.app n ≫ Y.σ i) := (F.map_comp _ _).symm
      _ = F.map (X.σ i ≫ f.app (n + 1)) := by rw [f.w_σ i]
      _ = F.map (X.σ i) ≫ F.map (f.app (n + 1)) := F.map_comp _ _

@[simp]
theorem mapHom_app {X Y : Data C} (F : C ⥤ D) (f : Hom X Y) (n : ℕ) :
    (mapHom F f).app n = F.map (f.app n) :=
  rfl

@[simp]
theorem mapHom_id_functor_app {X Y : Data C} (f : Hom X Y) (n : ℕ) :
    (mapHom (𝟭 C) f).app n = f.app n :=
  rfl

@[simp]
theorem mapHom_comp_functor_app {X Y : Data C} (F : C ⥤ D) (G : D ⥤ E) (f : Hom X Y) (n : ℕ) :
    (mapHom (F ⋙ G) f).app n = (mapHom G (mapHom F f)).app n :=
  rfl

@[simp]
theorem mapHom_id (F : C ⥤ D) (X : Data C) :
    mapHom F (Hom.id X) = Hom.id (mapObj F X) := by
  apply Hom.ext
  intro n
  simp [F.map_id]

@[simp]
theorem mapHom_comp {X Y Z : Data C} (F : C ⥤ D) (f : Hom X Y) (g : Hom Y Z) :
    mapHom F (Hom.comp f g) = Hom.comp (mapHom F f) (mapHom F g) := by
  apply Hom.ext
  intro n
  simp [F.map_comp]

/-- Functor `Data C ⥤ Data D` induced by `F : C ⥤ D`. -/
def mapFunctor (F : C ⥤ D) : Data C ⥤ Data D where
  obj X := mapObj F X
  map f := mapHom F f
  map_id X := by
    apply Hom.ext
    intro n
    simp [F.map_id]
  map_comp f g := by
    apply Hom.ext
    intro n
    simp [F.map_comp]

@[simp]
theorem mapFunctor_obj (F : C ⥤ D) (X : Data C) :
    (mapFunctor F).obj X = mapObj F X :=
  rfl

@[simp]
theorem mapFunctor_map {X Y : Data C} (F : C ⥤ D) (f : X ⟶ Y) :
    (mapFunctor F).map f = mapHom F f :=
  rfl

@[simp]
theorem mapFunctor_map_app {X Y : Data C} (F : C ⥤ D) (f : X ⟶ Y) (n : ℕ) :
    ((mapFunctor F).map f).app n = F.map (f.app n) :=
  rfl

@[simp]
theorem mapFunctor_obj_obj (F : C ⥤ D) (X : Data C) (n : ℕ) :
    ((mapFunctor F).obj X).obj n = F.obj (X.obj n) :=
  rfl

@[simp]
theorem mapFunctor_obj_δ (F : C ⥤ D) (X : Data C) {n : ℕ} (i : Fin (n + 2)) :
    ((mapFunctor F).obj X).δ i = F.map (X.δ i) :=
  rfl

@[simp]
theorem mapFunctor_obj_σ (F : C ⥤ D) (X : Data C) {n : ℕ} (i : Fin (n + 1)) :
    ((mapFunctor F).obj X).σ i = F.map (X.σ i) :=
  rfl

end Data

end SimplicialObject

end CategoryTheory
