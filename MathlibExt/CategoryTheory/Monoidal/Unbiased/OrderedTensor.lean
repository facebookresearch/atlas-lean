/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# OrderedTensor

Recursive ordered finite tensor functors associated to a binary monoidal category.
-/

/- Source proof segment: OrderedTensor -/
section source_OrderedTensor
/-!
# Ordered heterogeneous finite tensors

Finite tensors are formed from the supplied binary tensor product, with
the supplied tensor unit in degree zero. No cartesian structure is used.
This file is the ordered foundation for the unbiased tensor construction.
-/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.MonoidalCategory.OrderedTensor

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Left associated tensor of a finite ordered family, with the tensor
unit as the empty tensor. -/
def obj : {n : ℕ} → (Fin n → C) → C
  | 0, _ => 𝟙_ C
  | n + 1, X => obj (fun i : Fin n => X i.castSucc) ⊗ X (Fin.last n)

/-- Tensor a component morphism in every slot of an ordered finite family. -/
def map : {n : ℕ} → {X Y : Fin n → C} →
    (∀ i, X i ⟶ Y i) → (obj X ⟶ obj Y)
  | 0, _, _, _ => 𝟙 (𝟙_ C)
  | n + 1, _, _, f => map (fun i : Fin n => f i.castSucc) ⊗ₘ f (Fin.last n)

/-- The empty tensor is the original tensor unit. -/
@[simp] theorem obj_zero (X : Fin 0 → C) : obj X = 𝟙_ C := rfl

/-- A positive tensor is the tensor of its initial factors and its last factor. -/
@[simp] theorem obj_succ {n : ℕ} (X : Fin (n + 1) → C) :
    obj X = obj (fun i : Fin n => X i.castSucc) ⊗ X (Fin.last n) := rfl

/-- Tensoring identities gives the identity. -/
@[simp] theorem map_id : ∀ {n : ℕ} (X : Fin n → C),
    map (fun i => 𝟙 (X i)) = 𝟙 (obj X)
  | 0, _ => rfl
  | n + 1, X => by
      change map (fun i : Fin n => 𝟙 (X i.castSucc)) ⊗ₘ 𝟙 (X (Fin.last n)) =
        𝟙 (obj (fun i : Fin n => X i.castSucc) ⊗ X (Fin.last n))
      rw [map_id, id_tensorHom_id]

/-- Tensoring componentwise composites gives the composite of the tensor maps. -/
theorem map_comp : ∀ {n : ℕ} {X Y Z : Fin n → C}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i),
    map (fun i => f i ≫ g i) = map f ≫ map g
  | 0, _, _, _, _, _ => by
      change 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)
      exact (Category.id_comp _).symm
  | n + 1, X, Y, Z, f, g => by
      change map (fun i : Fin n => f i.castSucc ≫ g i.castSucc) ⊗ₘ
        (f (Fin.last n) ≫ g (Fin.last n)) = _
      rw [map_comp]
      exact (tensorHom_comp_tensorHom _ (f (Fin.last n)) _ (g (Fin.last n))).symm

/-- The heterogeneous ordered finite tensor functor. -/
def functor (C : Type u) [Category.{v} C] [MonoidalCategory C] (n : ℕ) :
    (Fin n → C) ⥤ C where
  obj := obj
  map := map
  map_id X := map_id X
  map_comp f g := map_comp f g

/-- Componentwise isomorphisms induce the original finite tensor isomorphism. -/
def iso {n : ℕ} {X Y : Fin n → C} (e : ∀ i, X i ≅ Y i) : obj X ≅ obj Y where
  hom := map (fun i => (e i).hom)
  inv := map (fun i => (e i).inv)
  hom_inv_id := by
    rw [← map_comp]
    simp only [Iso.hom_inv_id, map_id]
  inv_hom_id := by
    rw [← map_comp]
    simp only [Iso.inv_hom_id, map_id]

/-- Equal finite input counts and equal original input objects have
equal ordered tensor carriers. -/
theorem obj_congr {m n : ℕ} (h : m = n) (X : Fin m → C) (Y : Fin n → C)
    (hXY : ∀ i, X i = Y (Fin.cast h i)) : obj X = obj Y := by
  subst n
  have hX : X = Y := by
    funext i
    exact hXY i
  exact congrArg obj hX

/-- Transport the original ordered tensor along equality of its
input count and pointwise equality of its actual input objects. -/
def congrIso {m n : ℕ} (h : m = n) (X : Fin m → C) (Y : Fin n → C)
    (hXY : ∀ i, X i = Y (Fin.cast h i)) : obj X ≅ obj Y :=
  eqToIso (obj_congr h X Y hXY)

/-- In a monoidal category, a singleton ordered tensor `obj X` for `X : Fin 1 → C`
is isomorphic to `X 0` by the left unitor `λ_ (X 0) : 𝟙_ C ⊗ X 0 ≅ X 0`. -/
def singletonIso (X : Fin 1 → C) : obj X ≅ X 0 := λ_ (X 0)

/-- For `X : Fin 1 → C` in a monoidal category, the forward singleton comparison is
`(singletonIso X).hom = (λ_ (X 0)).hom`, a map from `𝟙_ C ⊗ X 0` to `X 0`. -/
@[simp] theorem singletonIso_hom (X : Fin 1 → C) :
    (singletonIso X).hom = (λ_ (X 0)).hom := rfl

/-- The singleton comparison is natural in the actual component map. -/
@[reassoc] theorem singletonIso_naturality {X Y : Fin 1 → C}
    (f : ∀ i, X i ⟶ Y i) :
    map f ≫ (singletonIso Y).hom = (singletonIso X).hom ≫ f 0 := by
  change (𝟙 (𝟙_ C) ⊗ₘ f 0) ≫ (λ_ (Y 0)).hom = (λ_ (X 0)).hom ≫ f 0
  rw [id_tensorHom]
  exact leftUnitor_naturality (f 0)

end CategoryTheory.MonoidalCategory.OrderedTensor
end
end source_OrderedTensor
