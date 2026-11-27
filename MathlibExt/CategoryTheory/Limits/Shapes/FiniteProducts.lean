/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Head and tail of a chosen finite product

The chosen product indexed by `Fin (n + 1)` is compared with the chosen
binary product of its first factor and chosen tail product. Both maps use
the original projections. The comparison is natural in every factor map
and gives the corresponding isomorphism of the original product arrows.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.Pi

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- The actual chosen successor product splits into its first factor and tail. -/
def finSuccProductIso (n : ℕ) (X : Fin (n + 1) → C) :
    ∏ᶜ X ≅ X 0 ⨯ ∏ᶜ (fun i : Fin n => X i.succ) where
  hom := prod.lift (CategoryTheory.Limits.Pi.π X 0)
      (CategoryTheory.Limits.Pi.lift fun i => CategoryTheory.Limits.Pi.π X i.succ)
  inv :=
      CategoryTheory.Limits.Pi.lift (Fin.cases prod.fst
        (fun i => prod.snd ≫ CategoryTheory.Limits.Pi.π _ i))
  hom_inv_id := by
    apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π, Fin.cases_zero,
        prod.lift_fst, Category.id_comp]
    · simp only [Category.assoc, CategoryTheory.Limits.Pi.lift_comp_π, Fin.cases_succ,
        Category.id_comp]
      rw [← Category.assoc, prod.lift_snd, CategoryTheory.Limits.Pi.lift_comp_π]
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, CategoryTheory.Limits.Pi.lift_comp_π,
        Fin.cases_zero, Category.id_comp]
    · apply CategoryTheory.Limits.Pi.hom_ext
      intro i
      simp only [Category.assoc, prod.lift_snd, CategoryTheory.Limits.Pi.lift_comp_π,
        Fin.cases_succ, Category.id_comp]

/-- Both forward and inverse legs are the literal selected projections. -/
theorem finSuccProductIso_legs (n : ℕ) (X : Fin (n + 1) → C) :
    (finSuccProductIso n X).hom ≫ prod.fst = CategoryTheory.Limits.Pi.π X 0 ∧
    (∀ i : Fin n,
        (finSuccProductIso n X).hom ≫ prod.snd ≫ CategoryTheory.Limits.Pi.π _ i =
        CategoryTheory.Limits.Pi.π X i.succ) ∧
    (finSuccProductIso n X).inv ≫ CategoryTheory.Limits.Pi.π X 0 = prod.fst ∧
    (∀ i : Fin n,
        (finSuccProductIso n X).inv ≫ CategoryTheory.Limits.Pi.π X i.succ = prod.snd ≫
        CategoryTheory.Limits.Pi.π _ i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact prod.lift_fst _ _
  · intro i
    simp only [finSuccProductIso]
    rw [← Category.assoc, prod.lift_snd, CategoryTheory.Limits.Pi.lift_comp_π]
  · simp only [finSuccProductIso, CategoryTheory.Limits.Pi.lift_comp_π, Fin.cases_zero]
  · intro i
    simp only [finSuccProductIso, CategoryTheory.Limits.Pi.lift_comp_π, Fin.cases_succ]

/-- The whole successor-product comparison commutes with every factor map. -/
theorem finSuccProductIso_naturality (n : ℕ) (X Y : Fin (n + 1) → C)
    (f : ∀ i, X i ⟶ Y i) :
    CategoryTheory.Limits.Pi.map f ≫ (finSuccProductIso n Y).hom =
      (finSuccProductIso n X).hom ≫ prod.map (f 0)
          (CategoryTheory.Limits.Pi.map fun i : Fin n => f i.succ) := by
  apply prod.hom_ext
  · simp only [Category.assoc, finSuccProductIso, prod.lift_fst, CategoryTheory.Limits.Pi.map_π,
      prod.map_fst]
    rw [← Category.assoc, prod.lift_fst]
  · apply CategoryTheory.Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, finSuccProductIso, prod.lift_snd,
        CategoryTheory.Limits.Pi.lift_comp_π,
      CategoryTheory.Limits.Pi.map_π, prod.map_snd]
    rw [← Category.assoc, ← Category.assoc, prod.lift_snd,
      CategoryTheory.Limits.Pi.lift_comp_π]


/-- The original successor product arrow is the product of its head and tail arrows. -/
def finSuccProductArrowIso (n : ℕ)
    {X Y : Fin (n + 1) → C} (f : ∀ i, X i ⟶ Y i) :
    Arrow.mk (Pi.map f) ≅
      Arrow.mk (prod.map (f 0) (Pi.map (fun i : Fin n => f i.succ))) :=
  Arrow.isoMk (finSuccProductIso n X) (finSuccProductIso n Y)
    (finSuccProductIso_naturality n X Y f).symm

end CategoryTheory.Limits.Pi
