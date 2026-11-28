/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Group objects transported along a monomorphism

In a cartesian monoidal category, let `j : R ⟶ G` be a monomorphism into a group object `G`
through which the unit, the multiplication `(j ⊗ j) ≫ μ` and the inverse `j ≫ ι` of `G` factor.
Then the factorizations make `R` a group object (`CategoryTheory.GrpObj.ofMono`) and `j` a
homomorphism (`CategoryTheory.GrpObj.isMonHom_ofMono`): the group axioms of `R` follow from
those of `G` after composing with the monomorphism `j`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]

/-- Transport a group object structure along a monomorphism `j : R ⟶ G` through which the
unit, multiplication and inverse of `G` factor. -/
noncomputable abbrev GrpObj.ofMono {R G : C} [GrpObj G] (j : R ⟶ G) [Mono j]
    (one : 𝟙_ C ⟶ R) (mul : R ⊗ R ⟶ R) (inv : R ⟶ R)
    (hone : one ≫ j = η[G]) (hmul : mul ≫ j = (j ⊗ₘ j) ≫ μ[G])
    (hinv : inv ≫ j = j ≫ ι[G]) : GrpObj R where
  one := one
  mul := mul
  inv := inv
  one_mul := by
    rw [← cancel_mono j, Category.assoc, hmul, ← leftUnitor_naturality,
      ← MonObj.one_mul (X := G), ← Category.assoc, ← Category.assoc]
    congr 1
    ext
    · simp [hone, toUnit_unique (fst (𝟙_ C) R) (toUnit _)]
    · simp [leftUnitor_hom]
  mul_one := by
    rw [← cancel_mono j, Category.assoc, hmul, ← rightUnitor_naturality,
      ← MonObj.mul_one (X := G), ← Category.assoc, ← Category.assoc]
    congr 1
    ext
    · simp [rightUnitor_hom]
    · simp [hone, toUnit_unique (snd R (𝟙_ C)) (toUnit _)]
  mul_assoc := by
    have h1 : mul ▷ R ≫ (j ⊗ₘ j) = ((j ⊗ₘ j) ⊗ₘ j) ≫ μ[G] ▷ G := by
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        hmul, Category.id_comp, Category.comp_id]
    have h2 : R ◁ mul ≫ (j ⊗ₘ j) = (j ⊗ₘ (j ⊗ₘ j)) ≫ G ◁ μ[G] := by
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        hmul, Category.id_comp, Category.comp_id]
    rw [← cancel_mono j, Category.assoc, Category.assoc, Category.assoc, hmul, reassoc_of% h1,
      reassoc_of% h2, MonObj.mul_assoc (X := G), associator_naturality_assoc]
  left_inv := by
    rw [← cancel_mono j, Category.assoc, hmul, Category.assoc, hone, lift_map_assoc, hinv,
      Category.id_comp]
    have : lift (j ≫ ι[G]) j = j ≫ lift ι[G] (𝟙 G) := by ext <;> simp
    rw [this, Category.assoc, GrpObj.left_inv]
    simp
  right_inv := by
    rw [← cancel_mono j, Category.assoc, hmul, Category.assoc, hone, lift_map_assoc, hinv,
      Category.id_comp]
    have : lift j (j ≫ ι[G]) = j ≫ lift (𝟙 G) ι[G] := by ext <;> simp
    rw [this, Category.assoc, GrpObj.right_inv]
    simp

/-- The monomorphism `j` is a homomorphism for the group structure `GrpObj.ofMono`. -/
lemma GrpObj.isMonHom_ofMono {R G : C} [GrpObj G] (j : R ⟶ G) [Mono j]
    (one : 𝟙_ C ⟶ R) (mul : R ⊗ R ⟶ R) (inv : R ⟶ R)
    (hone : one ≫ j = η[G]) (hmul : mul ≫ j = (j ⊗ₘ j) ≫ μ[G])
    (hinv : inv ≫ j = j ≫ ι[G]) :
    letI := GrpObj.ofMono j one mul inv hone hmul hinv
    IsMonHom j :=
  letI := GrpObj.ofMono j one mul inv hone hmul hinv
  ⟨hone, hmul⟩

end CategoryTheory
