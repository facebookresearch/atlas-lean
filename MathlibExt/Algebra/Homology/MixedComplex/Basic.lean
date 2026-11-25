/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Additive

/-!
# Mixed complexes

A mixed complex in a preadditive category is a chain complex with a
square-zero degree-one operator B that anticommutes with the differential.
Mixed-complex morphisms form a category with a faithful additive forgetful
functor to chain complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive

noncomputable section

universe v u

/-- A mixed complex in a preadditive category.

The underlying complex is homologically graded over `ℕ`.  The extra
operator raises degree by one.  The separate degree-zero equation is the
boundary case of `bB + Bb = 0`, where there is no degree `-1` term. -/
@[ext]
structure MixedComplex (C : Type u) [Category.{v} C] [Preadditive C] where
  /-- The underlying chain complex. -/
  underlying : ChainComplex C ℕ
  /-- The degree-one mixed operator. -/
  B : ∀ n : ℕ, underlying.X n ⟶ underlying.X (n + 1)
  /-- The mixed operator squares to zero. -/
  B_sq : ∀ n : ℕ, B n ≫ B (n + 1) = 0
  /-- The degree-zero boundary equation. -/
  B_b_zero : B 0 ≫ underlying.d 1 0 = 0
  /-- The mixed operator anticommutes with the differential in positive
  source degrees. -/
  anticomm : ∀ n : ℕ,
    B (n + 1) ≫ underlying.d (n + 2) (n + 1) +
      underlying.d (n + 1) n ≫ B n = 0

namespace MixedComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[reassoc (attr := simp)]
theorem B_comp_B (M : MixedComplex C) (n : ℕ) :
    M.B n ≫ M.B (n + 1) = 0 :=
  M.B_sq n

@[reassoc (attr := simp)]
theorem B_zero_comp_d (M : MixedComplex C) :
    M.B 0 ≫ M.underlying.d 1 0 = 0 :=
  M.B_b_zero

@[simp]
theorem B_comp_d_add_d_comp_B (M : MixedComplex C) (n : ℕ) :
    M.B (n + 1) ≫ M.underlying.d (n + 2) (n + 1) +
      M.underlying.d (n + 1) n ≫ M.B n = 0 :=
  M.anticomm n

/-- A morphism of mixed complexes is a chain map commuting with `B`. -/
@[ext]
structure Hom (M N : MixedComplex C) where
  /-- The underlying chain map. -/
  underlying : M.underlying ⟶ N.underlying
  /-- Compatibility with the mixed operators. -/
  comm_B' : ∀ n : ℕ,
    underlying.f n ≫ N.B n = M.B n ≫ underlying.f (n + 1)

@[reassoc (attr := simp)]
theorem Hom.comm_B {M N : MixedComplex C} (f : Hom M N) (n : ℕ) :
    f.underlying.f n ≫ N.B n = M.B n ≫ f.underlying.f (n + 1) :=
  f.comm_B' n

/-- The identity morphism of a mixed complex. -/
def Hom.id (M : MixedComplex C) : Hom M M where
  underlying := 𝟙 M.underlying
  comm_B' n := by simp

/-- Composition of mixed-complex morphisms. -/
def Hom.comp {M N P : MixedComplex C} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  underlying := f.underlying ≫ g.underlying
  comm_B' n := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      Category.assoc, g.comm_B, ← Category.assoc, f.comm_B,
      Category.assoc]

instance : Category.{v} (MixedComplex C) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp f := by
    apply Hom.ext
    simp [Hom.id, Hom.comp]
  comp_id f := by
    apply Hom.ext
    simp [Hom.id, Hom.comp]
  assoc f g h := by
    apply Hom.ext
    simp [Hom.comp, Category.assoc]

/-- Two mixed-complex morphisms are equal when their chain maps are equal. -/
@[ext]
theorem hom_ext {M N : MixedComplex C} (f g : M ⟶ N)
    (h : f.underlying = g.underlying) : f = g := by
  apply Hom.ext
  exact h

@[simp]
theorem id_underlying (M : MixedComplex C) :
    (𝟙 M : M ⟶ M).underlying = 𝟙 M.underlying :=
  rfl

@[simp]
theorem comp_underlying {M N P : MixedComplex C} (f : M ⟶ N)
    (g : N ⟶ P) : (f ≫ g).underlying = f.underlying ≫ g.underlying :=
  rfl

/-- Forget the mixed operator. -/
@[implicit_reducible]
def underlyingFunctor (C : Type u) [Category.{v} C] [Preadditive C] :
    MixedComplex C ⥤ ChainComplex C ℕ where
  obj M := M.underlying
  map f := f.underlying

@[simp]
theorem underlyingFunctor_obj (M : MixedComplex C) :
    (underlyingFunctor C).obj M = M.underlying :=
  rfl

@[simp]
theorem underlyingFunctor_map {M N : MixedComplex C} (f : M ⟶ N) :
    (underlyingFunctor C).map f = f.underlying :=
  rfl

instance : (underlyingFunctor C).Faithful where
  map_injective h := hom_ext _ _ h

instance homZero (M N : MixedComplex C) : Zero (M ⟶ N) where
  zero :=
    { underlying := 0
      comm_B' := by simp }

instance homAdd (M N : MixedComplex C) : Add (M ⟶ N) where
  add f g :=
    { underlying := f.underlying + g.underlying
      comm_B' := by
        intro n
        simp only [HomologicalComplex.add_f_apply, add_comp, comp_add,
          f.comm_B, g.comm_B] }

instance homNeg (M N : MixedComplex C) : Neg (M ⟶ N) where
  neg f :=
    { underlying := -f.underlying
      comm_B' := by
        intro n
        simp only [HomologicalComplex.neg_f_apply, neg_comp, comp_neg,
          f.comm_B] }

instance homSub (M N : MixedComplex C) : Sub (M ⟶ N) where
  sub f g :=
    { underlying := f.underlying - g.underlying
      comm_B' := by
        intro n
        simp only [HomologicalComplex.sub_f_apply, sub_comp, comp_sub,
          f.comm_B, g.comm_B] }

instance homNatSMul (M N : MixedComplex C) : SMul ℕ (M ⟶ N) where
  smul a f :=
    { underlying := a • f.underlying
      comm_B' := by
        intro n
        simp only [HomologicalComplex.nsmul_f_apply, nsmul_comp, comp_nsmul,
          f.comm_B] }

instance homIntSMul (M N : MixedComplex C) : SMul ℤ (M ⟶ N) where
  smul a f :=
    { underlying := a • f.underlying
      comm_B' := by
        intro n
        simp only [HomologicalComplex.zsmul_f_apply, zsmul_comp, comp_zsmul,
          f.comm_B] }

@[simp]
theorem zero_underlying (M N : MixedComplex C) :
    (0 : M ⟶ N).underlying = 0 :=
  rfl

@[simp]
theorem add_underlying {M N : MixedComplex C} (f g : M ⟶ N) :
    (f + g).underlying = f.underlying + g.underlying :=
  rfl

@[simp]
theorem neg_underlying {M N : MixedComplex C} (f : M ⟶ N) :
    (-f).underlying = -f.underlying :=
  rfl

@[simp]
theorem sub_underlying {M N : MixedComplex C} (f g : M ⟶ N) :
    (f - g).underlying = f.underlying - g.underlying :=
  rfl

@[simp]
theorem nsmul_underlying {M N : MixedComplex C} (a : ℕ) (f : M ⟶ N) :
    (a • f).underlying = a • f.underlying :=
  rfl

@[simp]
theorem zsmul_underlying {M N : MixedComplex C} (a : ℤ) (f : M ⟶ N) :
    (a • f).underlying = a • f.underlying :=
  rfl

theorem hom_underlying_injective (M N : MixedComplex C) :
    Function.Injective (fun f : M ⟶ N => f.underlying) := by
  intro f g h
  exact hom_ext f g h

instance (M N : MixedComplex C) : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f => f.underlying)
    (hom_underlying_injective M N)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

instance : Preadditive (MixedComplex C) where

instance : (underlyingFunctor C).Additive where

end MixedComplex
