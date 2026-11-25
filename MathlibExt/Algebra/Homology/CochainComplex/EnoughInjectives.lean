/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Enough injectives in nonnegative cochain complexes

Adjacent injective coefficient objects form a cofree complex with binary
biproduct terms. Degreewise injective covers embed every nonnegative
cochain complex into such an injective complex.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Cofree cochain complex with adjacent coefficient biproducts. -/
abbrev injectiveCofree (I : ℕ → A) : CochainComplex A ℕ :=
  CochainComplex.of (fun n => I n ⊞ I (n + 1))
    (fun n => (biprod.snd (X := I n) (Y := I (n + 1))) ≫
      (biprod.inl (X := I (n + 1)) (Y := I (n + 1 + 1)))) (by
        intro n
        simp only [Category.assoc, biprod.inl_snd_assoc, comp_zero, zero_comp])

/-- The differential is the second projection followed by the first inclusion. -/
theorem injectiveCofree_d (I : ℕ → A) (n : ℕ) :
    (injectiveCofree I).d n (n + 1) =
      (biprod.snd (X := I n) (Y := I (n + 1))) ≫ (biprod.inl (X := I (n + 1)) (Y := I (n + 1 + 1))) := by
  exact CochainComplex.of_d (fun k => I k ⊞ I (k + 1))
    (fun k => (biprod.snd (X := I k) (Y := I (k + 1))) ≫
      (biprod.inl (X := I (k + 1)) (Y := I (k + 1 + 1)))) n

/-- A coefficient family defines a map into the cofree complex. -/
def injectiveCofreeHom (K : CochainComplex A ℕ) (I : ℕ → A)
    (a : ∀ n, K.X n ⟶ I n) : K ⟶ injectiveCofree I :=
  CochainComplex.ofHom
    (fun n => biprod.lift (a n) (K.d n (n + 1) ≫ a (n + 1))) (by
      intro n
      rw [injectiveCofree_d]
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
          biprod.inl_fst, Category.comp_id]
      · simp only [Category.assoc, biprod.lift_snd, biprod.inl_snd, comp_zero]
        rw [← Category.assoc, K.d_comp_d, zero_comp])

/-- First coefficient of the cofree map. -/
@[reassoc]
theorem injectiveCofreeHom_fst (K : CochainComplex A ℕ) (I : ℕ → A)
    (a : ∀ n, K.X n ⟶ I n) (n : ℕ) :
    (injectiveCofreeHom K I a).f n ≫ (biprod.fst (X := I n) (Y := I (n + 1))) = a n := by
  exact biprod.lift_fst _ _

/-- The differential determines the second coefficient of the cofree map. -/
@[reassoc]
theorem injectiveCofreeHom_snd (K : CochainComplex A ℕ) (I : ℕ → A)
    (a : ∀ n, K.X n ⟶ I n) (n : ℕ) :
    (injectiveCofreeHom K I a).f n ≫ (biprod.snd (X := I n) (Y := I (n + 1))) =
      K.d n (n + 1) ≫ a (n + 1) := by
  exact biprod.lift_snd _ _

/-- The first coefficient determines the second for every map into the cofree complex. -/
@[reassoc]
theorem injectiveCofree_snd (K : CochainComplex A ℕ) (I : ℕ → A)
    (g : K ⟶ injectiveCofree I) (n : ℕ) :
    g.f n ≫ (biprod.snd (X := I n) (Y := I (n + 1))) =
      K.d n (n + 1) ≫ g.f (n + 1) ≫
        (biprod.fst (X := I (n + 1)) (Y := I (n + 1 + 1))) := by
  have h := congrArg (fun f : K.X n ⟶ (injectiveCofree I).X (n + 1) =>
    f ≫ (biprod.fst (X := I (n + 1)) (Y := I (n + 1 + 1)))) (g.comm n (n + 1))
  simpa only [CochainComplex.of_d, Category.assoc, biprod.inl_fst, Category.comp_id] using h

/-- A cofree complex with injective coefficients is injective. -/
theorem injectiveCofree_injective (I : ℕ → A) [∀ n, Injective (I n)] :
    Injective (injectiveCofree I) where
  factors {X Y} g f hf := by
    letI : Mono f := hf
    let a : ∀ n, Y.X n ⟶ I n := fun n =>
      Injective.factorThru (g.f n ≫ (biprod.fst (X := I n) (Y := I (n + 1)))) (f.f n)
    let b : Y ⟶ injectiveCofree I := injectiveCofreeHom Y I a
    refine ⟨b, ?_⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply biprod.hom_ext
    · change (f.f n ≫ b.f n) ≫ (biprod.fst (X := I n) (Y := I (n + 1))) =
        g.f n ≫ (biprod.fst (X := I n) (Y := I (n + 1)))
      rw [Category.assoc, injectiveCofreeHom_fst]
      exact Injective.comp_factorThru _ _
    · change (f.f n ≫ b.f n) ≫ (biprod.snd (X := I n) (Y := I (n + 1))) =
        g.f n ≫ (biprod.snd (X := I n) (Y := I (n + 1)))
      calc
        _ = f.f n ≫ (Y.d n (n + 1) ≫ a (n + 1)) := by
          rw [Category.assoc, injectiveCofreeHom_snd]
        _ = (X.d n (n + 1) ≫ f.f (n + 1)) ≫ a (n + 1) := by
          rw [← Category.assoc, f.comm]
        _ = X.d n (n + 1) ≫ (g.f (n + 1) ≫
            (biprod.fst (X := I (n + 1)) (Y := I (n + 1 + 1)))) := by
          rw [Category.assoc, Injective.comp_factorThru]
        _ = _ := (injectiveCofree_snd X I g n).symm

/-- Degreewise injective covers give enough injectives in nonnegative cochain complexes. -/
instance enoughInjectives [EnoughInjectives A] : EnoughInjectives (CochainComplex A ℕ) where
  presentation K := by
    let I : ℕ → A := fun n => Injective.under (K.X n)
    let a : ∀ n, K.X n ⟶ I n := fun n => Injective.ι (K.X n)
    let J : CochainComplex A ℕ := injectiveCofree I
    let f : K ⟶ J := injectiveCofreeHom K I a
    letI : ∀ n, Injective (I n) := fun n => by dsimp only [I]; infer_instance
    letI : Injective J := injectiveCofree_injective I
    letI : Mono f := by
      apply HomologicalComplex.mono_of_mono_f
      intro n
      have h : f.f n ≫ (biprod.fst (X := I n) (Y := I (n + 1))) = a n :=
        injectiveCofreeHom_fst K I a n
      letI : Mono (a n) := by dsimp only [a, I]; infer_instance
      exact mono_of_mono_fac h
    exact ⟨{ J := J, f := f }⟩

end CochainComplex
