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
# Injective objects in nonnegative cochain complexes

Let A be an abelian category. A family Iₙ of coefficient objects determines
a cochain complex with term Iₙ ⊞ Iₙ₊₁ and differential (a,b) ↦ (b,0).
For any nonnegative cochain complex K and maps aₙ:Kⁿ → Iₙ, the component
(aₙ,aₙ₊₁ ∘ d_Kⁿ) defines a cochain map from K into this complex.

If every Iₙ is injective in A, the resulting cofree complex is injective
in the category of nonnegative cochain complexes. If A has enough injectives,
choosing monomorphisms Kⁿ → Iₙ gives a monomorphism from K to such an
injective cochain complex. Consequently the cochain category has enough
injectives.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- In an abelian category A, the nonnegative cochain complex associated to
an arbitrary family I:ℕ → A, with n-th term Iₙ ⊞ Iₙ₊₁ and differential
the second projection followed by the first inclusion into Iₙ₊₁ ⊞ Iₙ₊₂,
that is, (a,b) ↦ (b,0). -/
abbrev injectiveCofree (I : ℕ → A) : CochainComplex A ℕ :=
  CochainComplex.of (fun n => I n ⊞ I (n + 1))
    (fun n => (biprod.snd (X := I n) (Y := I (n + 1))) ≫
      (biprod.inl (X := I (n + 1)) (Y := I (n + 1 + 1)))) (by
        intro n
        simp only [Category.assoc, biprod.inl_snd_assoc, comp_zero, zero_comp])

/-- For an arbitrary family I:ℕ → A in an abelian category, the differential
from degree n to n+1 of its cofree complex is
Iₙ ⊞ Iₙ₊₁ → Iₙ₊₁ → Iₙ₊₁ ⊞ Iₙ₊₂, using the second projection and
the first inclusion. In biproduct coordinates it sends (a,b) to (b,0). -/
theorem injectiveCofree_d (I : ℕ → A) (n : ℕ) :
    (injectiveCofree I).d n (n + 1) =
      (biprod.snd (X := I n) (Y := I (n + 1))) ≫ (biprod.inl (X := I (n + 1)) (Y := I (n + 1 + 1))) := by
  exact CochainComplex.of_d (fun k => I k ⊞ I (k + 1))
    (fun k => (biprod.snd (X := I k) (Y := I (k + 1))) ≫
      (biprod.inl (X := I (k + 1)) (Y := I (k + 1 + 1)))) n

/-- Let A be abelian, K a nonnegative cochain complex, I:ℕ → A a family,
and aₙ:Kⁿ → Iₙ arbitrary coefficient maps. The cochain map K → Cofree(I)
whose n-th component into Iₙ ⊞ Iₙ₊₁ is
(aₙ,aₙ₊₁ ∘ d_Kⁿ). -/
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

/-- In an abelian category A, for a nonnegative cochain complex K, a family
Iₙ and coefficient maps aₙ:Kⁿ → Iₙ, the n-th component of the induced
map K → Cofree(I), followed by projection onto Iₙ, equals aₙ. -/
@[reassoc]
theorem injectiveCofreeHom_fst (K : CochainComplex A ℕ) (I : ℕ → A)
    (a : ∀ n, K.X n ⟶ I n) (n : ℕ) :
    (injectiveCofreeHom K I a).f n ≫ (biprod.fst (X := I n) (Y := I (n + 1))) = a n := by
  exact biprod.lift_fst _ _

/-- In an abelian category A, for coefficient maps aₙ:Kⁿ → Iₙ from a
nonnegative cochain complex K, the n-th component of K → Cofree(I),
followed by projection onto Iₙ₊₁, equals aₙ₊₁ ∘ d_Kⁿ. -/
@[reassoc]
theorem injectiveCofreeHom_snd (K : CochainComplex A ℕ) (I : ℕ → A)
    (a : ∀ n, K.X n ⟶ I n) (n : ℕ) :
    (injectiveCofreeHom K I a).f n ≫ (biprod.snd (X := I n) (Y := I (n + 1))) =
      K.d n (n + 1) ≫ a (n + 1) := by
  exact biprod.lift_snd _ _

/-- Let A be abelian and g:K → Cofree(I) a map of nonnegative cochain
complexes, where Cofree(I)ⁿ=Iₙ ⊞ Iₙ₊₁ and d(a,b)=(b,0).
The second coordinate of g in degree n equals the first coordinate of
g in degree n+1 composed with d_Kⁿ:
pr₂ ∘ gₙ = pr₁ ∘ gₙ₊₁ ∘ d_Kⁿ. -/
@[reassoc]
theorem injectiveCofree_snd (K : CochainComplex A ℕ) (I : ℕ → A)
    (g : K ⟶ injectiveCofree I) (n : ℕ) :
    g.f n ≫ (biprod.snd (X := I n) (Y := I (n + 1))) =
      K.d n (n + 1) ≫ g.f (n + 1) ≫
        (biprod.fst (X := I (n + 1)) (Y := I (n + 1 + 1))) := by
  have h := congrArg (fun f : K.X n ⟶ (injectiveCofree I).X (n + 1) =>
    f ≫ (biprod.fst (X := I (n + 1)) (Y := I (n + 1 + 1)))) (g.comm n (n + 1))
  simpa only [CochainComplex.of_d, Category.assoc, biprod.inl_fst, Category.comp_id] using h

/-- For a family I:ℕ → A in an abelian category A, if every Iₙ is injective,
then the cofree complex with terms Iₙ ⊞ Iₙ₊₁ and differential (a,b)↦(b,0)
is an injective object of the category of nonnegative cochain complexes. -/
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

/-- If an abelian category A has enough injectives, then its category of
nonnegative cochain complexes has enough injectives. For each K, injective
embeddings Kⁿ → Iₙ induce a monomorphism K → Cofree(I), whose target is
injective in the cochain category. -/
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
