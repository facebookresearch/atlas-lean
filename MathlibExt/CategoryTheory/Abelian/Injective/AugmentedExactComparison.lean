/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Homotopy uniqueness for exact augmented cochain sources

In an abelian category `C`, let `X → P⁰ → P¹` and all positive
rows of a natural-index cochain complex `P` be exact. Maps from `P`
to a cochain complex with injective terms are homotopic if they agree
on the augmentation. Applying any additive functor preserves equality
of the resulting homology maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, let `ι : X[0] → P` augment a
cochain complex with exact row `X → P⁰ → P¹` and exact positive
rows. If every term of `Q` is injective and `a : P → Q` satisfies
`ι ≫ a = 0`, then `a` is null-homotopic. -/
def augmentedExactNullHomotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {X : C} {P Q : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ P)
    (h₀ : (ShortComplex.mk (ι.f 0) (P.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact)
    (hP : ∀ n : ℕ, (ShortComplex.mk (P.d n (n + 1)) (P.d (n + 1) (n + 2))
      (P.d_comp_d n (n + 1) (n + 2))).Exact)
    (hQ : ∀ n : ℕ, Injective (Q.X n))
    (a : P ⟶ Q) (ha : ι ≫ a = 0) : Homotopy a 0 := by
  let : Injective (Q.X 0) := hQ 0
  let : Injective (Q.X 1) := hQ 1
  have ha₀ : ι.f 0 ≫ a.f 0 = 0 := congrArg (fun f => f.f 0) ha
  let s₀ : P.X 1 ⟶ Q.X 0 := h₀.descToInjective (a.f 0) ha₀
  have hs₀ : P.d 0 1 ≫ s₀ = a.f 0 := h₀.comp_descToInjective _ _
  have hz₁ : P.d 0 1 ≫ (a.f 1 - s₀ ≫ Q.d 0 1) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hs₀, a.comm 0 1, sub_self]
  let s₁ : P.X 2 ⟶ Q.X 1 := (hP 0).descToInjective (a.f 1 - s₀ ≫ Q.d 0 1) hz₁
  have hs₁ : P.d 1 2 ≫ s₁ = a.f 1 - s₀ ≫ Q.d 0 1 :=
    (hP 0).comp_descToInjective _ _
  refine Homotopy.mkCoinductive a s₀ hs₀.symm s₁ ?_ ?_
  · exact (eq_add_of_sub_eq hs₁.symm).trans (add_comm _ _)
  · intro n p
    rcases p with ⟨g, g', hg⟩
    let : Injective (Q.X (n + 2)) := hQ (n + 2)
    have hz : P.d (n + 1) (n + 2) ≫
        (a.f (n + 2) - g' ≫ Q.d (n + 1) (n + 2)) = 0 := by
      rw [Preadditive.comp_sub, ← a.comm (n + 1) (n + 2), hg,
        Preadditive.add_comp, Category.assoc, Q.d_comp_d,
        comp_zero, zero_add, Category.assoc, sub_self]
    let s : P.X (n + 3) ⟶ Q.X (n + 2) :=
      (hP (n + 1)).descToInjective (a.f (n + 2) - g' ≫ Q.d (n + 1) (n + 2)) hz
    have hs : P.d (n + 2) (n + 3) ≫ s =
        a.f (n + 2) - g' ≫ Q.d (n + 1) (n + 2) :=
      (hP (n + 1)).comp_descToInjective _ _
    exact ⟨s, (eq_add_of_sub_eq hs.symm).trans (add_comm _ _)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, let `ι : X[0] → P` have exact
augmentation and positive cochain rows. If all terms of `Q` are
injective and `a,b : P → Q` agree after `ι`, there is a
cochain homotopy `a ~ b`. -/
def augmentedExactComparisonHomotopy
    {C : Type u} [Category.{v} C] [Abelian C]
    {X : C} {P Q : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ P)
    (h₀ : (ShortComplex.mk (ι.f 0) (P.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact)
    (hP : ∀ n : ℕ, (ShortComplex.mk (P.d n (n + 1)) (P.d (n + 1) (n + 2))
      (P.d_comp_d n (n + 1) (n + 2))).Exact)
    (hQ : ∀ n : ℕ, Injective (Q.X n))
    (a b : P ⟶ Q) (hab : ι ≫ a = ι ≫ b) : Homotopy a b :=
  Homotopy.equivSubZero.invFun (augmentedExactNullHomotopy ι h₀ hP hQ (a - b)
    (by rw [Preadditive.comp_sub, hab, sub_self]))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C`, `D` be abelian and `F : C → D` additive. If a
cochain complex `P` has exact augmentation and positive rows,
`Q` has injective terms, and `a,b : P → Q` agree on the
augmentation, the maps on degree-`n` homology of `F(P) → F(Q)`
induced by `F(a)` and `F(b)` are equal. -/
theorem augmentedExactComparison_homologyMap_eq
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]
    {X : C} {P Q : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ P)
    (h₀ : (ShortComplex.mk (ι.f 0) (P.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact)
    (hP : ∀ n : ℕ, (ShortComplex.mk (P.d n (n + 1)) (P.d (n + 1) (n + 2))
      (P.d_comp_d n (n + 1) (n + 2))).Exact)
    (hQ : ∀ n : ℕ, Injective (Q.X n))
    (a b : P ⟶ Q) (hab : ι ≫ a = ι ≫ b) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map b) n :=
  (F.mapHomotopy (augmentedExactComparisonHomotopy ι h₀ hP hQ a b hab)).homologyMap_eq n

end CategoryTheory
