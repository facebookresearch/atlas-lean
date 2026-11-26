/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.Injective.AugmentedExactComparison

/-!
# Comparison maps from exact augmented cochain complexes

In an abelian category `C`, an augmented cochain complex with monic
coaugmentation and exact augmentation and positive rows admits a map
into every cochain complex with injective terms, extending a prescribed
map between the augmented objects.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, let `ι : X[0] → P` be monic in
degree zero, with exact augmentation and positive rows, and let
`κ : Y[0] → Q` have injective target terms. For every `f : X → Y`
there exists `a : P → Q` with `ι ≫ a = single₀(f) ≫ κ`. -/
theorem exists_augmentedExactComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : C} {P Q : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ P) [Mono (ι.f 0)]
    (κ : (CochainComplex.single₀ C).obj Y ⟶ Q)
    (h₀ : (ShortComplex.mk (ι.f 0) (P.d 0 1)
      (by rw [ι.comm 0 1, HomologicalComplex.single_obj_d, zero_comp])).Exact)
    (hP : ∀ n : ℕ, (ShortComplex.mk (P.d n (n + 1)) (P.d (n + 1) (n + 2))
      (P.d_comp_d n (n + 1) (n + 2))).Exact)
    (hQ : ∀ n : ℕ, Injective (Q.X n)) (f : X ⟶ Y) :
    ∃ a : P ⟶ Q, ι ≫ a = (CochainComplex.single₀ C).map f ≫ κ := by
  let : Injective (Q.X 0) := hQ 0
  let : Injective (Q.X 1) := hQ 1
  have hm : Mono (ι.f 0) := inferInstance
  let a₀ : P.X 0 ⟶ Q.X 0 :=
    @Injective.factorThru C _ (Q.X 0) (((CochainComplex.single₀ C).obj X).X 0)
      (P.X 0) (hQ 0) (f ≫ κ.f 0) (ι.f 0) hm
  have ha₀ : ι.f 0 ≫ a₀ = f ≫ κ.f 0 :=
    @Injective.comp_factorThru C _ (Q.X 0) (((CochainComplex.single₀ C).obj X).X 0)
      (P.X 0) (hQ 0) (f ≫ κ.f 0) (ι.f 0) hm
  have hκ : κ.f 0 ≫ Q.d 0 1 = 0 := by
    rw [κ.comm 0 1, HomologicalComplex.single_obj_d, zero_comp]
  have hz : ι.f 0 ≫ (a₀ ≫ Q.d 0 1) = 0 := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Q.d 0 1) ha₀).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun t => f ≫ t) hκ).trans (comp_zero))))
  let a₁ : P.X 1 ⟶ Q.X 1 := h₀.descToInjective (a₀ ≫ Q.d 0 1) hz
  have ha₁ : a₀ ≫ Q.d 0 1 = P.d 0 1 ≫ a₁ := (h₀.comp_descToInjective _ _).symm
  let succ : ∀ (n : ℕ)
      (p : Σ' (g : P.X n ⟶ Q.X n) (g' : P.X (n + 1) ⟶ Q.X (n + 1)),
        g ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ g'),
      Σ' g'' : P.X (n + 2) ⟶ Q.X (n + 2),
        p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ g'' := by
    intro n p
    rcases p with ⟨g, g', hg⟩
    let : Injective (Q.X (n + 2)) := hQ (n + 2)
    have hz' : P.d n (n + 1) ≫ (g' ≫ Q.d (n + 1) (n + 2)) = 0 := by
      rw [← Category.assoc, ← hg, Category.assoc, Q.d_comp_d, comp_zero]
    exact ⟨(hP n).descToInjective _ hz', ((hP n).comp_descToInjective _ _).symm⟩
  let a := CochainComplex.mkHom P Q a₀ a₁ ha₁ succ
  refine ⟨a, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change ι.f 0 ≫ a.f 0 = ((CochainComplex.single₀ C).map f).f 0 ≫ κ.f 0
      rw [CochainComplex.single₀_map_f_zero]
      exact ha₀
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 X
        (n + 1) (by omega)).eq_of_src _ _

end CategoryTheory
