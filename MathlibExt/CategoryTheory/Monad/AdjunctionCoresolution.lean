/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Monad.Bar
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The actual adjunction contraction of monad coresolutions

After applying the left adjoint, the counit of the same adjunction supplies
the extra codegeneracies of the canonical monad coresolution. Its split and
coface equations use the original unit insertions and the literal monad powers.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u₁ v₁ u₂ v₂

open CategoryTheory
open scoped BigOperators

namespace CategoryTheory.Monad

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

private theorem barEtaAtPos_zero_power (T : Monad C) (n : ℕ) (X : C) :
    barEtaAtPos T n 0 X ≫ eqToHom (monadPow_succ_obj_eq T n X) =
      T.η.app ((monadPow T n).obj X) := by
  simp only [barEtaAtPos, Fin.rev_zero]
  induction n generalizing X with
  | zero => exact Category.comp_id _
  | succ n ih => exact ih (T.obj X)

private theorem etaAtPos_castSucc_power (T : Monad C) (n : ℕ) (i : Fin (n + 1))
    (X : C) :
    etaAtPos T (n + 1) i.castSucc X ≫
        eqToHom (monadPow_succ_obj_eq T (n + 1) X) =
      eqToHom (monadPow_succ_obj_eq T n X) ≫ T.map (etaAtPos T n i X) := by
  induction n generalizing X with
  | zero =>
    have hi : i = 0 := by
      apply Fin.ext
      omega
    subst i
    exact monadPow_obj_T_comm_naturality T 0 (T.η.app X)
  | succ n ih =>
    cases i with
    | mk val hval =>
      cases val with
      | zero => exact monadPow_obj_T_comm_naturality T (n + 1) (T.η.app X)
      | succ k =>
        let j : Fin (n + 1) := ⟨k, Nat.lt_of_succ_lt_succ hval⟩
        exact ih j (T.obj X)

private theorem barEtaAtPos_succ_power (T : Monad C) (n : ℕ) (i : Fin (n + 1))
    (X : C) :
    barEtaAtPos T (n + 1) i.succ X ≫
        eqToHom (monadPow_succ_obj_eq T (n + 1) X) =
      eqToHom (monadPow_succ_obj_eq T n X) ≫ T.map (barEtaAtPos T n i X) := by
  simp only [barEtaAtPos, Fin.rev_succ]
  exact etaAtPos_castSucc_power T n i.rev X

variable {F : C ⥤ D} {R : D ⥤ C}

/-- The actual counit retracts the next monad power after the same left adjoint. -/
def adjunctionCoresolutionRetraction (adj : F ⊣ R) (n : ℕ) (X : C) :
    F.obj ((monadPow adj.toMonad (n + 1)).obj X) ⟶
      F.obj ((monadPow adj.toMonad n).obj X) :=
  F.map (eqToHom (monadPow_succ_obj_eq adj.toMonad n X)) ≫
    adj.counit.app (F.obj ((monadPow adj.toMonad n).obj X))

set_option backward.isDefEq.respectTransparency.types false in
/-- The counit contractions are natural in every original object morphism. -/
theorem adjunctionCoresolutionRetraction_naturality (adj : F ⊣ R) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    F.map ((monadPow adj.toMonad (n + 1)).map f) ≫
        adjunctionCoresolutionRetraction adj n Y =
      adjunctionCoresolutionRetraction adj n X ≫
        F.map ((monadPow adj.toMonad n).map f) := by
  let T := adj.toMonad
  let qX := eqToHom (monadPow_succ_obj_eq T n X)
  let qY := eqToHom (monadPow_succ_obj_eq T n Y)
  let g := (monadPow T n).map f
  have hp := monadPow_succ_obj_eq_naturality T n f
  have he : F.map (T.map g) ≫ adj.counit.app (F.obj ((monadPow T n).obj Y)) =
      adj.counit.app (F.obj ((monadPow T n).obj X)) ≫ F.map g :=
    adj.counit.naturality (F.map g)
  change F.map ((monadPow T (n + 1)).map f) ≫
      (F.map qY ≫ adj.counit.app (F.obj ((monadPow T n).obj Y))) =
    (F.map qX ≫ adj.counit.app (F.obj ((monadPow T n).obj X))) ≫ F.map g
  rw [← Category.assoc, ← F.map_comp, hp, F.map_comp, Category.assoc, he]
  exact (Category.assoc (F.map qX)
    (adj.counit.app (F.obj ((monadPow T n).obj X))) (F.map g)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The original first coface and the counit contraction compose to the identity. -/
theorem adjunctionCoresolutionRetraction_coface_zero (adj : F ⊣ R) (n : ℕ) (X : C) :
    F.map (barEtaAtPos adj.toMonad n 0 X) ≫
      adjunctionCoresolutionRetraction adj n X = 𝟙 _ := by
  unfold adjunctionCoresolutionRetraction
  rw [← Category.assoc, ← F.map_comp, barEtaAtPos_zero_power]
  exact adj.left_triangle_components ((monadPow adj.toMonad n).obj X)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every shifted coface commutes with the actual counit contraction. -/
theorem adjunctionCoresolutionRetraction_coface_succ (adj : F ⊣ R) (n : ℕ)
    (i : Fin (n + 1)) (X : C) :
    F.map (barEtaAtPos adj.toMonad (n + 1) i.succ X) ≫
        adjunctionCoresolutionRetraction adj (n + 1) X =
      adjunctionCoresolutionRetraction adj n X ≫ F.map (barEtaAtPos adj.toMonad n i X) := by
  let T := adj.toMonad
  let g := barEtaAtPos T n i X
  have hp := barEtaAtPos_succ_power T n i X
  have he : F.map (T.map g) ≫ adj.counit.app (F.obj ((monadPow T (n + 1)).obj X)) =
      adj.counit.app (F.obj ((monadPow T n).obj X)) ≫ F.map g :=
    adj.counit.naturality (F.map g)
  unfold adjunctionCoresolutionRetraction
  rw [← Category.assoc, ← F.map_comp, hp, F.map_comp, Category.assoc, he]
  exact (Category.assoc (F.map (eqToHom (monadPow_succ_obj_eq T n X)))
    (adj.counit.app (F.obj ((monadPow T n).obj X))) (F.map g)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The same actual counit supplies the alternating differential contraction in every degree. -/
theorem adjunctionCoresolutionRetraction_alternating [Preadditive D]
    (adj : F ⊣ R) (n : ℕ) (X : C) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        F.map (barEtaAtPos adj.toMonad (n + 1) i X)) ≫
        adjunctionCoresolutionRetraction adj (n + 1) X +
      adjunctionCoresolutionRetraction adj n X ≫
        (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
          F.map (barEtaAtPos adj.toMonad n i X)) = 𝟙 _ := by
  let a := fun i : Fin (n + 1) =>
    (-1 : ℤ) ^ i.val • F.map (barEtaAtPos adj.toMonad n i X)
  have hs (i : Fin (n + 1)) :
      ((-1 : ℤ) ^ i.succ.val • F.map (barEtaAtPos adj.toMonad (n + 1) i.succ X)) ≫
          adjunctionCoresolutionRetraction adj (n + 1) X =
        -(adjunctionCoresolutionRetraction adj n X ≫ a i) := by
    rw [Preadditive.zsmul_comp, adjunctionCoresolutionRetraction_coface_succ]
    simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul,
      a, Preadditive.comp_zsmul]
  rw [Preadditive.sum_comp, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    adjunctionCoresolutionRetraction_coface_zero]
  simp_rw [hs]
  rw [Finset.sum_neg_distrib, ← Preadditive.comp_sum]
  change (𝟙 _ + -(adjunctionCoresolutionRetraction adj n X ≫ ∑ i, a i)) +
    (adjunctionCoresolutionRetraction adj n X ≫ ∑ i, a i) = 𝟙 _
  exact neg_add_cancel_right _ _

end CategoryTheory.Monad
