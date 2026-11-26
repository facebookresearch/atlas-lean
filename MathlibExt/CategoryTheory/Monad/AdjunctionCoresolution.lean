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
# Counit contractions after applying a left adjoint to a monad coresolution

Let F : C → D and U : D → C form an adjunction, with induced monad T=UF. The counit gives
retractions s_n : F(T^{n+1}X) → F(T^nX), natural in X. They split the first unit insertion and
commute with shifted unit cofaces.

If D is preadditive, let D_n be the alternating sum of the F-images of the n+1 unit insertions
T^nX → T^{n+1}X. Then D_{n+1}≫s_{n+1}+s_n≫D_n=id_{F(T^{n+1}X)}, the contraction identity in
every n≥0.
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

/-- Let F : C → D and U : D → C form an adjunction with monad T=UF. For n ∈ ℕ and X ∈ C, define
s_n : F(T^{n+1}X) → F(T^nX) by the canonical successor-power identification followed by
ε_{F(T^nX)}. This is the counit retraction of the next unit-insertion term. -/
def adjunctionCoresolutionRetraction (adj : F ⊣ R) (n : ℕ) (X : C) :
    F.obj ((monadPow adj.toMonad (n + 1)).obj X) ⟶
      F.obj ((monadPow adj.toMonad n).obj X) :=
  F.map (eqToHom (monadPow_succ_obj_eq adj.toMonad n X)) ≫
    adj.counit.app (F.obj ((monadPow adj.toMonad n).obj X))

set_option backward.isDefEq.respectTransparency.types false in
/-- For an adjunction F ⊣ U, T=UF, n ∈ ℕ, and f : X → Y, the retractions s satisfy
F(T^{n+1}f)≫s_n(Y)=s_n(X)≫F(T^n f). Both sides go from F(T^{n+1}X) to F(T^nY). -/
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
/-- Let F ⊣ U be an adjunction, T=UF, n ∈ ℕ, and X ∈ C. The first source-ordered insertion
v_n^0=barEtaAtPos(T,n,0,X), after applying F, satisfies F(v_n^0)≫s_n=id_{F(T^nX)}, where s_n
is the counit power retraction. -/
theorem adjunctionCoresolutionRetraction_coface_zero (adj : F ⊣ R) (n : ℕ) (X : C) :
    F.map (barEtaAtPos adj.toMonad n 0 X) ≫
      adjunctionCoresolutionRetraction adj n X = 𝟙 _ := by
  unfold adjunctionCoresolutionRetraction
  rw [← Category.assoc, ← F.map_comp, barEtaAtPos_zero_power]
  exact adj.left_triangle_components ((monadPow adj.toMonad n).obj X)

set_option backward.isDefEq.respectTransparency.types false in
/-- For an adjunction F ⊣ U, T=UF, n ∈ ℕ, i ∈ Fin(n+1), and X ∈ C, the source-ordered unit
insertions v satisfy F(v_{n+1}^{i+1})≫s_{n+1}=s_n≫F(v_n^i). This is the counit-retraction
compatibility for every shifted coface. -/
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
/-- Let F ⊣ U be an adjunction with preadditive target D, and T=UF. Put
D_n=Σ_{i∈Fin(n+1)}(-1)^i·F(barEtaAtPos(T,n,i,X)) and s_n the counit retraction. For every n ∈
ℕ and X ∈ C, D_{n+1}≫s_{n+1}+s_n≫D_n=id_{F(T^{n+1}X)}. The signs use the displayed finite
indices. -/
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
