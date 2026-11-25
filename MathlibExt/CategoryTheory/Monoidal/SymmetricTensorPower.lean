/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.TensorPowers
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Symmetric tensor powers indexed by finite bijections

The symmetric braiding acts functorially on the existing left-associated
finite tensor powers. The resulting finite-bijection action is compatible
with ordered block sums and the ambient braiding.

This file introduces no new tensor-power carrier, global instance, Day
convolution, spectrum, or model-category structure.
-/

public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped MonoidalCategory

namespace CategoryTheory.MonoidalCategory.SymmetricTensorPower

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
  [SymmetricCategory.{v} C]

/-- Swap the last two factors of a left-associated tensor power. -/
private noncomputable def adjacentSwapIso (X : C) (k : ℕ) :
    tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2) :=
  (α_ (tensorPowObj X k) X X) ≪≫
    MonoidalCategory.whiskerLeftIso (tensorPowObj X k) (β_ X X) ≪≫
    (α_ (tensorPowObj X k) X X).symm

/-- The one-way adjacent word `s₀ ⋯ s_(i-1)` in right-to-left
coordinates. -/
private noncomputable def oneWayCycleIso (X : C) :
    (n : ℕ) → Fin (n + 1) →
      (tensorPowObj X (n + 1) ≅ tensorPowObj X (n + 1))
  | 0, _ => Iso.refl _
  | n + 1, i =>
      Fin.cases (Iso.refl _)
        (fun q => adjacentSwapIso X n ≪≫
          tensorIso (oneWayCycleIso X n q) (Iso.refl X)) i

/-- In right-to-left coordinates, the star transposition exchanging zero
with the specified coordinate, expressed by a linear adjacent word. -/
private noncomputable def moveZeroIso (X : C) :
    (n : ℕ) → Fin n → (tensorPowObj X n ≅ tensorPowObj X n)
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      Fin.cases (Iso.refl _)
        (fun q => oneWayCycleIso X n q.succ ≪≫
          (oneWayCycleIso X n q.castSucc).symm) i

/-- The linear star word satisfies the right-normal recursion used by the
permutation action laws. -/
private theorem moveZeroIso_succ (X : C) (k : ℕ)
    (q : Fin (k + 1)) :
    moveZeroIso X (k + 2) q.succ =
      (tensorIso (moveZeroIso X (k + 1) q) (Iso.refl X) ≪≫
          adjacentSwapIso X k) ≪≫
        (tensorIso (moveZeroIso X (k + 1) q) (Iso.refl X)).symm := by
  have hAdjacentInvolutive (j : ℕ) :
      adjacentSwapIso X j ≪≫ adjacentSwapIso X j = Iso.refl _ := by
    let s (A : C) : ((A ⊗ X) ⊗ X) ≅ ((A ⊗ X) ⊗ X) :=
      (α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫ (α_ A X X).symm
    have hs (A : C) : s A ≪≫ s A = Iso.refl _ := by
      apply Iso.ext
      simp only [s, Iso.trans_assoc, Iso.symm_self_id_assoc,
        Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
        Iso.refl_hom]
      rw [← Category.assoc (A ◁ (β_ X X).hom)
          (A ◁ (β_ X X).hom) (α_ A X X).inv,
        ← whiskerLeft_comp, SymmetricCategory.symmetry]
      simp only [whiskerLeft_id, Category.id_comp, Iso.hom_inv_id]
    have hadj : adjacentSwapIso X j = s (tensorPowObj X j) := rfl
    rw [hadj]
    exact hs _
  have hAdjacentSelfSymm (j : ℕ) :
      (adjacentSwapIso X j).symm = adjacentSwapIso X j := by
    apply Iso.ext
    have h := congrArg Iso.hom (hAdjacentInvolutive j)
    simp only [Iso.trans_hom, Iso.refl_hom] at h
    exact ((Iso.hom_comp_eq_id (adjacentSwapIso X j)).mp h).symm
  have hPrefixYangBaxter (A : C) :
      (tensorIso
            ((α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫
              (α_ A X X).symm) (Iso.refl X) ≪≫
          ((α_ (A ⊗ X) X X) ≪≫
            whiskerLeftIso (A ⊗ X) (β_ X X) ≪≫
              (α_ (A ⊗ X) X X).symm)) ≪≫
        tensorIso
          ((α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫
            (α_ A X X).symm) (Iso.refl X) =
      (((α_ (A ⊗ X) X X) ≪≫
            whiskerLeftIso (A ⊗ X) (β_ X X) ≪≫
              (α_ (A ⊗ X) X X).symm) ≪≫
          tensorIso
            ((α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫
              (α_ A X X).symm) (Iso.refl X)) ≪≫
        ((α_ (A ⊗ X) X X) ≪≫
          whiskerLeftIso (A ⊗ X) (β_ X X) ≪≫
            (α_ (A ⊗ X) X X).symm) := by
    let s (D : C) : ((D ⊗ X) ⊗ X) ≅ ((D ⊗ X) ⊗ X) :=
      (α_ D X X) ≪≫ whiskerLeftIso D (β_ X X) ≪≫ (α_ D X X).symm
    let b1 : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X) :=
      (α_ X X X).symm ≪≫ whiskerRightIso (β_ X X) X ≪≫ α_ X X X
    let b2 : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X) :=
      whiskerLeftIso X (β_ X X)
    let qIso (D : C) : (((D ⊗ X) ⊗ X) ⊗ X) ≅
        D ⊗ (X ⊗ (X ⊗ X)) :=
      (α_ (D ⊗ X) X X) ≪≫ α_ D X (X ⊗ X)
    let Q (D : C) (t : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X)) :
        (((D ⊗ X) ⊗ X) ⊗ X) ≅ (((D ⊗ X) ⊗ X) ⊗ X) :=
      qIso D ≪≫ whiskerLeftIso D t ≪≫ (qIso D).symm
    have hQb2 (D : C) : Q D b2 = s (D ⊗ X) := by
      apply Iso.ext
      simp only [Q, qIso, b2, Iso.trans_symm, Iso.trans_assoc,
        Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, s,
        tensor_whiskerLeft, Category.assoc]
    have hQb1 (D : C) : Q D b1 = tensorIso (s D) (Iso.refl X) := by
      apply Iso.ext
      simp only [Q, qIso, b1, whiskerLeftIso_trans, Iso.trans_symm,
        Iso.trans_assoc, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
        whiskerRightIso_hom, pentagon_hom_inv_inv_inv_inv,
        pentagon_hom_hom_inv_hom_hom_assoc, s, tensorIso_hom,
        Iso.refl_hom, tensorHom_id, comp_whiskerRight, whisker_assoc,
        Category.assoc]
    have hQtrans (D : C) (t u : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X)) :
        Q D (t ≪≫ u) = Q D t ≪≫ Q D u := by
      apply Iso.ext
      simp only [Q, qIso, whiskerLeftIso_trans, Iso.trans_symm,
        Iso.trans_assoc, Iso.trans_hom, whiskerLeftIso_hom,
        Iso.symm_hom, Iso.symm_self_id_assoc]
    have hCore : (b1 ≪≫ b2) ≪≫ b1 = (b2 ≪≫ b1) ≪≫ b2 := by
      simpa only [b1, b2, Iso.trans_assoc] using
        BraidedCategory.yang_baxter_iso X X X
    have h :
        (tensorIso (s A) (Iso.refl X) ≪≫ s (A ⊗ X)) ≪≫
            tensorIso (s A) (Iso.refl X) =
          (s (A ⊗ X) ≪≫ tensorIso (s A) (Iso.refl X)) ≪≫
            s (A ⊗ X) := by
      calc
        (tensorIso (s A) (Iso.refl X) ≪≫ s (A ⊗ X)) ≪≫
              tensorIso (s A) (Iso.refl X) =
            (Q A b1 ≪≫ Q A b2) ≪≫ Q A b1 := by rw [hQb1, hQb2]
        _ = Q A (b1 ≪≫ b2) ≪≫ Q A b1 := by rw [hQtrans]
        _ = Q A ((b1 ≪≫ b2) ≪≫ b1) := by
          rw [hQtrans A (b1 ≪≫ b2) b1, hQtrans A b1 b2]
        _ = Q A ((b2 ≪≫ b1) ≪≫ b2) := by rw [hCore]
        _ = Q A (b2 ≪≫ b1) ≪≫ Q A b2 := by rw [hQtrans]
        _ = (Q A b2 ≪≫ Q A b1) ≪≫ Q A b2 := by
          rw [hQtrans A b2 b1]
        _ = (s (A ⊗ X) ≪≫ tensorIso (s A) (Iso.refl X)) ≪≫
            s (A ⊗ X) := by rw [hQb1, hQb2]
    simpa only [s] using h
  have hAdjacentCommDoubleLift (A : C) (f : A ≅ A) :
      ((α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫
          (α_ A X X).symm) ≪≫
          tensorIso (tensorIso f (Iso.refl X)) (Iso.refl X) =
        tensorIso (tensorIso f (Iso.refl X)) (Iso.refl X) ≪≫
          ((α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫
            (α_ A X X).symm) := by
    let s (D : C) : ((D ⊗ X) ⊗ X) ≅ ((D ⊗ X) ⊗ X) :=
      (α_ D X X) ≪≫ whiskerLeftIso D (β_ X X) ≪≫ (α_ D X X).symm
    have h : s A ≪≫ tensorIso (tensorIso f (Iso.refl X)) (Iso.refl X) =
        tensorIso (tensorIso f (Iso.refl X)) (Iso.refl X) ≪≫ s A := by
      apply Iso.ext
      simp only [s, Iso.trans_assoc, Iso.trans_hom, whiskerLeftIso_hom,
        Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id]
      rw [← associator_inv_naturality_left f.hom X X]
      rw [whisker_exchange_assoc f.hom (β_ X X).hom]
      rw [← associator_naturality_left_assoc f.hom X X]
    simpa only [s] using h
  have hConjugateBraid {Y : C} (a b d : Y ≅ Y)
      (hab : (b ≪≫ a) ≪≫ b = (a ≪≫ b) ≪≫ a)
      (had : a ≪≫ d = d ≪≫ a) :
      (a ≪≫ ((d ≪≫ b) ≪≫ d.symm)) ≪≫ a =
        (((d ≪≫ b) ≪≫ d.symm) ≪≫ a) ≪≫
          ((d ≪≫ b) ≪≫ d.symm) := by
    have hadSymm : d.symm ≪≫ a = a ≪≫ d.symm := by
      have h := congrArg (fun z => (d.symm ≪≫ z) ≪≫ d.symm) had
      simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc,
        Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.refl_trans,
        Iso.trans_refl] using h
    have hadAssoc (z : Y ≅ Y) : a ≪≫ d ≪≫ z = d ≪≫ a ≪≫ z := by
      rw [← Iso.trans_assoc, had, Iso.trans_assoc]
    have hadSymmAssoc (z : Y ≅ Y) :
        d.symm ≪≫ a ≪≫ z = a ≪≫ d.symm ≪≫ z := by
      rw [← Iso.trans_assoc, hadSymm, Iso.trans_assoc]
    have hconjAssoc (z : Y ≅ Y) :
        d.symm ≪≫ a ≪≫ d ≪≫ z = a ≪≫ z := by
      rw [hadSymmAssoc, ← Iso.trans_assoc d.symm d z,
        Iso.symm_self_id, Iso.refl_trans]
    have hLeft :
        (a ≪≫ ((d ≪≫ b) ≪≫ d.symm)) ≪≫ a =
          d ≪≫ b ≪≫ a ≪≫ b ≪≫ d.symm := by
      calc
        (a ≪≫ ((d ≪≫ b) ≪≫ d.symm)) ≪≫ a =
            d ≪≫ a ≪≫ b ≪≫ d.symm ≪≫ a := by
          simpa only [Iso.trans_assoc] using hadAssoc (b ≪≫ d.symm ≪≫ a)
        _ = d ≪≫ a ≪≫ b ≪≫ a ≪≫ d.symm := by
          have h := congrArg (fun z => d ≪≫ a ≪≫ b ≪≫ z) hadSymm
          simpa only [Iso.trans_assoc] using h
        _ = d ≪≫ b ≪≫ a ≪≫ b ≪≫ d.symm := by
          have h := congrArg (fun z => d ≪≫ z ≪≫ d.symm) hab.symm
          simpa only [Iso.trans_assoc] using h
    have hRight :
        (((d ≪≫ b) ≪≫ d.symm) ≪≫ a) ≪≫
            ((d ≪≫ b) ≪≫ d.symm) =
          d ≪≫ b ≪≫ a ≪≫ b ≪≫ d.symm := by
      have h := congrArg
        (fun z => d ≪≫ b ≪≫ z ≪≫ b ≪≫ d.symm)
        (hconjAssoc (Iso.refl Y))
      simpa only [Iso.trans_assoc, Iso.trans_refl] using h
    exact hLeft.trans hRight.symm
  have hConjugateInvolutive {Y : C} (a d : Y ≅ Y)
      (ha : a ≪≫ a = Iso.refl _) :
      ((d ≪≫ a) ≪≫ d.symm) ≪≫ ((d ≪≫ a) ≪≫ d.symm) =
        Iso.refl _ := by
    have h := congrArg (fun z => (d ≪≫ z) ≪≫ d.symm) ha
    calc
      ((d ≪≫ a) ≪≫ d.symm) ≪≫ ((d ≪≫ a) ≪≫ d.symm) =
          (d ≪≫ (a ≪≫ a)) ≪≫ d.symm := by
        simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
      _ = Iso.refl _ := by
        simpa only [Iso.trans_assoc, Iso.refl_trans, Iso.trans_refl,
          Iso.self_symm_id] using h
  have hLiftInvolutive {A : C} (f : A ≅ A)
      (hf : f ≪≫ f = Iso.refl _) :
      tensorIso f (Iso.refl X) ≪≫ tensorIso f (Iso.refl X) =
        Iso.refl _ := by
    apply Iso.ext
    change (f.hom ⊗ₘ 𝟙 X) ≫ (f.hom ⊗ₘ 𝟙 X) = 𝟙 _
    rw [tensorHom_comp_tensorHom]
    have h := congrArg Iso.hom hf
    simp only [Iso.trans_hom, Iso.refl_hom] at h
    rw [h, Category.comp_id]
    exact id_tensorHom_id _ _
  have hSelfSymm {A : C} (f : A ≅ A)
      (hf : f ≪≫ f = Iso.refl _) : f.symm = f := by
    apply Iso.ext
    have h := congrArg Iso.hom hf
    simp only [Iso.trans_hom, Iso.refl_hom] at h
    exact ((Iso.hom_comp_eq_id f).mp h).symm
  have hCycleZero (n : ℕ) :
      oneWayCycleIso X n (0 : Fin (n + 1)) = Iso.refl _ := by
    cases n <;> rfl
  have hCycleSucc (n : ℕ) (r : Fin (n + 1)) :
      oneWayCycleIso X (n + 1) r.succ = adjacentSwapIso X n ≪≫
        tensorIso (oneWayCycleIso X n r) (Iso.refl X) := by
    rfl
  have hMoveZero (n : ℕ) :
      moveZeroIso X (n + 1) (0 : Fin (n + 1)) = Iso.refl _ := by
    rfl
  have hMoveSuccDef (n : ℕ) (r : Fin n) :
      moveZeroIso X (n + 1) r.succ =
        oneWayCycleIso X n r.succ ≪≫
          (oneWayCycleIso X n r.castSucc).symm := by
    rfl
  have hLeftRecursion (j : ℕ) (t : Fin (j + 1)) :
      moveZeroIso X ((j + 1) + 2) t.succ.succ =
        (adjacentSwapIso X (j + 1) ≪≫
            tensorIso (moveZeroIso X ((j + 1) + 1) t.succ)
              (Iso.refl X)) ≪≫
          adjacentSwapIso X (j + 1) := by
    let S : (tensorPowObj X ((j + 1) + 1) ⊗ X) ≅
        (tensorPowObj X ((j + 1) + 1) ⊗ X) :=
      adjacentSwapIso X (j + 1)
    let Fs := oneWayCycleIso X (j + 1) t.succ
    let F0 := oneWayCycleIso X (j + 1) t.castSucc
    let LS := tensorIso Fs (Iso.refl X)
    let L0 := tensorIso F0 (Iso.refl X)
    let M := moveZeroIso X ((j + 1) + 1) t.succ
    let LM := tensorIso M (Iso.refl X)
    have hcast : Fin.castSucc t.succ = (Fin.castSucc t).succ := by rfl
    have hFs : oneWayCycleIso X ((j + 1) + 1) t.succ.succ =
        S ≪≫ LS := by
      apply Iso.ext
      exact congrArg Iso.hom (hCycleSucc (j + 1) t.succ)
    have hF0 : oneWayCycleIso X ((j + 1) + 1)
        (Fin.castSucc t.succ) = S ≪≫ L0 := by
      rw [hcast]
      apply Iso.ext
      exact congrArg Iso.hom (hCycleSucc (j + 1) t.castSucc)
    have hM : M = Fs ≪≫ F0.symm := by
      simpa only [M, Fs, F0] using hMoveSuccDef (j + 1) t
    have hLift : LM = LS ≪≫ L0.symm := by
      apply Iso.ext
      dsimp only [LM, LS, L0]
      rw [hM]
      change (((Fs.hom ≫ F0.inv) ⊗ₘ 𝟙 X)) =
        (Fs.hom ⊗ₘ 𝟙 X) ≫ (F0.inv ⊗ₘ 𝟙 X)
      simpa only [Category.comp_id] using
        (tensorHom_comp_tensorHom Fs.hom (𝟙 X) F0.inv (𝟙 X)).symm
    rw [hMoveSuccDef, hFs, hF0]
    change (S ≪≫ LS) ≪≫ (S ≪≫ L0).symm = (S ≪≫ LM) ≪≫ S
    apply Iso.ext
    have hS := congrArg Iso.hom (hAdjacentSelfSymm (j + 1))
    change S.inv = S.hom at hS
    have hL := congrArg Iso.hom hLift
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom] at hL ⊢
    rw [hS, hL]
    simp only [Category.assoc]
  have hMoveOne (j : ℕ) :
      moveZeroIso X (j + 2) (0 : Fin (j + 1)).succ =
        adjacentSwapIso X j := by
    rw [hMoveSuccDef, hCycleSucc, hCycleZero]
    have hzero : Fin.castSucc (0 : Fin (j + 1)) =
        (0 : Fin (j + 2)) := by rfl
    rw [hzero, hCycleZero]
    let rIso := tensorIso (Iso.refl (tensorPowObj X (j + 1)))
      (Iso.refl X)
    have hr : rIso = Iso.refl _ := by
      apply Iso.ext
      exact id_tensorHom_id _ _
    let S : (tensorPowObj X (j + 1) ⊗ X) ≅
        (tensorPowObj X (j + 1) ⊗ X) := adjacentSwapIso X j
    change (S ≪≫ rIso) ≪≫ (Iso.refl _).symm = S
    apply Iso.ext
    have hrh := congrArg Iso.hom hr
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_inv]
    rw [hrh]
    simp only [Iso.refl_hom, Category.comp_id]
  have hSuccZero (j : ℕ) :
      moveZeroIso X (j + 2) (0 : Fin (j + 1)).succ =
        (tensorIso (moveZeroIso X (j + 1) (0 : Fin (j + 1)))
            (Iso.refl X) ≪≫ adjacentSwapIso X j) ≪≫
          (tensorIso (moveZeroIso X (j + 1) (0 : Fin (j + 1)))
            (Iso.refl X)).symm := by
    rw [hMoveOne, hMoveZero]
    let L := tensorIso (Iso.refl (tensorPowObj X (j + 1)))
      (Iso.refl X)
    have hL : L = Iso.refl _ := by
      apply Iso.ext
      exact id_tensorHom_id _ _
    let S : (tensorPowObj X (j + 1) ⊗ X) ≅
        (tensorPowObj X (j + 1) ⊗ X) := adjacentSwapIso X j
    change S = (L ≪≫ S) ≪≫ L.symm
    rw [hL, Iso.refl_trans, Iso.refl_symm, Iso.trans_refl]
  let I : ℕ → Prop := fun n => ∀ i : Fin (n + 1),
    moveZeroIso X (n + 1) i ≪≫ moveZeroIso X (n + 1) i =
      Iso.refl _
  let R : ℕ → Prop := fun n => ∀ r : Fin (n + 1),
    moveZeroIso X (n + 2) r.succ =
      (tensorIso (moveZeroIso X (n + 1) r) (Iso.refl X) ≪≫
          adjacentSwapIso X n) ≪≫
        (tensorIso (moveZeroIso X (n + 1) r) (Iso.refl X)).symm
  have hIR : ∀ n, I n ∧ R n := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_⟩
        · intro i
          have hi : i = 0 := Fin.eq_zero i
          subst i
          change Iso.refl _ ≪≫ Iso.refl _ = Iso.refl _
          exact Iso.refl_trans _
        · intro r
          have hr : r = 0 := Fin.eq_zero r
          subst r
          exact hSuccZero 0
    | succ n ih =>
        rcases ih with ⟨_hI, hR⟩
        have hIsucc : I (n + 1) := by
          intro i
          refine Fin.cases ?_ (fun r => ?_) i
          · change Iso.refl _ ≪≫ Iso.refl _ = Iso.refl _
            exact Iso.refl_trans _
          · rw [hR r]
            exact hConjugateInvolutive (adjacentSwapIso X n)
              (tensorIso (moveZeroIso X (n + 1) r) (Iso.refl X))
              (hAdjacentInvolutive n)
        refine ⟨hIsucc, ?_⟩
        intro r
        refine Fin.cases (hSuccZero (n + 1)) (fun t => ?_) r
        let A := tensorPowObj X n
        let low : ((A ⊗ X) ⊗ X) ≅ ((A ⊗ X) ⊗ X) :=
          adjacentSwapIso X n
        let adj : (((A ⊗ X) ⊗ X) ⊗ X) ≅
            (((A ⊗ X) ⊗ X) ⊗ X) := adjacentSwapIso X (n + 1)
        let inner : ((A ⊗ X) ⊗ X) ≅ ((A ⊗ X) ⊗ X) :=
          tensorIso (moveZeroIso X (n + 1) t) (Iso.refl X)
        let LM : (((A ⊗ X) ⊗ X) ⊗ X) ≅
            (((A ⊗ X) ⊗ X) ⊗ X) :=
          tensorIso (moveZeroIso X ((n + 1) + 1) t.succ) (Iso.refl X)
        let lift3 (z : ((A ⊗ X) ⊗ X) ≅ ((A ⊗ X) ⊗ X)) :
            (((A ⊗ X) ⊗ X) ⊗ X) ≅ (((A ⊗ X) ⊗ X) ⊗ X) :=
          tensorIso z (Iso.refl X)
        let d := lift3 inner
        let lowerAdj := lift3 low
        have hLower : moveZeroIso X ((n + 1) + 1) t.succ =
            (inner ≪≫ low) ≪≫ inner.symm := by
          apply Iso.ext
          exact congrArg Iso.hom (hR t)
        have hLM : LM = (d ≪≫ lowerAdj) ≪≫ d.symm := by
          calc
            LM = lift3 (moveZeroIso X (n + 2) t.succ) := rfl
            _ = lift3 ((inner ≪≫ low) ≪≫ inner.symm) := by rw [hLower]
            _ = (d ≪≫ lowerAdj) ≪≫ d.symm := by
              apply Iso.ext
              change
                ((((inner.hom ≫ low.hom) ≫ inner.inv) ⊗ₘ 𝟙 X)) =
                  (((inner.hom ⊗ₘ 𝟙 X) ≫ (low.hom ⊗ₘ 𝟙 X)) ≫
                    (inner.inv ⊗ₘ 𝟙 X))
              rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
              simp only [Category.comp_id]
        have hBase : (lowerAdj ≪≫ adj) ≪≫ lowerAdj =
            (adj ≪≫ lowerAdj) ≪≫ adj := by
          have h := hPrefixYangBaxter A
          change (lowerAdj ≪≫ adj) ≪≫ lowerAdj =
            (adj ≪≫ lowerAdj) ≪≫ adj at h
          exact h
        have hComm : adj ≪≫ d = d ≪≫ adj := by
          have h := hAdjacentCommDoubleLift (tensorPowObj X (n + 1))
            (moveZeroIso X (n + 1) t)
          change adj ≪≫ d = d ≪≫ adj at h
          exact h
        have hBraid : (adj ≪≫ LM) ≪≫ adj =
            (LM ≪≫ adj) ≪≫ LM := by
          rw [hLM]
          exact hConjugateBraid adj lowerAdj d hBase hComm
        have hLeft : moveZeroIso X ((n + 1) + 2) t.succ.succ =
            (adj ≪≫ LM) ≪≫ adj := by
          apply Iso.ext
          exact congrArg Iso.hom (hLeftRecursion n t)
        have hLMInv : LM ≪≫ LM = Iso.refl _ :=
          hLiftInvolutive (moveZeroIso X ((n + 1) + 1) t.succ)
            (hIsucc t.succ)
        have hLMSymm : LM.symm = LM := hSelfSymm LM hLMInv
        have hFinal : (adj ≪≫ LM) ≪≫ adj =
            (LM ≪≫ adj) ≪≫ LM.symm :=
          hBraid.trans
            (congrArg (fun z => (LM ≪≫ adj) ≪≫ z) hLMSymm.symm)
        exact hLeft.trans hFinal
  exact (hIR k).2 q

/-- Internal right-to-left permutation action, recursively normalized by
`Equiv.Perm.decomposeFin`. -/
private noncomputable def permutationIsoAux (X : C) :
    (n : ℕ) → Equiv.Perm (Fin n) →
      (tensorPowObj X n ≅ tensorPowObj X n)
  | 0, _ => Iso.refl _
  | k + 1, σ =>
      let d := Equiv.Perm.decomposeFin σ
      tensorIso (permutationIsoAux X k d.2) (Iso.refl X) ≪≫
        moveZeroIso X (k + 1) d.1

/-- The internal action sends the identity permutation to the identity iso. -/
private theorem permutationIsoAux_refl (X : C) (n : ℕ) :
    permutationIsoAux X n (Equiv.refl (Fin n)) = Iso.refl _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hdec :
          Equiv.Perm.decomposeFin (Equiv.refl (Fin (n + 1))) =
            (0, Equiv.refl (Fin n)) := by
        apply Equiv.Perm.decomposeFin.symm.injective
        simp
      rw [permutationIsoAux, hdec, ih]
      cases n <;> apply Iso.ext <;>
        simp only [Nat.reduceAdd, tensorPowObj_succ, tensorPowObj_zero,
          moveZeroIso, Iso.trans_refl, tensorIso_hom, Iso.refl_hom,
          tensorHom_id, id_whiskerRight, Fin.cases_zero]

/-- The internal permutation action respects composition. -/
private theorem permutationIsoAux_trans (X : C) (n : ℕ)
    (σ τ : Equiv.Perm (Fin n)) :
    permutationIsoAux X n (σ.trans τ) =
      permutationIsoAux X n σ ≪≫ permutationIsoAux X n τ := by
  let T : (k : ℕ) → Prop := fun k =>
    ∀ a b : Equiv.Perm (Fin k),
      permutationIsoAux X k (a.trans b) =
        permutationIsoAux X k a ≪≫ permutationIsoAux X k b
  let N : (k : ℕ) → Prop := fun k =>
    ∀ (p : Fin (k + 1)) (f : Equiv.Perm (Fin k)),
      moveZeroIso X (k + 1) p ≪≫
          tensorIso (permutationIsoAux X k f) (Iso.refl X) =
        tensorIso (permutationIsoAux X k f) (Iso.refl X) ≪≫
          moveZeroIso X (k + 1)
            (Fin.cases 0 (fun i => (f i).succ) p)
  let S : (k : ℕ) → Prop := fun k =>
    ∀ p q : Fin (k + 1),
      let d := Equiv.Perm.decomposeFin
        ((Equiv.swap 0 p).trans (Equiv.swap 0 q))
      moveZeroIso X (k + 1) p ≪≫ moveZeroIso X (k + 1) q =
        tensorIso (permutationIsoAux X k d.2) (Iso.refl X) ≪≫
          moveZeroIso X (k + 1) d.1
  have hTNS : ∀ k, T k ∧ N k ∧ S k := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro a b
          have ha : a = Equiv.refl (Fin 0) := Subsingleton.elim _ _
          have hb : b = Equiv.refl (Fin 0) := Subsingleton.elim _ _
          subst a
          subst b
          apply Iso.ext
          simp only [tensorPowObj_zero, permutationIsoAux,
            Iso.refl_hom, Iso.trans_refl]
        · intro p f
          have hp : p = 0 := Fin.eq_zero p
          have hf : f = Equiv.refl (Fin 0) := Subsingleton.elim _ _
          subst p
          subst f
          let out : Fin 1 := Fin.cases 0
            (fun i => ((Equiv.refl (Fin 0)) i).succ) 0
          let M : tensorPowObj X 1 ≅ tensorPowObj X 1 :=
            moveZeroIso X 1 0
          let M' : tensorPowObj X 1 ≅ tensorPowObj X 1 :=
            moveZeroIso X 1 out
          let L : tensorPowObj X 1 ≅ tensorPowObj X 1 :=
            tensorIso (permutationIsoAux X 0 (Equiv.refl (Fin 0)))
              (Iso.refl X)
          change M ≪≫ L = L ≪≫ M'
          have hM : M = Iso.refl _ := rfl
          have hM' : M' = Iso.refl _ := by
            have hout : out = 0 := Fin.eq_zero out
            dsimp only [M']
            rw [hout]
            rfl
          have hL : L = Iso.refl _ := by
            dsimp only [L]
            rw [permutationIsoAux_refl]
            apply Iso.ext
            exact id_tensorHom_id _ _
          rw [hM, hM', hL]
        · intro p q
          have hp : p = 0 := Fin.eq_zero p
          have hq : q = 0 := Fin.eq_zero q
          subst p
          subst q
          have hd : Equiv.Perm.decomposeFin
              ((Equiv.swap 0 (0 : Fin 1)).trans (Equiv.swap 0 0)) =
                (0, Equiv.refl (Fin 0)) := by
            apply Equiv.Perm.decomposeFin.symm.injective
            simp
          rw [hd]
          let M : tensorPowObj X 1 ≅ tensorPowObj X 1 :=
            moveZeroIso X 1 0
          let L : tensorPowObj X 1 ≅ tensorPowObj X 1 :=
            tensorIso (permutationIsoAux X 0 (Equiv.refl (Fin 0)))
              (Iso.refl X)
          change M ≪≫ M = L ≪≫ M
          have hM : M = Iso.refl _ := rfl
          have hL : L = Iso.refl _ := by
            dsimp only [L]
            rw [permutationIsoAux_refl]
            apply Iso.ext
            exact id_tensorHom_id _ _
          rw [hM, hL]
    | succ k ih =>
        rcases ih with ⟨hT, hN, hS⟩
        let liftPerm (e : Equiv.Perm (Fin k)) :
            Equiv.Perm (Fin (k + 1)) :=
          Equiv.Perm.decomposeFin.symm (0, e)
        let liftPoint (e : Equiv.Perm (Fin k)) :
            Fin (k + 1) → Fin (k + 1) :=
          Fin.cases 0 (fun i => (e i).succ)
        let starDec (p q : Fin (k + 1)) :
            Fin (k + 1) × Equiv.Perm (Fin k) :=
          Equiv.Perm.decomposeFin
            ((Equiv.swap 0 p).trans (Equiv.swap 0 q))
        have hD (p : Fin (k + 1)) (e : Equiv.Perm (Fin k)) :
            Equiv.Perm.decomposeFin.symm (p, e) =
              (liftPerm e).trans (Equiv.swap 0 p) := by
          apply Equiv.ext
          intro x
          refine Fin.cases ?_ (fun i => ?_) x <;>
            simp [liftPerm, Equiv.swap_apply_def]
        have hLiftPoint (e : Equiv.Perm (Fin k))
            (p : Fin (k + 1)) : liftPerm e p = liftPoint e p := by
          refine Fin.cases ?_ (fun i => ?_) p <;>
            simp [liftPerm, liftPoint]
        have hConj (p : Fin (k + 1)) (e : Equiv.Perm (Fin k)) :
            (Equiv.swap 0 p).trans (liftPerm e) =
              (liftPerm e).trans
                (Equiv.swap 0 (liftPoint e p)) := by
          apply Equiv.ext
          intro x
          rw [← hLiftPoint]
          simpa [liftPerm] using
            Function.Injective.map_swap (liftPerm e).injective 0 p x
        have hLift (e f : Equiv.Perm (Fin k)) :
            (liftPerm e).trans (liftPerm f) =
              liftPerm (e.trans f) := by
          apply Equiv.ext
          intro x
          refine Fin.cases ?_ (fun i => ?_) x <;> simp [liftPerm]
        have hStarZeroLeft (q : Fin (k + 1)) :
            starDec 0 q = (q, Equiv.refl (Fin k)) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          simp [starDec]
        have hStarZeroRight (p : Fin (k + 1)) :
            starDec p 0 = (p, Equiv.refl (Fin k)) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          simp [starDec]
        have hStarSame (p : Fin (k + 1)) :
            starDec p p = (0, Equiv.refl (Fin k)) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          simp [starDec]
        have hStarDistinct (r t : Fin k) (hrt : r ≠ t) :
            starDec r.succ t.succ = (r.succ, Equiv.swap r t) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          ext x
          refine Fin.cases ?_ (fun i => ?_) x
          · simp [starDec, Equiv.swap_apply_def, hrt]
          · by_cases hir : i = r
            · subst i
              simp [starDec, Equiv.swap_apply_def, Ne.symm hrt]
            · by_cases hit : i = t
              · subst i
                simp [starDec, Equiv.swap_apply_def, Ne.symm hrt]
              · simp [starDec, Equiv.swap_apply_def, hir, hit]
        have hProduct (a b : Equiv.Perm (Fin (k + 1))) :
            let da := Equiv.Perm.decomposeFin a
            let db := Equiv.Perm.decomposeFin b
            let p' := liftPoint db.2 da.1
            let c := starDec p' db.1
            Equiv.Perm.decomposeFin (a.trans b) =
              (c.1, (da.2.trans db.2).trans c.2) := by
          dsimp only
          let da := Equiv.Perm.decomposeFin a
          let db := Equiv.Perm.decomposeFin b
          let p' := liftPoint db.2 da.1
          let c := starDec p' db.1
          have ha : Equiv.Perm.decomposeFin.symm da = a := by
            exact Equiv.symm_apply_apply _ _
          have hb : Equiv.Perm.decomposeFin.symm db = b := by
            exact Equiv.symm_apply_apply _ _
          have hc : Equiv.Perm.decomposeFin.symm c =
              (Equiv.swap 0 p').trans (Equiv.swap 0 db.1) := by
            exact Equiv.symm_apply_apply _ _
          apply Equiv.Perm.decomposeFin.symm.injective
          rw [Equiv.symm_apply_apply]
          calc
            a.trans b =
                (Equiv.Perm.decomposeFin.symm da).trans
                  (Equiv.Perm.decomposeFin.symm db) := by rw [ha, hb]
            _ = ((liftPerm da.2).trans
                  (Equiv.swap 0 da.1)).trans
                ((liftPerm db.2).trans
                  (Equiv.swap 0 db.1)) := by rw [hD, hD]
            _ = (liftPerm da.2).trans
                (((Equiv.swap 0 da.1).trans
                  (liftPerm db.2)).trans
                  (Equiv.swap 0 db.1)) := by rfl
            _ = (liftPerm da.2).trans
                (((liftPerm db.2).trans
                  (Equiv.swap 0 p')).trans
                  (Equiv.swap 0 db.1)) := by rw [hConj]
            _ = (liftPerm (da.2.trans db.2)).trans
                ((Equiv.swap 0 p').trans
                  (Equiv.swap 0 db.1)) := by
              rw [Equiv.trans_assoc (liftPerm db.2)
                (Equiv.swap 0 p') (Equiv.swap 0 db.1)]
              rw [← Equiv.trans_assoc (liftPerm da.2)
                (liftPerm db.2)
                ((Equiv.swap 0 p').trans
                  (Equiv.swap 0 db.1)), hLift]
            _ = (liftPerm (da.2.trans db.2)).trans
                (Equiv.Perm.decomposeFin.symm c) := by rw [hc]
            _ = (liftPerm (da.2.trans db.2)).trans
                ((liftPerm c.2).trans
                  (Equiv.swap 0 c.1)) := by rw [hD]
            _ = (liftPerm
                  ((da.2.trans db.2).trans c.2)).trans
                (Equiv.swap 0 c.1) := by
              rw [← Equiv.trans_assoc, hLift]
            _ = Equiv.Perm.decomposeFin.symm
                (c.1, (da.2.trans db.2).trans c.2) := by rw [hD]
        let L (e : Equiv.Perm (Fin k)) :
            tensorPowObj X (k + 1) ≅ tensorPowObj X (k + 1) :=
          tensorIso (permutationIsoAux X k e) (Iso.refl X)
        have hTensorTrans (e f : Equiv.Perm (Fin k)) :
            L e ≪≫ L f = L (e.trans f) := by
          dsimp only [L]
          rw [hT e f]
          apply Iso.ext
          change
            ((permutationIsoAux X k e).hom ⊗ₘ 𝟙 X) ≫
                ((permutationIsoAux X k f).hom ⊗ₘ 𝟙 X) =
              (((permutationIsoAux X k e).hom ≫
                (permutationIsoAux X k f).hom) ⊗ₘ 𝟙 X)
          simpa only [Category.comp_id] using
            tensorHom_comp_tensorHom
              (permutationIsoAux X k e).hom (𝟙 X)
              (permutationIsoAux X k f).hom (𝟙 X)
        have hLrefl : L (Equiv.refl (Fin k)) = Iso.refl _ := by
          dsimp only [L]
          rw [permutationIsoAux_refl]
          apply Iso.ext
          exact id_tensorHom_id _ _
        have hMzero :
            moveZeroIso X (k + 1) (0 : Fin (k + 1)) = Iso.refl _ := by
          cases k <;> apply Iso.ext <;>
            simp only [Nat.reduceAdd, tensorPowObj_succ,
              tensorPowObj_zero, moveZeroIso, Iso.refl_hom,
              Fin.cases_zero]
        have hMInvolutive (p : Fin (k + 1)) :
            moveZeroIso X (k + 1) p ≪≫
                moveZeroIso X (k + 1) p = Iso.refl _ := by
          have hp := hS p p
          change moveZeroIso X (k + 1) p ≪≫
                moveZeroIso X (k + 1) p =
              L (starDec p p).2 ≪≫
                moveZeroIso X (k + 1) (starDec p p).1 at hp
          rw [hStarSame] at hp
          change moveZeroIso X (k + 1) p ≪≫
                moveZeroIso X (k + 1) p =
              L (Equiv.refl (Fin k)) ≪≫
                moveZeroIso X (k + 1) 0 at hp
          have hLrefl : L (Equiv.refl (Fin k)) = Iso.refl _ := by
            dsimp only [L]
            rw [permutationIsoAux_refl]
            apply Iso.ext
            simp only [tensorIso_hom, Iso.refl_hom, tensorHom_id,
              id_whiskerRight, tensorPowObj_succ]
          rw [hLrefl, hMzero] at hp
          simpa only [Iso.refl_trans] using hp
        let LM (p : Fin (k + 1)) :
            tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2) :=
          tensorIso (moveZeroIso X (k + 1) p) (Iso.refl X)
        have hLMInvolutive (p : Fin (k + 1)) :
            LM p ≪≫ LM p = Iso.refl _ := by
          apply Iso.ext
          change
            ((moveZeroIso X (k + 1) p).hom ⊗ₘ 𝟙 X) ≫
                ((moveZeroIso X (k + 1) p).hom ⊗ₘ 𝟙 X) = 𝟙 _
          rw [tensorHom_comp_tensorHom]
          have hp := congrArg Iso.hom (hMInvolutive p)
          simp only [Iso.trans_hom, Iso.refl_hom] at hp
          rw [hp]
          rw [Category.comp_id]
          exact id_tensorHom_id (tensorPowObj X (k + 1)) X
        have hLMSymm (p : Fin (k + 1)) : (LM p).symm = LM p := by
          apply Iso.ext
          have hp := congrArg Iso.hom (hLMInvolutive p)
          simp only [Iso.trans_hom, Iso.refl_hom] at hp
          exact ((Iso.hom_comp_eq_id (LM p)).mp hp).symm
        let s (A : C) : ((A ⊗ X) ⊗ X) ≅ ((A ⊗ X) ⊗ X) :=
          (α_ A X X) ≪≫ whiskerLeftIso A (β_ X X) ≪≫
            (α_ A X X).symm
        let b1 : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X) :=
          (α_ X X X).symm ≪≫ whiskerRightIso (β_ X X) X ≪≫
            α_ X X X
        let b2 : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X) :=
          whiskerLeftIso X (β_ X X)
        let qIso (A : C) :
            (((A ⊗ X) ⊗ X) ⊗ X) ≅ A ⊗ (X ⊗ (X ⊗ X)) :=
          (α_ (A ⊗ X) X X) ≪≫ (α_ A X (X ⊗ X))
        let Q (A : C)
            (t : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X)) :
            (((A ⊗ X) ⊗ X) ⊗ X) ≅
              (((A ⊗ X) ⊗ X) ⊗ X) :=
          qIso A ≪≫ whiskerLeftIso A t ≪≫ (qIso A).symm
        have hsInvolutive (A : C) :
            s A ≪≫ s A = Iso.refl _ := by
          apply Iso.ext
          simp only [s, Iso.trans_assoc, Iso.symm_self_id_assoc,
            Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
            Iso.refl_hom]
          rw [← Category.assoc (A ◁ (β_ X X).hom)
              (A ◁ (β_ X X).hom) (α_ A X X).inv,
            ← whiskerLeft_comp, SymmetricCategory.symmetry]
          simp only [whiskerLeft_id, Category.id_comp,
            Iso.hom_inv_id]
        have hQb2 (A : C) : Q A b2 = s (A ⊗ X) := by
          apply Iso.ext
          simp only [Q, qIso, b2, Iso.trans_symm,
            Iso.trans_assoc, Iso.trans_hom, whiskerLeftIso_hom,
            Iso.symm_hom, s, tensor_whiskerLeft, Category.assoc]
        have hQb1 (A : C) :
            Q A b1 = tensorIso (s A) (Iso.refl X) := by
          apply Iso.ext
          simp only [Q, qIso, b1, whiskerLeftIso_trans,
            Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom,
            whiskerLeftIso_hom, Iso.symm_hom,
            whiskerRightIso_hom,
            pentagon_hom_inv_inv_inv_inv,
            pentagon_hom_hom_inv_hom_hom_assoc, s,
            tensorIso_hom, Iso.refl_hom, tensorHom_id,
            comp_whiskerRight, whisker_assoc, Category.assoc]
        have hQtrans (A : C)
            (t u : X ⊗ (X ⊗ X) ≅ X ⊗ (X ⊗ X)) :
            Q A (t ≪≫ u) = Q A t ≪≫ Q A u := by
          apply Iso.ext
          simp only [Q, qIso, whiskerLeftIso_trans,
            Iso.trans_symm, Iso.trans_assoc, Iso.trans_hom,
            whiskerLeftIso_hom, Iso.symm_hom,
            Iso.symm_self_id_assoc]
        have hCoreYB :
            (b1 ≪≫ b2) ≪≫ b1 = (b2 ≪≫ b1) ≪≫ b2 := by
          simpa only [b1, b2, Iso.trans_assoc] using
            BraidedCategory.yang_baxter_iso X X X
        have hPrefixYB (A : C) :
            (tensorIso (s A) (Iso.refl X) ≪≫ s (A ⊗ X)) ≪≫
                tensorIso (s A) (Iso.refl X) =
              (s (A ⊗ X) ≪≫
                tensorIso (s A) (Iso.refl X)) ≪≫ s (A ⊗ X) := by
          calc
            (tensorIso (s A) (Iso.refl X) ≪≫ s (A ⊗ X)) ≪≫
                tensorIso (s A) (Iso.refl X) =
              (Q A b1 ≪≫ Q A b2) ≪≫ Q A b1 := by
                rw [hQb1, hQb2]
            _ = Q A (b1 ≪≫ b2) ≪≫ Q A b1 := by
                rw [hQtrans]
            _ = Q A ((b1 ≪≫ b2) ≪≫ b1) := by
                rw [hQtrans A (b1 ≪≫ b2) b1,
                  hQtrans A b1 b2]
            _ = Q A ((b2 ≪≫ b1) ≪≫ b2) := by rw [hCoreYB]
            _ = Q A (b2 ≪≫ b1) ≪≫ Q A b2 := by
                rw [hQtrans]
            _ = (Q A b2 ≪≫ Q A b1) ≪≫ Q A b2 := by
                rw [hQtrans A b2 b1]
            _ = (s (A ⊗ X) ≪≫
                  tensorIso (s A) (Iso.refl X)) ≪≫
                s (A ⊗ X) := by rw [hQb1, hQb2]
        have hConjugateBraid {Y : C} (a b d : Y ≅ Y)
            (hab : (b ≪≫ a) ≪≫ b = (a ≪≫ b) ≪≫ a)
            (had : a ≪≫ d = d ≪≫ a) :
            (a ≪≫ ((d ≪≫ b) ≪≫ d.symm)) ≪≫ a =
              (((d ≪≫ b) ≪≫ d.symm) ≪≫ a) ≪≫
                ((d ≪≫ b) ≪≫ d.symm) := by
          have hadSymm : d.symm ≪≫ a = a ≪≫ d.symm := by
            have h := congrArg
              (fun z => (d.symm ≪≫ z) ≪≫ d.symm) had
            simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc,
              Iso.self_symm_id_assoc, Iso.self_symm_id,
              Iso.refl_trans, Iso.trans_refl] using h
          have hadAssoc (z : Y ≅ Y) :
              a ≪≫ d ≪≫ z = d ≪≫ a ≪≫ z := by
            rw [← Iso.trans_assoc, had, Iso.trans_assoc]
          have hadSymmAssoc (z : Y ≅ Y) :
              d.symm ≪≫ a ≪≫ z = a ≪≫ d.symm ≪≫ z := by
            rw [← Iso.trans_assoc, hadSymm, Iso.trans_assoc]
          have hconjAssoc (z : Y ≅ Y) :
              d.symm ≪≫ a ≪≫ d ≪≫ z = a ≪≫ z := by
            rw [hadSymmAssoc, ← Iso.trans_assoc d.symm d z,
              Iso.symm_self_id, Iso.refl_trans]
          have hLeft :
              (a ≪≫ ((d ≪≫ b) ≪≫ d.symm)) ≪≫ a =
                d ≪≫ b ≪≫ a ≪≫ b ≪≫ d.symm := by
            calc
              (a ≪≫ ((d ≪≫ b) ≪≫ d.symm)) ≪≫ a =
                  d ≪≫ a ≪≫ b ≪≫ d.symm ≪≫ a := by
                simpa only [Iso.trans_assoc] using
                  hadAssoc (b ≪≫ d.symm ≪≫ a)
              _ = d ≪≫ a ≪≫ b ≪≫ a ≪≫ d.symm := by
                have h := congrArg
                  (fun z => d ≪≫ a ≪≫ b ≪≫ z) hadSymm
                simpa only [Iso.trans_assoc] using h
              _ = d ≪≫ b ≪≫ a ≪≫ b ≪≫ d.symm := by
                have h := congrArg
                  (fun z => d ≪≫ z ≪≫ d.symm) hab.symm
                simpa only [Iso.trans_assoc] using h
          have hRight :
              (((d ≪≫ b) ≪≫ d.symm) ≪≫ a) ≪≫
                  ((d ≪≫ b) ≪≫ d.symm) =
                d ≪≫ b ≪≫ a ≪≫ b ≪≫ d.symm := by
            have h := congrArg
              (fun z => d ≪≫ b ≪≫ z ≪≫ b ≪≫ d.symm)
              (hconjAssoc (Iso.refl Y))
            simpa only [Iso.trans_assoc, Iso.trans_refl] using h
          exact hLeft.trans hRight.symm
        have hConjugateInvolutive {Y : C} (a d : Y ≅ Y)
            (ha : a ≪≫ a = Iso.refl _) :
            ((d ≪≫ a) ≪≫ d.symm) ≪≫
                ((d ≪≫ a) ≪≫ d.symm) = Iso.refl _ := by
          have h := congrArg (fun z => (d ≪≫ z) ≪≫ d.symm) ha
          calc
            ((d ≪≫ a) ≪≫ d.symm) ≪≫
                ((d ≪≫ a) ≪≫ d.symm) =
              (d ≪≫ (a ≪≫ a)) ≪≫ d.symm := by
                simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
            _ = Iso.refl _ := by
              simpa only [Iso.trans_assoc, Iso.refl_trans,
                Iso.trans_refl, Iso.self_symm_id] using h
        have hProductRightZero {Y : C} (a x : Y ≅ Y)
            (ha : a ≪≫ a = Iso.refl _)
            (hx : x ≪≫ x = Iso.refl _)
            (hb : (a ≪≫ x) ≪≫ a = (x ≪≫ a) ≪≫ x) :
            ((x ≪≫ a) ≪≫ x) ≪≫ a =
              x ≪≫ ((x ≪≫ a) ≪≫ x) := by
          have hLeft := congrArg (fun z => z ≪≫ a) hb.symm
          have hxAssoc : x ≪≫ x ≪≫ a ≪≫ x = a ≪≫ x := by
            rw [← Iso.trans_assoc x x (a ≪≫ x), hx, Iso.refl_trans]
          calc
            ((x ≪≫ a) ≪≫ x) ≪≫ a =
                ((a ≪≫ x) ≪≫ a) ≪≫ a := hLeft
            _ = a ≪≫ x := by
              simp only [Iso.trans_assoc, ha, Iso.trans_refl]
            _ = x ≪≫ ((x ≪≫ a) ≪≫ x) := by
              simpa only [Iso.trans_assoc] using hxAssoc.symm
        have hProductLeftZero {Y : C} (a x : Y ≅ Y)
            (hx : x ≪≫ x = Iso.refl _)
            (hb : (a ≪≫ x) ≪≫ a = (x ≪≫ a) ≪≫ x) :
            a ≪≫ ((x ≪≫ a) ≪≫ x) = x ≪≫ a := by
          calc
            a ≪≫ ((x ≪≫ a) ≪≫ x) =
                ((a ≪≫ x) ≪≫ a) ≪≫ x := by
                  simp only [Iso.trans_assoc]
            _ = ((x ≪≫ a) ≪≫ x) ≪≫ x := by rw [hb]
            _ = x ≪≫ a := by
              simp only [Iso.trans_assoc, hx, Iso.trans_refl]
        have hProductDistinct {Y : C} (a x y R : Y ≅ Y)
            (ha : a ≪≫ a = Iso.refl _)
            (hx : x ≪≫ x = Iso.refl _)
            (hy : y ≪≫ y = Iso.refl _)
            (hax : (a ≪≫ x) ≪≫ a = (x ≪≫ a) ≪≫ x)
            (hay : (a ≪≫ y) ≪≫ a = (y ≪≫ a) ≪≫ y)
            (hRxy : R = (x ≪≫ y) ≪≫ x)
            (hRyx : R = (y ≪≫ x) ≪≫ y)
            (hcomm : a ≪≫ R = R ≪≫ a) :
            ((x ≪≫ a) ≪≫ x) ≪≫ ((y ≪≫ a) ≪≫ y) =
              R ≪≫ ((x ≪≫ a) ≪≫ x) := by
          have hCommWord : a ≪≫ x ≪≫ y ≪≫ x =
              x ≪≫ y ≪≫ x ≪≫ a := by
            simpa only [Iso.trans_assoc, hRxy] using hcomm
          have haxy₀ : a ≪≫ x ≪≫ y =
              x ≪≫ y ≪≫ x ≪≫ a ≪≫ x := by
            have h := congrArg (fun z => z ≪≫ x) hCommWord
            simpa only [Iso.trans_assoc, hx, Iso.trans_refl] using h
          have hxa : x ≪≫ a ≪≫ x = a ≪≫ x ≪≫ a := by
            simpa only [Iso.trans_assoc] using hax.symm
          have haxy : a ≪≫ x ≪≫ y =
              x ≪≫ y ≪≫ a ≪≫ x ≪≫ a := by
            calc
              a ≪≫ x ≪≫ y =
                  x ≪≫ y ≪≫ x ≪≫ a ≪≫ x := haxy₀
              _ = x ≪≫ y ≪≫ a ≪≫ x ≪≫ a := by
                have h := congrArg (fun z => x ≪≫ y ≪≫ z) hxa
                simpa only [Iso.trans_assoc] using h
          have hyR : y ≪≫ R = x ≪≫ y := by
            rw [hRyx]
            simp only [Iso.trans_assoc]
            rw [← Iso.trans_assoc y y (x ≪≫ y), hy, Iso.refl_trans]
          have hxx (z : Y ≅ Y) : x ≪≫ x ≪≫ z = z := by
            rw [← Iso.trans_assoc, hx, Iso.refl_trans]
          have haa (z : Y ≅ Y) : a ≪≫ a ≪≫ z = z := by
            rw [← Iso.trans_assoc, ha, Iso.refl_trans]
          have hLeft₀ :
              ((x ≪≫ a) ≪≫ x) ≪≫ ((y ≪≫ a) ≪≫ y) =
                y ≪≫ a ≪≫ x ≪≫ y := by
            have h := congrArg (fun z => x ≪≫ z ≪≫ a ≪≫ y) haxy
            simpa only [Iso.trans_assoc, hxx, haa] using h
          have hLeft₁ : y ≪≫ a ≪≫ x ≪≫ y =
              y ≪≫ a ≪≫ y ≪≫ R := by
            have h := congrArg (fun z => y ≪≫ a ≪≫ z) hyR.symm
            simpa only [Iso.trans_assoc] using h
          have hya : y ≪≫ a ≪≫ y = a ≪≫ y ≪≫ a := by
            simpa only [Iso.trans_assoc] using hay.symm
          have hLeft₂ : y ≪≫ a ≪≫ y ≪≫ R =
              a ≪≫ y ≪≫ R ≪≫ a := by
            calc
              y ≪≫ a ≪≫ y ≪≫ R =
                  a ≪≫ y ≪≫ a ≪≫ R := by
                have h := congrArg (fun z => z ≪≫ R) hya
                simpa only [Iso.trans_assoc] using h
              _ = a ≪≫ y ≪≫ R ≪≫ a := by
                have h := congrArg (fun z => a ≪≫ y ≪≫ z) hcomm
                simpa only [Iso.trans_assoc] using h
          have hLeft₃ : a ≪≫ y ≪≫ R ≪≫ a =
              a ≪≫ x ≪≫ y ≪≫ a := by
            have h := congrArg (fun z => a ≪≫ z ≪≫ a) hyR
            simpa only [Iso.trans_assoc] using h
          have hLeft₄ : a ≪≫ x ≪≫ y ≪≫ a =
              x ≪≫ y ≪≫ a ≪≫ x := by
            have h := congrArg (fun z => z ≪≫ a) haxy
            simpa only [Iso.trans_assoc, ha, Iso.trans_refl] using h
          have hLeft :
              ((x ≪≫ a) ≪≫ x) ≪≫ ((y ≪≫ a) ≪≫ y) =
                x ≪≫ y ≪≫ a ≪≫ x :=
            hLeft₀.trans
              (hLeft₁.trans (hLeft₂.trans (hLeft₃.trans hLeft₄)))
          have hRight : R ≪≫ ((x ≪≫ a) ≪≫ x) =
              x ≪≫ y ≪≫ a ≪≫ x := by
            rw [hRxy]
            simp only [Iso.trans_assoc]
            rw [← Iso.trans_assoc x x (a ≪≫ x), hx,
              Iso.refl_trans]
          exact hLeft.trans hRight.symm
        have hAdjComm (A : C) (f : A ≅ A) :
            s A ≪≫ tensorIso (tensorIso f (Iso.refl X))
                (Iso.refl X) =
              tensorIso (tensorIso f (Iso.refl X))
                  (Iso.refl X) ≪≫ s A := by
          apply Iso.ext
          simp only [s, Iso.trans_assoc, Iso.trans_hom,
            whiskerLeftIso_hom, Iso.symm_hom, tensorIso_hom,
            Iso.refl_hom, tensorHom_id]
          rw [← associator_inv_naturality_left f.hom X X]
          rw [whisker_exchange_assoc f.hom (β_ X X).hom]
          rw [← associator_naturality_left_assoc f.hom X X]
        let LL (e : Equiv.Perm (Fin k)) :
            tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2) :=
          tensorIso (L e) (Iso.refl X)
        have hLLrefl : LL (Equiv.refl (Fin k)) = Iso.refl _ := by
          dsimp only [LL]
          rw [hLrefl]
          apply Iso.ext
          exact id_tensorHom_id _ _
        let adj : tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2) :=
          adjacentSwapIso X k
        let M2 (p : Fin (k + 2)) :
            tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2) :=
          moveZeroIso X (k + 2) p
        let L2 (f : Equiv.Perm (Fin (k + 1))) :
            tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2) :=
          tensorIso (permutationIsoAux X (k + 1) f) (Iso.refl X)
        have hadj : adj = s (tensorPowObj X k) := rfl
        have hM2zero : M2 0 = Iso.refl _ := by
          apply Iso.ext
          simp only [tensorPowObj_succ, moveZeroIso, Fin.cases_zero,
            Iso.refl_hom, M2]
        have hM2succ (r : Fin (k + 1)) :
            M2 r.succ = (LM r ≪≫ adj) ≪≫ (LM r).symm := by
          dsimp only [M2, LM, adj]
          exact moveZeroIso_succ X k r
        have hAdjInvolutive : adj ≪≫ adj = Iso.refl _ := by
          rw [hadj]
          exact hsInvolutive (tensorPowObj X k)
        have hM2Involutive (p : Fin (k + 2)) :
            M2 p ≪≫ M2 p = Iso.refl _ := by
          refine Fin.cases ?_ (fun r => ?_) p
          · rw [hM2zero, Iso.refl_trans]
          · rw [hM2succ]
            exact hConjugateInvolutive adj (LM r) hAdjInvolutive
        have hL2Decomp (f : Equiv.Perm (Fin (k + 1))) :
            let d := Equiv.Perm.decomposeFin f
            L2 f = LL d.2 ≪≫ LM d.1 := by
          dsimp only
          let d := Equiv.Perm.decomposeFin f
          change tensorIso
                (L d.2 ≪≫ moveZeroIso X (k + 1) d.1)
                (Iso.refl X) =
              LL d.2 ≪≫ LM d.1
          apply Iso.ext
          change
            (((L d.2).hom ≫
                (moveZeroIso X (k + 1) d.1).hom) ⊗ₘ 𝟙 X) =
              ((L d.2).hom ⊗ₘ 𝟙 X) ≫
                ((moveZeroIso X (k + 1) d.1).hom ⊗ₘ 𝟙 X)
          simpa only [Category.comp_id] using
            (tensorHom_comp_tensorHom (L d.2).hom (𝟙 X)
              (moveZeroIso X (k + 1) d.1).hom (𝟙 X)).symm
        have hAdjLL (e : Equiv.Perm (Fin k)) :
            adj ≪≫ LL e = LL e ≪≫ adj := by
          change s (tensorPowObj X k) ≪≫
                tensorIso
                    (tensorIso (permutationIsoAux X k e) (Iso.refl X))
                    (Iso.refl X) =
              tensorIso
                  (tensorIso (permutationIsoAux X k e) (Iso.refl X))
                  (Iso.refl X) ≪≫ s (tensorPowObj X k)
          exact hAdjComm (tensorPowObj X k) (permutationIsoAux X k e)
        have hLM_LL (r : Fin (k + 1))
            (e : Equiv.Perm (Fin k)) :
            LM r ≪≫ LL e = LL e ≪≫ LM (liftPoint e r) := by
          have hr := hN r e
          change moveZeroIso X (k + 1) r ≪≫ L e =
              L e ≪≫ moveZeroIso X (k + 1) (liftPoint e r) at hr
          apply Iso.ext
          change
            ((moveZeroIso X (k + 1) r).hom ⊗ₘ 𝟙 X) ≫
                ((L e).hom ⊗ₘ 𝟙 X) =
              ((L e).hom ⊗ₘ 𝟙 X) ≫
                ((moveZeroIso X (k + 1) (liftPoint e r)).hom ⊗ₘ 𝟙 X)
          rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
          have hrHom := congrArg Iso.hom hr
          simp only [Iso.trans_hom] at hrHom
          rw [hrHom]
        have hM2_LL (r : Fin (k + 1))
            (e : Equiv.Perm (Fin k)) :
            M2 r.succ ≪≫ LL e =
              LL e ≪≫ M2 (liftPoint e r).succ := by
          rw [hM2succ, hM2succ, hLMSymm, hLMSymm]
          apply Iso.ext
          simp only [Iso.trans_hom]
          have hr := congrArg Iso.hom (hLM_LL r e)
          have ha := congrArg Iso.hom (hAdjLL e)
          simp only [Iso.trans_hom] at hr ha
          simp only [Category.assoc]
          rw [hr]
          rw [← Category.assoc (adj.hom) (LL e).hom
            (LM (liftPoint e r)).hom]
          rw [ha]
          simp only [Category.assoc]
          rw [← Category.assoc (LM r).hom (LL e).hom
            (adj.hom ≫ (LM (liftPoint e r)).hom)]
          rw [hr]
          exact Category.assoc _ _ _
        have hLMzero : LM (0 : Fin (k + 1)) = Iso.refl _ := by
          dsimp only [LM]
          rw [hMzero]
          apply Iso.ext
          simp only [tensorPowObj_succ, tensorIso_hom, Iso.refl_hom,
            tensorHom_id, id_whiskerRight]
        have hCross (r q : Fin (k + 1)) :
            M2 r.succ ≪≫ LM q =
              LM q ≪≫ M2 (Equiv.swap 0 q r).succ := by
          let c := starDec r q
          have hEndpoint : c.1 = Equiv.swap 0 q r := by
            have hc := Equiv.symm_apply_apply Equiv.Perm.decomposeFin
              ((Equiv.swap 0 r).trans (Equiv.swap 0 q))
            have hc0 := congrArg (fun e => e 0) hc
            change c.1 = Equiv.swap 0 q r
            rw [Equiv.Perm.decomposeFin_symm_apply_zero] at hc0
            simpa only [Equiv.trans_apply, Equiv.swap_apply_left] using hc0
          have hs := hS r q
          change moveZeroIso X (k + 1) r ≪≫
                moveZeroIso X (k + 1) q =
              L c.2 ≪≫ moveZeroIso X (k + 1) c.1 at hs
          have hLMprod : LM r ≪≫ LM q = LL c.2 ≪≫ LM c.1 := by
            apply Iso.ext
            change
              ((moveZeroIso X (k + 1) r).hom ⊗ₘ 𝟙 X) ≫
                  ((moveZeroIso X (k + 1) q).hom ⊗ₘ 𝟙 X) =
                ((L c.2).hom ⊗ₘ 𝟙 X) ≫
                  ((moveZeroIso X (k + 1) c.1).hom ⊗ₘ 𝟙 X)
            rw [tensorHom_comp_tensorHom,
              tensorHom_comp_tensorHom]
            have hsHom := congrArg Iso.hom hs
            simp only [Iso.trans_hom] at hsHom
            rw [hsHom]
          rw [hEndpoint] at hLMprod
          have hqForm :
              LM q = (LM r ≪≫ LL c.2) ≪≫
                LM (Equiv.swap 0 q r) := by
            calc
              LM q = Iso.refl _ ≪≫ LM q := by rw [Iso.refl_trans]
              _ = (LM r ≪≫ LM r) ≪≫ LM q := by
                rw [hLMInvolutive]
              _ = LM r ≪≫ (LM r ≪≫ LM q) := by
                rw [Iso.trans_assoc]
              _ = LM r ≪≫
                  (LL c.2 ≪≫ LM (Equiv.swap 0 q r)) := by
                rw [hLMprod]
              _ = (LM r ≪≫ LL c.2) ≪≫
                  LM (Equiv.swap 0 q r) := by
                rw [Iso.trans_assoc]
          rw [hM2succ, hM2succ, hLMSymm, hLMSymm, hqForm]
          have hInvAssoc (p : Fin (k + 1))
              (z : tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2)) :
              LM p ≪≫ LM p ≪≫ z = z := by
            rw [← Iso.trans_assoc, hLMInvolutive, Iso.refl_trans]
          have hAdjAssoc (e : Equiv.Perm (Fin k))
              (z : tensorPowObj X (k + 2) ≅ tensorPowObj X (k + 2)) :
              adj ≪≫ LL e ≪≫ z = LL e ≪≫ adj ≪≫ z := by
            rw [← Iso.trans_assoc, hAdjLL, Iso.trans_assoc]
          simp only [Iso.trans_assoc, hInvAssoc]
          rw [hAdjAssoc]
        have hBraid (q : Fin (k + 1)) (hq : q ≠ 0) :
            (adj ≪≫ LM q) ≪≫ adj =
              (LM q ≪≫ adj) ≪≫ LM q := by
          cases k with
          | zero => exact (hq (Fin.eq_zero q)).elim
          | succ j =>
              obtain ⟨t, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hq
              let e : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 t
              let inner :
                  tensorPowObj X (j + 2) ≅ tensorPowObj X (j + 2) :=
                tensorIso (moveZeroIso X (j + 1) t) (Iso.refl X)
              let low :
                  tensorPowObj X (j + 2) ≅ tensorPowObj X (j + 2) :=
                adjacentSwapIso X j
              let lift3 (z :
                  tensorPowObj X (j + 2) ≅ tensorPowObj X (j + 2)) :
                  tensorPowObj X (j + 3) ≅ tensorPowObj X (j + 3) :=
                tensorIso z (Iso.refl X)
              let d : tensorPowObj X (j + 3) ≅ tensorPowObj X (j + 3) :=
                LL e
              let dLift :
                  tensorPowObj X (j + 3) ≅ tensorPowObj X (j + 3) :=
                lift3 inner
              let lowerAdj :
                  tensorPowObj X (j + 3) ≅ tensorPowObj X (j + 3) :=
                lift3 low
              have hdec : Equiv.Perm.decomposeFin e =
                  (t, Equiv.refl (Fin j)) := by
                apply Equiv.Perm.decomposeFin.symm.injective
                simp [e]
              have hAuxStar :
                  permutationIsoAux X (j + 1) e =
                    moveZeroIso X (j + 1) t := by
                rw [permutationIsoAux, hdec,
                  permutationIsoAux_refl]
                let rIso :
                    tensorPowObj X (j + 1) ≅ tensorPowObj X (j + 1) :=
                  tensorIso (Iso.refl (tensorPowObj X j)) (Iso.refl X)
                change rIso ≪≫ moveZeroIso X (j + 1) t =
                  moveZeroIso X (j + 1) t
                have htr : rIso = Iso.refl (tensorPowObj X (j + 1)) := by
                  apply Iso.ext
                  exact id_tensorHom_id _ _
                rw [htr, Iso.refl_trans]
              have hBase :
                  (lowerAdj ≪≫ adj) ≪≫ lowerAdj =
                    (adj ≪≫ lowerAdj) ≪≫ adj := by
                have hb := hPrefixYB (tensorPowObj X j)
                change (lowerAdj ≪≫ adj) ≪≫ lowerAdj =
                  (adj ≪≫ lowerAdj) ≪≫ adj at hb
                exact hb
              have hComm : adj ≪≫ d = d ≪≫ adj := hAdjLL e
              have hd : d = dLift := by
                dsimp only [d, dLift, LL, L, inner]
                rw [hAuxStar]
              have hMove :
                  moveZeroIso X (j + 2) t.succ =
                    (inner ≪≫ low) ≪≫ inner.symm := by
                dsimp only [inner, low]
                exact moveZeroIso_succ X j t
              have hTensorConj :
                  lift3 ((inner ≪≫ low) ≪≫ inner.symm) =
                    (dLift ≪≫ lowerAdj) ≪≫ dLift.symm := by
                dsimp only [lift3, dLift, lowerAdj]
                apply Iso.ext
                change
                  ((((inner.hom ≫ low.hom) ≫ inner.inv) ⊗ₘ 𝟙 X)) =
                    (((inner.hom ⊗ₘ 𝟙 X) ≫
                      (low.hom ⊗ₘ 𝟙 X)) ≫ (inner.inv ⊗ₘ 𝟙 X))
                rw [tensorHom_comp_tensorHom,
                  tensorHom_comp_tensorHom]
                simp only [Category.comp_id]
              have hLMsucc :
                  LM t.succ = (d ≪≫ lowerAdj) ≪≫ d.symm := by
                calc
                  LM t.succ = lift3
                      (moveZeroIso X (j + 2) t.succ) := rfl
                  _ = lift3 ((inner ≪≫ low) ≪≫ inner.symm) := by
                    rw [hMove]
                  _ = (dLift ≪≫ lowerAdj) ≪≫ dLift.symm := hTensorConj
                  _ = (d ≪≫ lowerAdj) ≪≫ d.symm := by rw [hd]
              rw [hLMsucc]
              exact hConjugateBraid adj lowerAdj d hBase hComm
        let starDec2 (p q : Fin (k + 2)) :
            Fin (k + 2) × Equiv.Perm (Fin (k + 1)) :=
          Equiv.Perm.decomposeFin
            ((Equiv.swap 0 p).trans (Equiv.swap 0 q))
        have hStar2ZeroLeft (q : Fin (k + 2)) :
            starDec2 0 q = (q, Equiv.refl (Fin (k + 1))) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          simp [starDec2]
        have hStar2ZeroRight (p : Fin (k + 2)) :
            starDec2 p 0 = (p, Equiv.refl (Fin (k + 1))) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          simp [starDec2]
        have hStar2Same (p : Fin (k + 2)) :
            starDec2 p p = (0, Equiv.refl (Fin (k + 1))) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          simp [starDec2]
        have hStar2Distinct (r t : Fin (k + 1)) (hrt : r ≠ t) :
            starDec2 r.succ t.succ = (r.succ, Equiv.swap r t) := by
          apply Equiv.Perm.decomposeFin.symm.injective
          ext x
          refine Fin.cases ?_ (fun i => ?_) x
          · simp [starDec2, Equiv.swap_apply_def, hrt]
          · by_cases hir : i = r
            · subst i
              simp [starDec2, Equiv.swap_apply_def, Ne.symm hrt]
            · by_cases hit : i = t
              · subst i
                simp [starDec2, Equiv.swap_apply_def, Ne.symm hrt]
              · simp [starDec2, Equiv.swap_apply_def, hir, hit]
        have hAuxStar2 (r : Fin (k + 1)) :
            permutationIsoAux X (k + 1) (Equiv.swap 0 r) =
              moveZeroIso X (k + 1) r := by
          have hdec : Equiv.Perm.decomposeFin (Equiv.swap 0 r) =
              (r, Equiv.refl (Fin k)) := by
            apply Equiv.Perm.decomposeFin.symm.injective
            simp
          rw [permutationIsoAux, hdec]
          change L (Equiv.refl (Fin k)) ≪≫
              moveZeroIso X (k + 1) r =
            moveZeroIso X (k + 1) r
          rw [hLrefl, Iso.refl_trans]
        have hL2refl : L2 (Equiv.refl (Fin (k + 1))) = Iso.refl _ := by
          dsimp only [L2]
          rw [permutationIsoAux_refl]
          apply Iso.ext
          exact id_tensorHom_id _ _
        have hL2Star (r : Fin (k + 1)) :
            L2 (Equiv.swap 0 r) = LM r := by
          dsimp only [L2, LM]
          rw [hAuxStar2]
        have hT' : T (k + 1) := by
          intro a b
          let da := Equiv.Perm.decomposeFin a
          let db := Equiv.Perm.decomposeFin b
          let p' := liftPoint db.2 da.1
          let c := starDec p' db.1
          have hdec : Equiv.Perm.decomposeFin (a.trans b) =
              (c.1, (da.2.trans db.2).trans c.2) :=
            hProduct a b
          have hn := hN da.1 db.2
          change moveZeroIso X (k + 1) da.1 ≪≫
                L db.2 =
              L db.2 ≪≫
                moveZeroIso X (k + 1) p' at hn
          have hs := hS p' db.1
          change moveZeroIso X (k + 1) p' ≪≫
              moveZeroIso X (k + 1) db.1 =
              L c.2 ≪≫
                moveZeroIso X (k + 1) c.1 at hs
          change
            L (Equiv.Perm.decomposeFin (a.trans b)).2 ≪≫
              moveZeroIso X (k + 1)
                (Equiv.Perm.decomposeFin (a.trans b)).1 =
            (L da.2 ≪≫
              moveZeroIso X (k + 1) da.1) ≪≫
            (L db.2 ≪≫
              moveZeroIso X (k + 1) db.1)
          rw [hdec]
          symm
          apply Iso.ext
          change
            ((L da.2).hom ≫
              (moveZeroIso X (k + 1) da.1).hom) ≫
                ((L db.2).hom ≫
                  (moveZeroIso X (k + 1) db.1).hom) =
              (L ((da.2.trans db.2).trans c.2)).hom ≫
                (moveZeroIso X (k + 1) c.1).hom
          have hnHom := congrArg Iso.hom hn
          have hsHom := congrArg Iso.hom hs
          have hefHom := congrArg Iso.hom
            (hTensorTrans da.2 db.2)
          have hefcHom := congrArg Iso.hom
            (hTensorTrans (da.2.trans db.2) c.2)
          simp only [Iso.trans_hom] at hnHom hsHom hefHom hefcHom
          rw [Category.assoc]
          rw [← Category.assoc
            (moveZeroIso X (k + 1) da.1).hom
            (L db.2).hom
            (moveZeroIso X (k + 1) db.1).hom]
          rw [hnHom]
          rw [Category.assoc]
          rw [← Category.assoc
            (L da.2).hom
            (L db.2).hom
            ((moveZeroIso X (k + 1) p').hom ≫
              (moveZeroIso X (k + 1) db.1).hom)]
          rw [hefHom]
          rw [hsHom]
          rw [← Category.assoc]
          rw [hefcHom]
        have hL2Trans (f g : Equiv.Perm (Fin (k + 1))) :
            L2 f ≪≫ L2 g = L2 (f.trans g) := by
          dsimp only [L2]
          rw [hT' f g]
          apply Iso.ext
          change
            ((permutationIsoAux X (k + 1) f).hom ⊗ₘ 𝟙 X) ≫
                ((permutationIsoAux X (k + 1) g).hom ⊗ₘ 𝟙 X) =
              (((permutationIsoAux X (k + 1) f).hom ≫
                (permutationIsoAux X (k + 1) g).hom) ⊗ₘ 𝟙 X)
          simpa only [Category.comp_id] using
            tensorHom_comp_tensorHom
              (permutationIsoAux X (k + 1) f).hom (𝟙 X)
              (permutationIsoAux X (k + 1) g).hom (𝟙 X)
        have hSwapTriple (r t : Fin (k + 1))
            (hrt : r ≠ t) (ht : t ≠ 0) :
            Equiv.swap r t =
              ((Equiv.swap 0 r).trans (Equiv.swap 0 t)).trans
                (Equiv.swap 0 r) := by
          by_cases hr : r = 0
          · subst r
            simp
          apply Equiv.ext
          intro x
          by_cases hx0 : x = 0
          · subst x
            simp [Equiv.swap_apply_def, hrt, hr, Ne.symm hr,
              Ne.symm ht]
          by_cases hxr : x = r
          · subst x
            simp [Equiv.swap_apply_def, ht, Ne.symm hrt]
          by_cases hxt : x = t
          · subst x
            simp [Equiv.swap_apply_def, ht, Ne.symm hrt]
          · simp [Equiv.swap_apply_def, hx0, hxr, hxt]
        have hL2SwapTriple (r t : Fin (k + 1))
            (hrt : r ≠ t) (ht : t ≠ 0) :
            L2 (Equiv.swap r t) =
              (LM r ≪≫ LM t) ≪≫ LM r := by
          rw [hSwapTriple r t hrt ht]
          rw [← hL2Trans, ← hL2Trans, hL2Star, hL2Star]
        refine ⟨hT', ?_, ?_⟩
        · intro p f
          let d := Equiv.Perm.decomposeFin f
          have hdecomp : L2 f = LL d.2 ≪≫ LM d.1 := hL2Decomp f
          change M2 p ≪≫ L2 f =
            L2 f ≪≫ M2 (Fin.cases 0 (fun i => (f i).succ) p)
          refine Fin.cases ?_ (fun r => ?_) p
          · rw [hM2zero]
            change Iso.refl _ ≪≫ L2 f = L2 f ≪≫ M2 0
            rw [Iso.refl_trans, hM2zero, Iso.trans_refl]
          · have hf : Equiv.Perm.decomposeFin.symm d = f := by
              exact Equiv.symm_apply_apply _ _
            have hfr : f r = Equiv.swap 0 d.1 (liftPoint d.2 r) := by
              calc
                f r = Equiv.Perm.decomposeFin.symm d r := by rw [hf]
                _ = ((liftPerm d.2).trans
                    (Equiv.swap 0 d.1)) r := by rw [hD]
                _ = Equiv.swap 0 d.1 (liftPoint d.2 r) := by
                  change Equiv.swap 0 d.1 (liftPerm d.2 r) = _
                  rw [hLiftPoint]
            change M2 r.succ ≪≫ L2 f =
              L2 f ≪≫ M2 (f r).succ
            rw [hfr]
            calc
              M2 r.succ ≪≫ L2 f =
                  M2 r.succ ≪≫ (LL d.2 ≪≫ LM d.1) := by
                    rw [hdecomp]
              _ = (M2 r.succ ≪≫ LL d.2) ≪≫ LM d.1 := by
                    rw [Iso.trans_assoc]
              _ = (LL d.2 ≪≫ M2 (liftPoint d.2 r).succ) ≪≫
                  LM d.1 := by rw [hM2_LL]
              _ = LL d.2 ≪≫
                  (M2 (liftPoint d.2 r).succ ≪≫ LM d.1) := by
                    rw [Iso.trans_assoc]
              _ = LL d.2 ≪≫
                  (LM d.1 ≪≫
                    M2 (Equiv.swap 0 d.1 (liftPoint d.2 r)).succ) := by
                    rw [hCross]
              _ = (LL d.2 ≪≫ LM d.1) ≪≫
                  M2 (Equiv.swap 0 d.1 (liftPoint d.2 r)).succ := by
                    rw [Iso.trans_assoc]
              _ = L2 f ≪≫
                  M2 (Equiv.swap 0 d.1 (liftPoint d.2 r)).succ := by
                    rw [hdecomp]
        · intro p q
          change M2 p ≪≫ M2 q =
            L2 (starDec2 p q).2 ≪≫ M2 (starDec2 p q).1
          refine Fin.cases ?_ (fun r => ?_) p
          · rw [hStar2ZeroLeft, hM2zero, hL2refl]
          · refine Fin.cases ?_ (fun t => ?_) q
            · rw [hStar2ZeroRight, hM2zero, hL2refl]
              simp only [Iso.trans_refl, Iso.refl_trans]
            · by_cases hrt : r = t
              · subst t
                rw [hStar2Same, hM2Involutive, hL2refl,
                  hM2zero, Iso.refl_trans]
              · rw [hStar2Distinct r t hrt]
                change M2 r.succ ≪≫ M2 t.succ =
                  L2 (Equiv.swap r t) ≪≫ M2 r.succ
                by_cases ht : t = 0
                · subst t
                  have hr : r ≠ 0 := by
                    intro h
                    exact hrt h
                  rw [Equiv.swap_comm, hL2Star]
                  rw [hM2succ, hM2succ, hLMzero,
                    Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
                    hLMSymm]
                  exact hProductRightZero adj (LM r)
                    hAdjInvolutive (hLMInvolutive r) (hBraid r hr)
                by_cases hr : r = 0
                · subst r
                  rw [hL2Star]
                  rw [hM2succ, hM2succ, hLMzero,
                    Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
                    hLMSymm]
                  exact hProductLeftZero adj (LM t)
                    (hLMInvolutive t) (hBraid t ht)
                · let R := L2 (Equiv.swap r t)
                  have hRxy : R = (LM r ≪≫ LM t) ≪≫ LM r :=
                    hL2SwapTriple r t hrt ht
                  have hRyx : R = (LM t ≪≫ LM r) ≪≫ LM t := by
                    calc
                      R = L2 (Equiv.swap t r) := by
                        rw [Equiv.swap_comm]
                      _ = (LM t ≪≫ LM r) ≪≫ LM t :=
                        hL2SwapTriple t r (Ne.symm hrt) hr
                  obtain ⟨r0, rfl⟩ :=
                    Fin.exists_succ_eq_of_ne_zero hr
                  obtain ⟨t0, rfl⟩ :=
                    Fin.exists_succ_eq_of_ne_zero ht
                  let b : Equiv.Perm (Fin k) := Equiv.swap r0 t0
                  have hpermLift :
                      Equiv.swap r0.succ t0.succ = liftPerm b := by
                    apply Equiv.ext
                    intro x
                    refine Fin.cases ?_ (fun i => ?_) x
                    · simp [liftPerm, b, Equiv.swap_apply_def,
                        Ne.symm (Fin.succ_ne_zero r0),
                        Ne.symm (Fin.succ_ne_zero t0)]
                    · by_cases hir : i = r0
                      · subst i
                        simp [liftPerm, b]
                      · by_cases hit : i = t0
                        · subst i
                          simp [liftPerm, b]
                        · simp [liftPerm, b, Equiv.swap_apply_def,
                            hir, hit]
                  have hL2Lift : L2 (liftPerm b) = LL b := by
                    have hdec : Equiv.Perm.decomposeFin (liftPerm b) =
                        (0, b) := by
                      exact Equiv.apply_symm_apply _ _
                    have h := hL2Decomp (liftPerm b)
                    rw [hdec] at h
                    change L2 (liftPerm b) = LL b ≪≫ LM 0 at h
                    rw [hLMzero, Iso.trans_refl] at h
                    exact h
                  have hRLL : R = LL b := by
                    dsimp only [R]
                    rw [hpermLift, hL2Lift]
                  have hcomm : adj ≪≫ R = R ≪≫ adj := by
                    rw [hRLL]
                    exact hAdjLL b
                  rw [hM2succ, hM2succ, hLMSymm, hLMSymm]
                  exact hProductDistinct adj (LM r0.succ) (LM t0.succ) R
                    hAdjInvolutive (hLMInvolutive r0.succ)
                    (hLMInvolutive t0.succ) (hBraid r0.succ (by simp))
                    (hBraid t0.succ (by simp)) hRxy hRyx hcomm
  exact (hTNS n).1 σ τ

/-- The canonical symmetric action of a finite equivalence on tensor powers.
Public coordinates are conjugated by reversal because the recursive carrier
adds its newest factor on the right. -/
noncomputable def permutationIso {m n : ℕ}
    (X : C) (e : Fin m ≃ Fin n) :
    tensorPowObj X m ≅ tensorPowObj X n := by
  have h : m = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact permutationIsoAux X m
    (Fin.revPerm.trans (e.trans Fin.revPerm))

/-- The identity finite equivalence acts by the identity isomorphism. -/
theorem permutationIso_refl (X : C) (n : ℕ) :
    permutationIso X (Equiv.refl (Fin n)) = Iso.refl _ := by
  simp only [permutationIso]
  have hrev : Fin.revPerm.trans (Fin.revPerm : Fin n ≃ Fin n) =
      Equiv.refl (Fin n) := by
    apply Equiv.ext
    intro i
    exact Fin.rev_rev i
  rw [Equiv.refl_trans, hrev, permutationIsoAux_refl]

/-- The symmetric action respects composition of finite equivalences. -/
theorem permutationIso_trans {m n k : ℕ} (X : C)
    (e : Fin m ≃ Fin n) (f : Fin n ≃ Fin k) :
    permutationIso X (e.trans f) =
      permutationIso X e ≪≫ permutationIso X f := by
  have hmn : m = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hnk : n = k := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f
  subst n
  subst k
  simp only [permutationIso]
  have hrev :
      Fin.revPerm.trans ((e.trans f).trans Fin.revPerm) =
        (Fin.revPerm.trans (e.trans Fin.revPerm)).trans
          (Fin.revPerm.trans (f.trans Fin.revPerm)) := by
    apply Equiv.ext
    intro i
    simp only [Equiv.trans_apply]
    change Fin.rev (f (e (Fin.rev i))) =
      Fin.rev (f (Fin.rev (Fin.rev (e (Fin.rev i)))))
    rw [Fin.rev_rev]
  rw [hrev, permutationIsoAux_trans]

/-- The action of an inverse finite equivalence is the inverse isomorphism. -/
theorem permutationIso_symm {m n : ℕ} (X : C)
    (e : Fin m ≃ Fin n) :
    permutationIso X e.symm = (permutationIso X e).symm := by
  apply Iso.ext
  change (permutationIso X e.symm).hom = (permutationIso X e).inv
  have h := congrArg Iso.hom (permutationIso_trans X e e.symm)
  rw [Equiv.self_trans_symm, permutationIso_refl] at h
  simp only [Iso.trans_hom, Iso.refl_hom] at h
  exact (Iso.hom_comp_eq_id (permutationIso X e)).mp h.symm

/-- The symmetric action is natural in the powered object. -/
theorem permutationIso_hom_naturality
    {X Y : C} (g : X ⟶ Y) {m n : ℕ} (e : Fin m ≃ Fin n) :
    tensorPowMap g m ≫ (permutationIso Y e).hom =
      (permutationIso X e).hom ≫ tensorPowMap g n := by
  have h : m = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  have hAdjacent (k : ℕ) :
      tensorPowMap g (k + 2) ≫ (adjacentSwapIso Y k).hom =
        (adjacentSwapIso X k).hom ≫ tensorPowMap g (k + 2) := by
    have hAdjY : (adjacentSwapIso Y k).hom =
        (α_ (tensorPowObj Y k) Y Y).hom ≫
          (tensorPowObj Y k ◁ (β_ Y Y).hom) ≫
            (α_ (tensorPowObj Y k) Y Y).inv := rfl
    have hAdjX : (adjacentSwapIso X k).hom =
        (α_ (tensorPowObj X k) X X).hom ≫
          (tensorPowObj X k ◁ (β_ X X).hom) ≫
            (α_ (tensorPowObj X k) X X).inv := rfl
    rw [hAdjY, hAdjX]
    change
      ((tensorPowMap g k ⊗ₘ g) ⊗ₘ g) ≫
          (α_ (tensorPowObj Y k) Y Y).hom ≫
            (tensorPowObj Y k ◁ (β_ Y Y).hom) ≫
              (α_ (tensorPowObj Y k) Y Y).inv =
        ((α_ (tensorPowObj X k) X X).hom ≫
          (tensorPowObj X k ◁ (β_ X X).hom) ≫
            (α_ (tensorPowObj X k) X X).inv) ≫
              ((tensorPowMap g k ⊗ₘ g) ⊗ₘ g)
    have hMiddle :
        (tensorPowMap g k ⊗ₘ (g ⊗ₘ g)) ≫
            (tensorPowObj Y k ◁ (β_ Y Y).hom) =
          (tensorPowObj X k ◁ (β_ X X).hom) ≫
            (tensorPowMap g k ⊗ₘ (g ⊗ₘ g)) := by
      rw [← id_tensorHom, ← id_tensorHom,
        tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp,
        BraidedCategory.braiding_naturality]
    have hMiddleTail :
        (tensorPowMap g k ⊗ₘ (g ⊗ₘ g)) ≫
              (tensorPowObj Y k ◁ (β_ Y Y).hom) ≫
                (α_ (tensorPowObj Y k) Y Y).inv =
          (tensorPowObj X k ◁ (β_ X X).hom) ≫
            (tensorPowMap g k ⊗ₘ (g ⊗ₘ g)) ≫
              (α_ (tensorPowObj Y k) Y Y).inv := by
      rw [← Category.assoc, hMiddle, Category.assoc]
    calc
      ((tensorPowMap g k ⊗ₘ g) ⊗ₘ g) ≫
            (α_ (tensorPowObj Y k) Y Y).hom ≫
              (tensorPowObj Y k ◁ (β_ Y Y).hom) ≫
                (α_ (tensorPowObj Y k) Y Y).inv =
          (α_ (tensorPowObj X k) X X).hom ≫
            (tensorPowMap g k ⊗ₘ (g ⊗ₘ g)) ≫
              (tensorPowObj Y k ◁ (β_ Y Y).hom) ≫
                (α_ (tensorPowObj Y k) Y Y).inv := by
          rw [associator_naturality_assoc]
      _ = (α_ (tensorPowObj X k) X X).hom ≫
            (tensorPowObj X k ◁ (β_ X X).hom) ≫
              (tensorPowMap g k ⊗ₘ (g ⊗ₘ g)) ≫
                (α_ (tensorPowObj Y k) Y Y).inv := by
          rw [hMiddleTail]
      _ = (α_ (tensorPowObj X k) X X).hom ≫
            (tensorPowObj X k ◁ (β_ X X).hom) ≫
              (α_ (tensorPowObj X k) X X).inv ≫
                ((tensorPowMap g k ⊗ₘ g) ⊗ₘ g) := by
          rw [associator_inv_naturality]
      _ = ((α_ (tensorPowObj X k) X X).hom ≫
              (tensorPowObj X k ◁ (β_ X X).hom) ≫
                (α_ (tensorPowObj X k) X X).inv) ≫
            ((tensorPowMap g k ⊗ₘ g) ⊗ₘ g) := by
          simp only [Category.assoc]
  let M : ℕ → Prop := fun k => ∀ i : Fin k,
    tensorPowMap g k ≫ (moveZeroIso Y k i).hom =
      (moveZeroIso X k i).hom ≫ tensorPowMap g k
  let T : ℕ → Prop := fun k => ∀ τ : Equiv.Perm (Fin k),
    tensorPowMap g k ≫ (permutationIsoAux Y k τ).hom =
      (permutationIsoAux X k τ).hom ≫ tensorPowMap g k
  have hMT : ∀ k, M k ∧ T k := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro τ
          change (𝟙 _) ≫ (𝟙 _) = (𝟙 _) ≫ (𝟙 _)
          simp only [Category.comp_id]
    | succ k ih =>
        rcases ih with ⟨hM, hT⟩
        have hMsucc : M (k + 1) := by
          cases k with
          | zero =>
              intro i
              have hi : i = 0 := Fin.eq_zero i
              subst i
              change tensorPowMap g 1 ≫ (Iso.refl _).hom =
                (Iso.refl _).hom ≫ tensorPowMap g 1
              simp only [Iso.refl_hom, Category.comp_id,
                Category.id_comp]
          | succ k =>
              intro i
              refine Fin.cases ?_ (fun q => ?_) i
              · change tensorPowMap g (k + 2) ≫ (Iso.refl _).hom =
                  (Iso.refl _).hom ≫ tensorPowMap g (k + 2)
                simp only [Iso.refl_hom, Category.comp_id,
                  Category.id_comp]
              · let AX : tensorPowObj X (k + 2) ≅
                    tensorPowObj X (k + 2) :=
                  tensorIso (moveZeroIso X (k + 1) q) (Iso.refl X)
                let AY : tensorPowObj Y (k + 2) ≅
                    tensorPowObj Y (k + 2) :=
                  tensorIso (moveZeroIso Y (k + 1) q) (Iso.refl Y)
                let SX : tensorPowObj X (k + 2) ≅
                    tensorPowObj X (k + 2) := adjacentSwapIso X k
                let SY : tensorPowObj Y (k + 2) ≅
                    tensorPowObj Y (k + 2) := adjacentSwapIso Y k
                change tensorPowMap g (k + 2) ≫
                      (moveZeroIso Y (k + 2) q.succ).hom =
                    (moveZeroIso X (k + 2) q.succ).hom ≫
                      tensorPowMap g (k + 2)
                have hA : tensorPowMap g (k + 2) ≫ AY.hom =
                    AX.hom ≫ tensorPowMap g (k + 2) := by
                  change (tensorPowMap g (k + 1) ⊗ₘ g) ≫
                        ((moveZeroIso Y (k + 1) q).hom ⊗ₘ 𝟙 Y) =
                    ((moveZeroIso X (k + 1) q).hom ⊗ₘ 𝟙 X) ≫
                      (tensorPowMap g (k + 1) ⊗ₘ g)
                  rw [tensorHom_comp_tensorHom,
                    tensorHom_comp_tensorHom, hM q]
                  simp only [Category.comp_id, Category.id_comp]
                have hAinv : tensorPowMap g (k + 2) ≫ AY.inv =
                    AX.inv ≫ tensorPowMap g (k + 2) := by
                  apply (cancel_mono AY.hom).1
                  calc
                    (tensorPowMap g (k + 2) ≫ AY.inv) ≫ AY.hom =
                        tensorPowMap g (k + 2) := by
                      simp only [Category.assoc,
                        Iso.inv_hom_id, Category.comp_id]
                    _ = AX.inv ≫ AX.hom ≫
                          tensorPowMap g (k + 2) := by
                      simp only [Iso.inv_hom_id_assoc]
                    _ = (AX.inv ≫ tensorPowMap g (k + 2)) ≫
                          AY.hom := by
                      rw [Category.assoc, hA]
                rw [moveZeroIso_succ Y k q, moveZeroIso_succ X k q]
                change tensorPowMap g (k + 2) ≫
                      ((AY ≪≫ SY) ≪≫ AY.symm).hom =
                    ((AX ≪≫ SX) ≪≫ AX.symm).hom ≫
                      tensorPowMap g (k + 2)
                simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
                have hAdjacent' :
                    tensorPowMap g (k + 2) ≫
                        SY.hom =
                      SX.hom ≫
                        tensorPowMap g (k + 2) :=
                  hAdjacent k
                have hATail :
                    tensorPowMap g (k + 2) ≫ AY.hom ≫
                          SY.hom ≫ AY.inv =
                      AX.hom ≫ tensorPowMap g (k + 2) ≫
                        SY.hom ≫ AY.inv := by
                  rw [← Category.assoc, hA, Category.assoc]
                have hAdjacentTail :
                    tensorPowMap g (k + 2) ≫
                          SY.hom ≫ AY.inv =
                      SX.hom ≫
                        tensorPowMap g (k + 2) ≫ AY.inv := by
                  rw [← Category.assoc, hAdjacent',
                    Category.assoc]
                calc
                  tensorPowMap g (k + 2) ≫ AY.hom ≫
                        SY.hom ≫ AY.inv =
                    AX.hom ≫ tensorPowMap g (k + 2) ≫
                      SY.hom ≫ AY.inv := hATail
                  _ = AX.hom ≫ SX.hom ≫
                        tensorPowMap g (k + 2) ≫ AY.inv := by
                    rw [hAdjacentTail]
                  _ = AX.hom ≫ SX.hom ≫
                        AX.inv ≫ tensorPowMap g (k + 2) := by
                    rw [hAinv]
        refine ⟨hMsucc, ?_⟩
        intro τ
        let d := Equiv.Perm.decomposeFin τ
        let BX : tensorPowObj X (k + 1) ≅ tensorPowObj X (k + 1) :=
          tensorIso (permutationIsoAux X k d.2) (Iso.refl X)
        let BY : tensorPowObj Y (k + 1) ≅ tensorPowObj Y (k + 1) :=
          tensorIso (permutationIsoAux Y k d.2) (Iso.refl Y)
        let MX : tensorPowObj X (k + 1) ≅ tensorPowObj X (k + 1) :=
          moveZeroIso X (k + 1) d.1
        let MY : tensorPowObj Y (k + 1) ≅ tensorPowObj Y (k + 1) :=
          moveZeroIso Y (k + 1) d.1
        have hB : tensorPowMap g (k + 1) ≫ BY.hom =
            BX.hom ≫ tensorPowMap g (k + 1) := by
          change (tensorPowMap g k ⊗ₘ g) ≫
                ((permutationIsoAux Y k d.2).hom ⊗ₘ 𝟙 Y) =
            ((permutationIsoAux X k d.2).hom ⊗ₘ 𝟙 X) ≫
              (tensorPowMap g k ⊗ₘ g)
          rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hT d.2]
          simp only [Category.comp_id, Category.id_comp]
        have hMove : tensorPowMap g (k + 1) ≫ MY.hom =
            MX.hom ≫ tensorPowMap g (k + 1) := hMsucc d.1
        have hAuxY : (permutationIsoAux Y (k + 1) τ).hom =
            BY.hom ≫ MY.hom := rfl
        have hAuxX : (permutationIsoAux X (k + 1) τ).hom =
            BX.hom ≫ MX.hom := rfl
        rw [hAuxY, hAuxX]
        have hBTail : tensorPowMap g (k + 1) ≫ BY.hom ≫ MY.hom =
            BX.hom ≫ tensorPowMap g (k + 1) ≫ MY.hom := by
          rw [← Category.assoc, hB, Category.assoc]
        calc
          tensorPowMap g (k + 1) ≫ BY.hom ≫ MY.hom =
              BX.hom ≫ tensorPowMap g (k + 1) ≫ MY.hom := hBTail
          _ = BX.hom ≫ MX.hom ≫ tensorPowMap g (k + 1) := by
            rw [hMove]
          _ = (BX.hom ≫ MX.hom) ≫ tensorPowMap g (k + 1) := by
            simp only [Category.assoc]
  exact (hMT m).2 (Fin.revPerm.trans (e.trans Fin.revPerm))

/-- The action of the canonical equivalence induced by an equality is the
corresponding transport of tensor powers. -/
private theorem permutationIso_finCongr {m n : ℕ}
    (X : C) (h : m = n) :
    permutationIso X (finCongr h) =
      eqToIso (congrArg (tensorPowObj X) h) := by
  subst n
  simpa using permutationIso_refl X m

/-- The internal right-to-left action respects the ordered tensor-power
block decomposition. -/
private theorem permutationIsoAux_blockSum (X : C) {m n : ℕ}
    (e : Equiv.Perm (Fin m)) (f : Equiv.Perm (Fin n)) :
    tensorIso (permutationIsoAux X m e)
          (permutationIsoAux X n f) ≪≫ (tensorPowObj_add X m n).symm =
      (tensorPowObj_add X m n).symm ≪≫
        permutationIsoAux X (m + n)
          ((finCongr (Nat.add_comm m n)).trans
            ((finSumFinEquiv.symm.trans
              ((Equiv.sumCongr f e).trans finSumFinEquiv)).trans
                (finCongr (Nat.add_comm n m)))) := by
  let blockPerm {a b : ℕ}
      (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
      Equiv.Perm (Fin (a + b)) :=
    (finCongr (Nat.add_comm a b)).trans
      ((finSumFinEquiv.symm.trans
        ((Equiv.sumCongr h g).trans finSumFinEquiv)).trans
          (finCongr (Nat.add_comm b a)))
  change tensorIso (permutationIsoAux X m e)
          (permutationIsoAux X n f) ≪≫ (tensorPowObj_add X m n).symm =
    (tensorPowObj_add X m n).symm ≪≫ permutationIsoAux X (m + n) (blockPerm e f)
  let lowIndex (a b : ℕ) (p : Fin b) : Fin (a + b) :=
    finCongr (Nat.add_comm b a) (Fin.castAdd a p)
  let highIndex (a b : ℕ) (p : Fin a) : Fin (a + b) :=
    finCongr (Nat.add_comm b a) (Fin.natAdd b p)
  have hBlockLow {a b : ℕ} (g : Equiv.Perm (Fin a))
      (h : Equiv.Perm (Fin b)) (i : Fin b) :
      blockPerm g h (lowIndex a b i) = lowIndex a b (h i) := by
    apply Fin.ext
    simp [blockPerm, lowIndex, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_apply_left]
  have hBlockHigh {a b : ℕ} (g : Equiv.Perm (Fin a))
      (h : Equiv.Perm (Fin b)) (i : Fin a) :
      blockPerm g h (highIndex a b i) = highIndex a b (g i) := by
    apply Fin.ext
    simp [blockPerm, highIndex, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_apply_right]
  have hIndexCases {a b : ℕ} (i : Fin (a + b)) :
      (∃ x : Fin b, i = lowIndex a b x) ∨
        (∃ y : Fin a, i = highIndex a b y) := by
    let z := finSumFinEquiv.symm (finCongr (Nat.add_comm a b) i)
    rcases hz : z with x | y
    · left
      refine ⟨x, ?_⟩
      have hz' : finSumFinEquiv.symm
          (finCongr (Nat.add_comm a b) i) = Sum.inl x := by
        simpa only [z] using hz
      have h := congrArg finSumFinEquiv hz'
      rw [finSumFinEquiv.apply_symm_apply,
        finSumFinEquiv_apply_left] at h
      apply Fin.ext
      simpa only [lowIndex, finCongr_apply_coe,
        Fin.val_castAdd] using congrArg Fin.val h
    · right
      refine ⟨y, ?_⟩
      have hz' : finSumFinEquiv.symm
          (finCongr (Nat.add_comm a b) i) = Sum.inr y := by
        simpa only [z] using hz
      have h := congrArg finSumFinEquiv hz'
      rw [finSumFinEquiv.apply_symm_apply,
        finSumFinEquiv_apply_right] at h
      apply Fin.ext
      simpa only [highIndex, finCongr_apply_coe,
        Fin.val_natAdd] using congrArg Fin.val h
  have hBlockDecompose {a b : ℕ} (g : Equiv.Perm (Fin a))
      (h : Equiv.Perm (Fin (b + 1))) :
      let d := Equiv.Perm.decomposeFin h
      Equiv.Perm.decomposeFin (blockPerm g h) =
        (lowIndex a (b + 1) d.1, blockPerm g d.2) := by
    dsimp only
    let d := Equiv.Perm.decomposeFin h
    have hLowZero : lowIndex a (b + 1) (0 : Fin (b + 1)) = 0 := rfl
    have hLowSucc (x : Fin b) :
        lowIndex a (b + 1) x.succ = (lowIndex a b x).succ := rfl
    have hh : Equiv.Perm.decomposeFin.symm d = h :=
      Equiv.symm_apply_apply _ _
    have hh0 : h 0 = d.1 := by
      rw [← hh]
      exact Equiv.Perm.decomposeFin_symm_apply_zero d.1 d.2
    have hhsucc (x : Fin b) :
        h x.succ = Equiv.swap 0 d.1 (d.2 x).succ := by
      rw [← hh]
      exact Equiv.Perm.decomposeFin_symm_apply_succ d.2 d.1 x
    apply Equiv.Perm.decomposeFin.symm.injective
    rw [Equiv.symm_apply_apply]
    ext x
    refine Fin.cases ?_ (fun i => ?_) x
    · rw [← hLowZero, hBlockLow, hh0, hLowZero]
      simpa only using congrArg Fin.val
        (Equiv.Perm.decomposeFin_symm_apply_zero
          (lowIndex a (b + 1) d.1) (blockPerm g d.2)).symm
    · rcases hIndexCases i with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · rw [← hLowSucc, hBlockLow, hhsucc]
        rw [hLowSucc, Equiv.Perm.decomposeFin_symm_apply_succ,
          hBlockLow]
        have hlowInj : Function.Injective
            (lowIndex a (b + 1)) := by
          intro x y hxy
          apply Fin.ext
          simpa only [lowIndex, finCongr_apply_coe,
            Fin.val_castAdd] using congrArg Fin.val hxy
        have hmap := Function.Injective.map_swap hlowInj
          (0 : Fin (b + 1)) d.1 (d.2 x).succ
        simpa only [hLowZero, hLowSucc] using congrArg Fin.val hmap
      · have hHighSucc (z : Fin a) :
            (highIndex a b z).succ = highIndex a (b + 1) z := by
          apply Fin.ext
          simp only [highIndex, Fin.val_succ, finCongr_apply_coe,
            Fin.val_natAdd]
          omega
        rw [hHighSucc y, hBlockHigh]
        rw [← hHighSucc y,
          Equiv.Perm.decomposeFin_symm_apply_succ,
          hBlockHigh, hHighSucc (g y)]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro hz
          have hv := congrArg Fin.val hz
          change b + 1 + (g y).val = 0 at hv
          omega
        · intro hz
          have hv := congrArg Fin.val hz
          change b + 1 + (g y).val = d.1.val at hv
          omega
  have hConjNatural {A B : C} (u v : A ≅ A) (u' v' : B ≅ B)
      (K : A ≅ B) (hu : u ≪≫ K = K ≪≫ u')
      (hv : v ≪≫ K = K ≪≫ v') :
      ((u ≪≫ v) ≪≫ u.symm) ≪≫ K =
        K ≪≫ ((u' ≪≫ v') ≪≫ u'.symm) := by
    have huInv : u.symm ≪≫ K = K ≪≫ u'.symm := by
      calc
        u.symm ≪≫ K =
            ((u.symm ≪≫ K) ≪≫ u') ≪≫ u'.symm := by
          simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
        _ = (u.symm ≪≫ (K ≪≫ u')) ≪≫ u'.symm := by
          simp only [Iso.trans_assoc]
        _ = (u.symm ≪≫ (u ≪≫ K)) ≪≫ u'.symm := by rw [hu]
        _ = K ≪≫ u'.symm := by
          simp only [Iso.symm_self_id_assoc]
    calc
      ((u ≪≫ v) ≪≫ u.symm) ≪≫ K =
          u ≪≫ v ≪≫ u.symm ≪≫ K := by
        simp only [Iso.trans_assoc]
      _ = u ≪≫ v ≪≫ K ≪≫ u'.symm := by rw [huInv]
      _ = u ≪≫ K ≪≫ v' ≪≫ u'.symm := by
        have h := congrArg (fun z => u ≪≫ z ≪≫ u'.symm) hv
        simpa only [Iso.trans_assoc] using h
      _ = K ≪≫ u' ≪≫ v' ≪≫ u'.symm := by
        have h := congrArg (fun z => z ≪≫ v' ≪≫ u'.symm) hu
        simpa only [Iso.trans_assoc] using h
      _ = K ≪≫ ((u' ≪≫ v') ≪≫ u'.symm) := by
        simp only [Iso.trans_assoc]
  have hProductNatural {A B : C} (u v : A ≅ A) (u' v' : B ≅ B)
      (K : A ≅ B) (hu : u ≪≫ K = K ≪≫ u')
      (hv : v ≪≫ K = K ≪≫ v') :
      (u ≪≫ v) ≪≫ K = K ≪≫ (u' ≪≫ v') := by
    calc
      (u ≪≫ v) ≪≫ K = u ≪≫ (v ≪≫ K) :=
        Iso.trans_assoc _ _ _
      _ = u ≪≫ (K ≪≫ v') :=
        congrArg (fun z => u ≪≫ z) hv
      _ = (u ≪≫ K) ≪≫ v' :=
        (Iso.trans_assoc _ _ _).symm
      _ = (K ≪≫ u') ≪≫ v' :=
        congrArg (fun z => z ≪≫ v') hu
      _ = K ≪≫ (u' ≪≫ v') := Iso.trans_assoc _ _ _
  have hHorizontalNatural {A B D : C} (u : A ≅ A)
      (v : B ≅ B) (w : D ≅ D) (K : A ≅ B) (L : B ≅ D)
      (hK : u ≪≫ K = K ≪≫ v) (hL : v ≪≫ L = L ≪≫ w) :
      u ≪≫ (K ≪≫ L) = (K ≪≫ L) ≪≫ w := by
    calc
      u ≪≫ (K ≪≫ L) = (u ≪≫ K) ≪≫ L :=
        (Iso.trans_assoc _ _ _).symm
      _ = (K ≪≫ v) ≪≫ L :=
        congrArg (fun z => z ≪≫ L) hK
      _ = K ≪≫ (v ≪≫ L) := Iso.trans_assoc _ _ _
      _ = K ≪≫ (L ≪≫ w) :=
        congrArg (fun z => K ≪≫ z) hL
      _ = (K ≪≫ L) ≪≫ w :=
        (Iso.trans_assoc _ _ _).symm
  have hMoveZero (r : ℕ) :
      moveZeroIso X (r + 1) (0 : Fin (r + 1)) = Iso.refl _ := by
    cases r <;> apply Iso.ext <;>
      simp only [Nat.reduceAdd, tensorPowObj_succ, tensorPowObj_zero,
        moveZeroIso, Iso.refl_hom, Fin.cases_zero]
  have hMoveZeroOfPos (r : ℕ) (hr : 0 < r) :
      moveZeroIso X r (⟨0, hr⟩ : Fin r) = Iso.refl _ := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    exact hMoveZero s
  have hMoveBlock : ∀ (a b : ℕ) (p : Fin (b + 1)),
      tensorIso (Iso.refl (tensorPowObj X a))
            (moveZeroIso X (b + 1) p) ≪≫
          (tensorPowObj_add X a (b + 1)).symm =
        (tensorPowObj_add X a (b + 1)).symm ≪≫
          moveZeroIso X (a + (b + 1)) (lowIndex a (b + 1) p) := by
    intro a b
    induction b generalizing a with
    | zero =>
        intro p
        have hp : p = 0 := Fin.eq_zero p
        subst p
        have hlow : lowIndex a 1 0 = 0 := by
          apply Fin.ext
          rfl
        rw [hlow, hMoveZero, hMoveZero]
        have htr : tensorIso (Iso.refl (tensorPowObj X a))
            (Iso.refl (tensorPowObj X 1)) = Iso.refl _ := by
          apply Iso.ext
          exact id_tensorHom_id _ _
        rw [htr, Iso.refl_trans, Iso.trans_refl]
    | succ b ih =>
        intro p
        refine Fin.cases ?_ (fun q => ?_) p
        · have hlow : lowIndex a (b + 1 + 1) 0 = 0 := by
            apply Fin.ext
            rfl
          rw [hlow, hMoveZero]
          have hz : moveZeroIso X (a + (b + 1 + 1))
              (0 : Fin (a + (b + 1 + 1))) = Iso.refl _ :=
            hMoveZeroOfPos (a + (b + 1 + 1)) (by omega)
          rw [hz]
          have htr : tensorIso (Iso.refl (tensorPowObj X a))
              (Iso.refl (tensorPowObj X (b + 1 + 1))) = Iso.refl _ := by
            apply Iso.ext
            exact id_tensorHom_id _ _
          rw [htr, Iso.refl_trans, Iso.trans_refl]
        · let M : tensorPowObj X b ⊗ X ≅ tensorPowObj X b ⊗ X :=
            moveZeroIso X (b + 1) q
          let M' : tensorPowObj X (a + b) ⊗ X ≅
              tensorPowObj X (a + b) ⊗ X :=
            moveZeroIso X (a + (b + 1)) (lowIndex a (b + 1) q)
          let B1 : tensorPowObj X a ⊗ (tensorPowObj X b ⊗ X) ≅
              tensorPowObj X (a + b) ⊗ X :=
            (tensorPowObj_add X a (b + 1)).symm
          let B2 : tensorPowObj X a ⊗ ((tensorPowObj X b ⊗ X) ⊗ X) ≅
              (tensorPowObj X (a + b) ⊗ X) ⊗ X :=
            (tensorPowObj_add X a (b + 2)).symm
          have ih' : tensorIso (Iso.refl (tensorPowObj X a)) M ≪≫ B1 =
              B1 ≪≫ M' := ih a q
          have hAdd : B2 =
              (associator (tensorPowObj X a)
                  (tensorPowObj X b ⊗ X) X).symm ≪≫
                tensorIso B1 (Iso.refl X) := by
            rfl
          have hLift :
              tensorIso (Iso.refl (tensorPowObj X a))
                    (tensorIso M (Iso.refl X)) ≪≫ B2 =
                B2 ≪≫ tensorIso M' (Iso.refl X) := by
            apply Iso.ext
            have hAddHom := congrArg Iso.hom hAdd
            simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
              Iso.symm_hom] at hAddHom
            have ihh := congrArg Iso.hom ih'
            simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom] at ihh
            simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom] at ⊢
            rw [hAddHom]
            rw [← Category.assoc]
            rw [associator_inv_naturality]
            simp only [Category.assoc]
            rw [tensorHom_comp_tensorHom]
            rw [ihh]
            rw [tensorHom_comp_tensorHom]
          let B0 := (tensorPowObj_add X a b).symm
          let r : tensorPowObj X a ⊗ ((tensorPowObj X b ⊗ X) ⊗ X) ≅
              ((tensorPowObj X a ⊗ tensorPowObj X b) ⊗ X) ⊗ X :=
            (associator (tensorPowObj X a)
                (tensorPowObj X b ⊗ X) X).symm ≪≫
              whiskerRightIso
                ((associator (tensorPowObj X a)
                  (tensorPowObj X b) X).symm) X
          let T := tensorIso (tensorIso B0 (Iso.refl X)) (Iso.refl X)
          have h1 : B1 =
              (associator (tensorPowObj X a) (tensorPowObj X b) X).symm ≪≫
                tensorIso B0 (Iso.refl X) := by
            rfl
          have h2 : B2 =
              (associator (tensorPowObj X a)
                  (tensorPowObj X b ⊗ X) X).symm ≪≫
                tensorIso B1 (Iso.refl X) := by
            rfl
          have hFactor : B2 = r ≪≫ T := by
            apply Iso.ext
            have h1h := congrArg Iso.hom h1
            have h2h := congrArg Iso.hom h2
            simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
              Iso.refl_hom] at h1h h2h
            simp only [Iso.trans_hom]
            rw [h2h, h1h]
            have hTensor :
                (((associator (tensorPowObj X a)
                      (tensorPowObj X b) X).inv ≫
                    (B0.hom ⊗ₘ 𝟙 X)) ⊗ₘ 𝟙 X) =
                  (((associator (tensorPowObj X a)
                        (tensorPowObj X b) X).inv ⊗ₘ 𝟙 X) ≫
                    ((B0.hom ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X)) := by
              simpa only [Category.comp_id] using
                (tensorHom_comp_tensorHom
                  (associator (tensorPowObj X a)
                    (tensorPowObj X b) X).inv (𝟙 X)
                  (B0.hom ⊗ₘ 𝟙 X) (𝟙 X)).symm
            rw [hTensor]
            dsimp only [r, T]
            simp only [Iso.trans_hom, whiskerRightIso_hom,
              tensorIso_hom, Iso.refl_hom, tensorHom_id, Category.assoc]
            rfl
          have hAdjacentNatural {A D : C} (g : A ⟶ D) :
              ((g ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) ≫
                  ((associator D X X).hom ≫
                    (D ◁ (β_ X X).hom) ≫
                    (associator D X X).inv) =
                ((associator A X X).hom ≫
                    (A ◁ (β_ X X).hom) ≫
                    (associator A X X).inv) ≫
                  ((g ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) := by
            have hMid :
                (g ⊗ₘ (𝟙 X ⊗ₘ 𝟙 X)) ≫
                    (D ◁ (β_ X X).hom) =
                  (A ◁ (β_ X X).hom) ≫
                    (g ⊗ₘ (𝟙 X ⊗ₘ 𝟙 X)) := by
              rw [← id_tensorHom, ← id_tensorHom]
              rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
              rw [id_tensorHom_id]
              simp only [Category.comp_id, Category.id_comp]
            simp only [Category.assoc]
            slice_lhs 1 2 => rw [associator_naturality]
            slice_lhs 2 3 => rw [hMid]
            slice_lhs 3 4 => rw [associator_inv_naturality]
          let A := tensorPowObj X a
          let D := tensorPowObj X b
          let s (Y : C) : ((Y ⊗ X) ⊗ X) ≅ ((Y ⊗ X) ⊗ X) :=
            (associator Y X X) ≪≫
              whiskerLeftIso Y (β_ X X) ≪≫
                (associator Y X X).symm
          let qIso : (((A ⊗ D) ⊗ X) ⊗ X) ≅
              A ⊗ (D ⊗ (X ⊗ X)) :=
            (associator (A ⊗ D) X X) ≪≫
              associator A D (X ⊗ X)
          let b2 : D ⊗ (X ⊗ X) ≅ D ⊗ (X ⊗ X) :=
            whiskerLeftIso D (β_ X X)
          let Q : (((A ⊗ D) ⊗ X) ⊗ X) ≅
              (((A ⊗ D) ⊗ X) ⊗ X) :=
            qIso ≪≫ whiskerLeftIso A b2 ≪≫ qIso.symm
          have hRQ : r ≪≫ qIso = whiskerLeftIso A (associator D X X) := by
            apply Iso.ext
            simp only [r, qIso, Iso.trans_hom, Iso.symm_hom,
              whiskerRightIso_hom, whiskerLeftIso_hom, Category.assoc]
            slice_lhs 1 3 => rw [pentagon_inv_inv_hom_hom_inv]
            simp only [Category.assoc, cancelIso, Category.comp_id]
            rfl
          have hQ : Q = s (A ⊗ D) := by
            apply Iso.ext
            simp only [Q, qIso, b2, s, Iso.trans_symm,
              Iso.trans_assoc, Iso.trans_hom, whiskerLeftIso_hom,
              Iso.symm_hom, tensor_whiskerLeft, Category.assoc]
          have hMiddle :
              tensorIso (Iso.refl A) (s D) ≪≫
                  whiskerLeftIso A (associator D X X) =
                whiskerLeftIso A (associator D X X) ≪≫
                  whiskerLeftIso A b2 := by
            apply Iso.ext
            simp only [s, b2, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
              whiskerLeftIso_hom, Iso.symm_hom]
            rw [id_tensorHom]
            simp only [← whiskerLeft_comp, Category.assoc,
              Iso.inv_hom_id, Category.comp_id]
          have hStruct :
              tensorIso (Iso.refl A) (s D) ≪≫ r = r ≪≫ s (A ⊗ D) := by
            calc
              tensorIso (Iso.refl A) (s D) ≪≫ r =
                  (((tensorIso (Iso.refl A) (s D) ≪≫ r) ≪≫
                    qIso) ≪≫ qIso.symm) := by
                simp only [Iso.trans_assoc, Iso.self_symm_id,
                  Iso.trans_refl]
              _ = ((tensorIso (Iso.refl A) (s D) ≪≫
                    whiskerLeftIso A (associator D X X)) ≪≫
                    qIso.symm) := by
                  rw [Iso.trans_assoc (tensorIso (Iso.refl A) (s D)) r qIso,
                    hRQ]
              _ = ((whiskerLeftIso A (associator D X X) ≪≫
                    whiskerLeftIso A b2) ≪≫ qIso.symm) := by
                  rw [hMiddle]
              _ = (((r ≪≫ qIso) ≪≫ whiskerLeftIso A b2) ≪≫
                    qIso.symm) := by rw [hRQ]
              _ = r ≪≫ Q := by simp only [Iso.trans_assoc, Q]
              _ = r ≪≫ s (A ⊗ D) := by rw [hQ]
          have hNatIso : s (A ⊗ D) ≪≫ T =
              T ≪≫ s (tensorPowObj X (a + b)) := by
            apply Iso.ext
            change
              ((associator (A ⊗ D) X X).hom ≫
                  ((A ⊗ D) ◁ (β_ X X).hom) ≫
                  (associator (A ⊗ D) X X).inv) ≫
                    ((B0.hom ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) =
                ((B0.hom ⊗ₘ 𝟙 X) ⊗ₘ 𝟙 X) ≫
                  ((associator (tensorPowObj X (a + b)) X X).hom ≫
                    (tensorPowObj X (a + b) ◁ (β_ X X).hom) ≫
                    (associator (tensorPowObj X (a + b)) X X).inv)
            exact (hAdjacentNatural B0.hom).symm
          have hAdjacent :
              tensorIso (Iso.refl (tensorPowObj X a))
                    (adjacentSwapIso X b) ≪≫ B2 =
                B2 ≪≫ adjacentSwapIso X (a + b) := by
            have hs : adjacentSwapIso X b = s D := rfl
            have hs' : adjacentSwapIso X (a + b) =
                s (tensorPowObj X (a + b)) := rfl
            rw [hs, hs']
            exact (congrArg
              (fun z => tensorIso (Iso.refl A) (s D) ≪≫ z)
              hFactor).trans
                ((hHorizontalNatural
                  (tensorIso (Iso.refl A) (s D))
                  (s (A ⊗ D)) (s (tensorPowObj X (a + b)))
                  r T hStruct hNatIso).trans
                    (congrArg
                      (fun z => z ≪≫ s (tensorPowObj X (a + b)))
                      hFactor.symm))
          let E := tensorIso M (Iso.refl X)
          let E' := tensorIso M' (Iso.refl X)
          let S : (tensorPowObj X b ⊗ X) ⊗ X ≅
              (tensorPowObj X b ⊗ X) ⊗ X := adjacentSwapIso X b
          let S' : (tensorPowObj X (a + b) ⊗ X) ⊗ X ≅
              (tensorPowObj X (a + b) ⊗ X) ⊗ X :=
            adjacentSwapIso X (a + b)
          have hE : tensorIso (Iso.refl (tensorPowObj X a)) E ≪≫ B2 =
              B2 ≪≫ E' := hLift
          have hS : tensorIso (Iso.refl (tensorPowObj X a)) S ≪≫ B2 =
              B2 ≪≫ S' := hAdjacent
          have hEInv :
              tensorIso (Iso.refl (tensorPowObj X a)) E.symm ≪≫ B2 =
                B2 ≪≫ E'.symm := by
            have hLiftSymm :
                tensorIso (Iso.refl (tensorPowObj X a)) E.symm =
                  (tensorIso (Iso.refl (tensorPowObj X a)) E).symm := by
              rfl
            calc
              tensorIso (Iso.refl (tensorPowObj X a)) E.symm ≪≫ B2 =
                  (tensorIso (Iso.refl (tensorPowObj X a)) E.symm ≪≫
                    (B2 ≪≫ E')) ≪≫ E'.symm := by
                simp only [Iso.trans_assoc, Iso.self_symm_id,
                  Iso.trans_refl]
              _ = (tensorIso (Iso.refl (tensorPowObj X a)) E.symm ≪≫
                    (tensorIso (Iso.refl (tensorPowObj X a)) E ≪≫ B2)) ≪≫
                  E'.symm := by rw [← hE]
              _ = B2 ≪≫ E'.symm := by
                rw [hLiftSymm]
                simp only [Iso.symm_self_id_assoc]
          have hTensorTrans (U V :
              (tensorPowObj X b ⊗ X) ⊗ X ≅
                (tensorPowObj X b ⊗ X) ⊗ X) :
              tensorIso (Iso.refl (tensorPowObj X a)) (U ≪≫ V) =
                tensorIso (Iso.refl (tensorPowObj X a)) U ≪≫
                  tensorIso (Iso.refl (tensorPowObj X a)) V := by
            apply Iso.ext
            change (𝟙 (tensorPowObj X a) ⊗ₘ (U.hom ≫ V.hom)) =
              (𝟙 (tensorPowObj X a) ⊗ₘ U.hom) ≫
                (𝟙 (tensorPowObj X a) ⊗ₘ V.hom)
            simpa only [Category.id_comp] using
              (tensorHom_comp_tensorHom (𝟙 (tensorPowObj X a)) U.hom
                (𝟙 (tensorPowObj X a)) V.hom).symm
          have hLowSucc : lowIndex a (b + 2) q.succ =
              (lowIndex a (b + 1) q).succ := by
            apply Fin.ext
            rfl
          rw [hLowSucc]
          have hSourceMove : moveZeroIso X (b + 2) q.succ =
              (E ≪≫ S) ≪≫ E.symm := by
            dsimp only [E, S, M]
            exact moveZeroIso_succ X b q
          have hTargetMove :
              moveZeroIso X (a + (b + 2))
                  (lowIndex a (b + 1) q).succ =
                (E' ≪≫ S') ≪≫ E'.symm := by
            dsimp only [E', S', M']
            exact moveZeroIso_succ X (a + b) (lowIndex a (b + 1) q)
          rw [hSourceMove, hTargetMove]
          have hFactorMove :
              tensorIso (Iso.refl (tensorPowObj X a))
                  ((E ≪≫ S) ≪≫ E.symm) =
                (tensorIso (Iso.refl (tensorPowObj X a)) E ≪≫
                  tensorIso (Iso.refl (tensorPowObj X a))
                    S) ≪≫
                  tensorIso (Iso.refl (tensorPowObj X a)) E.symm := by
            exact (hTensorTrans (E ≪≫ S) E.symm).trans
              (congrArg
                (fun z => z ≪≫
                  tensorIso (Iso.refl (tensorPowObj X a)) E.symm)
                (hTensorTrans E S))
          have hFirst := hProductNatural
            (tensorIso (Iso.refl (tensorPowObj X a)) E)
            (tensorIso (Iso.refl (tensorPowObj X a)) S) E' S' B2 hE hS
          have hAll := hProductNatural
            (tensorIso (Iso.refl (tensorPowObj X a)) E ≪≫
              tensorIso (Iso.refl (tensorPowObj X a)) S)
            (tensorIso (Iso.refl (tensorPowObj X a)) E.symm)
            (E' ≪≫ S') E'.symm
            B2 hFirst hEInv
          exact
            (congrArg (fun z => z ≪≫ B2) hFactorMove).trans hAll
  induction n generalizing m with
  | zero =>
      have hf : f = Equiv.refl (Fin 0) := Subsingleton.elim _ _
      subst f
      have hblock : blockPerm e (Equiv.refl (Fin 0)) = e := by
        apply Equiv.ext
        intro i
        rcases hIndexCases i with ⟨j, hj⟩ | ⟨j, hj⟩
        · exact Fin.elim0 j
        · subst i
          rw [hBlockHigh]
          have hhigh (z : Fin m) : highIndex m 0 z = z := by
            apply Fin.ext
            simp only [highIndex, finCongr_apply_coe,
              Fin.val_natAdd, Nat.zero_add]
          rw [hhigh, hhigh]
      rw [permutationIsoAux_refl, hblock]
      apply Iso.ext
      change
        ((permutationIsoAux X m e).hom ⊗ₘ 𝟙 (tensorPowObj X 0)) ≫
            ((tensorPowObj_add X m 0).symm).hom =
          ((tensorPowObj_add X m 0).symm).hom ≫ (permutationIsoAux X m e).hom
      change
        ((permutationIsoAux X m e).hom ⊗ₘ 𝟙 (tensorPowObj X 0)) ≫
            (rightUnitor (tensorPowObj X m)).hom =
          (rightUnitor (tensorPowObj X m)).hom ≫
            (permutationIsoAux X m e).hom
      dsimp only [tensorPowObj]
      rw [tensorHom_id]
      exact rightUnitor_naturality (permutationIsoAux X m e).hom
  | succ n ih =>
      let d := Equiv.Perm.decomposeFin f
      have hdec : Equiv.Perm.decomposeFin
            (blockPerm (a := m) (b := n + 1) e f) =
          (lowIndex m (n + 1) d.1,
            blockPerm (a := m) (b := n) e d.2) :=
        hBlockDecompose e f
      have hf : permutationIsoAux X (n + 1) f =
          tensorIso (permutationIsoAux X n d.2) (Iso.refl X) ≪≫
            moveZeroIso X (n + 1) d.1 := by
        rfl
      have htotal :
          permutationIsoAux X (m + (n + 1))
              (blockPerm (a := m) (b := n + 1) e f) =
            tensorIso
                (permutationIsoAux X (m + n)
                  (blockPerm (a := m) (b := n) e d.2))
                (Iso.refl X) ≪≫
              moveZeroIso X (m + (n + 1))
                (lowIndex m (n + 1) d.1) := by
        change permutationIsoAux X ((m + n) + 1)
          (blockPerm (a := m) (b := n + 1) e f) = _
        rw [permutationIsoAux, hdec]
        rfl
      have hBlockSucc : (tensorPowObj_add X m (n + 1)).symm =
          (associator (tensorPowObj X m) (tensorPowObj X n) X).symm ≪≫
            tensorIso ((tensorPowObj_add X m n).symm) (Iso.refl X) := by
        rfl
      have hTensorFactor :
          tensorIso (permutationIsoAux X m e)
              (tensorIso (permutationIsoAux X n d.2) (Iso.refl X) ≪≫
                moveZeroIso X (n + 1) d.1) =
            tensorIso (permutationIsoAux X m e)
                (tensorIso (permutationIsoAux X n d.2) (Iso.refl X)) ≪≫
              tensorIso (Iso.refl (tensorPowObj X m))
                (moveZeroIso X (n + 1) d.1) := by
        apply Iso.ext
        calc
          (tensorIso (permutationIsoAux X m e)
              (tensorIso (permutationIsoAux X n d.2) (Iso.refl X) ≪≫
                moveZeroIso X (n + 1) d.1)).hom =
            (permutationIsoAux X m e).hom ⊗ₘ
              (((permutationIsoAux X n d.2).hom ⊗ₘ 𝟙 X) ≫
                (moveZeroIso X (n + 1) d.1).hom) := rfl
          _ = (((permutationIsoAux X m e).hom ≫
                  𝟙 (tensorPowObj X m)) ⊗ₘ
                (((permutationIsoAux X n d.2).hom ⊗ₘ 𝟙 X) ≫
                  (moveZeroIso X (n + 1) d.1).hom)) := by
                rw [Category.comp_id]
          _ = (((permutationIsoAux X m e).hom ⊗ₘ
                  ((permutationIsoAux X n d.2).hom ⊗ₘ 𝟙 X)) ≫
                (𝟙 (tensorPowObj X m) ⊗ₘ
                  (moveZeroIso X (n + 1) d.1).hom)) :=
                (tensorHom_comp_tensorHom _ _ _ _).symm
          _ = ((tensorIso (permutationIsoAux X m e)
                  (tensorIso (permutationIsoAux X n d.2) (Iso.refl X)) ≪≫
                tensorIso (Iso.refl (tensorPowObj X m))
                  (moveZeroIso X (n + 1) d.1)).hom) := rfl
      have hAssoc :
          tensorIso (permutationIsoAux X m e)
                (tensorIso (permutationIsoAux X n d.2) (Iso.refl X)) ≪≫
              (associator (tensorPowObj X m) (tensorPowObj X n) X).symm =
            (associator (tensorPowObj X m) (tensorPowObj X n) X).symm ≪≫
              tensorIso
                (tensorIso (permutationIsoAux X m e)
                  (permutationIsoAux X n d.2))
                (Iso.refl X) := by
        apply Iso.ext
        exact associator_inv_naturality
          (permutationIsoAux X m e).hom
          (permutationIsoAux X n d.2).hom (𝟙 X)
      have hLift :
          tensorIso
                (tensorIso (permutationIsoAux X m e)
                  (permutationIsoAux X n d.2))
                (Iso.refl X) ≪≫
              tensorIso ((tensorPowObj_add X m n).symm) (Iso.refl X) =
            tensorIso ((tensorPowObj_add X m n).symm) (Iso.refl X) ≪≫
              tensorIso
                (permutationIsoAux X (m + n)
                  (blockPerm (a := m) (b := n) e d.2))
                (Iso.refl X) := by
        have hi := congrArg Iso.hom (ih e d.2)
        simp only [Iso.trans_hom] at hi
        apply Iso.ext
        change
          (((permutationIsoAux X m e).hom ⊗ₘ
              (permutationIsoAux X n d.2).hom) ⊗ₘ 𝟙 X) ≫
                (((tensorPowObj_add X m n).symm).hom ⊗ₘ 𝟙 X) =
            (((tensorPowObj_add X m n).symm).hom ⊗ₘ 𝟙 X) ≫
              ((permutationIsoAux X (m + n)
                (blockPerm (a := m) (b := n) e d.2)).hom ⊗ₘ 𝟙 X)
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
        simp only [Category.comp_id]
        exact congrArg (fun z => z ⊗ₘ 𝟙 X) hi
      have hCore :
          tensorIso (permutationIsoAux X m e)
                (tensorIso (permutationIsoAux X n d.2) (Iso.refl X)) ≪≫
              (tensorPowObj_add X m (n + 1)).symm =
            (tensorPowObj_add X m (n + 1)).symm ≪≫
              tensorIso
                (permutationIsoAux X (m + n)
                  (blockPerm (a := m) (b := n) e d.2))
                (Iso.refl X) := by
        let F₁ := tensorIso (permutationIsoAux X m e)
          (tensorIso (permutationIsoAux X n d.2) (Iso.refl X))
        let R := (associator
          (tensorPowObj X m) (tensorPowObj X n) X).symm
        let T := tensorIso ((tensorPowObj_add X m n).symm) (Iso.refl X)
        let F₂ := tensorIso
          (tensorIso (permutationIsoAux X m e)
            (permutationIsoAux X n d.2)) (Iso.refl X)
        let F₃ := tensorIso
          (permutationIsoAux X (m + n)
            (blockPerm (a := m) (b := n) e d.2)) (Iso.refl X)
        change F₁ ≪≫ (tensorPowObj_add X m (n + 1)).symm =
          (tensorPowObj_add X m (n + 1)).symm ≪≫ F₃
        have hB : (tensorPowObj_add X m (n + 1)).symm = R ≪≫ T := hBlockSucc
        have hA : F₁ ≪≫ R = R ≪≫ F₂ := hAssoc
        have hL : F₂ ≪≫ T = T ≪≫ F₃ := hLift
        exact (congrArg (fun z => F₁ ≪≫ z) hB).trans
          ((hHorizontalNatural F₁ F₂ F₃ R T hA hL).trans
            (congrArg (fun z => z ≪≫ F₃) hB.symm))
      rw [hf, htotal]
      have hMove := hMoveBlock m n d.1
      have hProduct := hProductNatural
        (tensorIso (permutationIsoAux X m e)
          (tensorIso (permutationIsoAux X n d.2) (Iso.refl X)))
        (tensorIso (Iso.refl (tensorPowObj X m))
          (moveZeroIso X (n + 1) d.1))
        (tensorIso
          (permutationIsoAux X (m + n)
            (blockPerm (a := m) (b := n) e d.2))
          (Iso.refl X))
        (moveZeroIso X (m + (n + 1))
          (lowIndex m (n + 1) d.1))
        ((tensorPowObj_add X m (n + 1)).symm) hCore hMove
      exact
        (congrArg (fun z => z ≪≫ (tensorPowObj_add X m (n + 1)).symm)
          hTensorFactor).trans hProduct

/-- Block-sum naturality of the symmetric tensor-power action. -/
theorem blockSumIso_natural
    {m m' n n' : ℕ} (X : C)
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') :
    tensorIso (permutationIso X e) (permutationIso X f) ≪≫
        (tensorPowObj_add X m' n').symm =
      (tensorPowObj_add X m n).symm ≪≫
        permutationIso X
          (finSumFinEquiv.symm.trans
            ((Equiv.sumCongr e f).trans finSumFinEquiv)) := by
  have hm : m = m' := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hn : n = n' := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f
  subst m'
  subst n'
  let blockEquiv {a a' b b' : ℕ}
      (g : Fin a ≃ Fin a') (h : Fin b ≃ Fin b') :
      Fin (a + b) ≃ Fin (a' + b') :=
    finSumFinEquiv.symm.trans
      ((Equiv.sumCongr g h).trans finSumFinEquiv)
  let revAction {a b : ℕ} (g : Fin a ≃ Fin b) : Fin a ≃ Fin b :=
    Fin.revPerm.trans (g.trans Fin.revPerm)
  let internalBlockAux {a a' b b' : ℕ}
      (g : Fin a ≃ Fin a') (h : Fin b ≃ Fin b') :
      Fin (a + b) ≃ Fin (a' + b') :=
    (finCongr (Nat.add_comm a b)).trans
      ((blockEquiv h g).trans (finCongr (Nat.add_comm b' a')))
  have hrev : revAction (blockEquiv e f) =
      internalBlockAux (revAction e) (revAction f) := by
    apply Equiv.ext
    intro i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective i
    refine Fin.addCases (m := m) (n := n) (fun a => ?_) (fun b => ?_) j
    · have hr :
          (finCongr (Nat.add_comm m n)) (Fin.castAdd n a).rev =
            Fin.natAdd n a.rev := by
        apply Fin.ext
        simp [Fin.rev]
        omega
      simp only [revAction, internalBlockAux, blockEquiv,
        Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
      rw [hr]
      apply Fin.ext
      simp
      omega
    · have hr :
          (finCongr (Nat.add_comm m n)) (Fin.natAdd m b).rev =
            Fin.castAdd m b.rev := by
        apply Fin.ext
        simp [Fin.rev]
        omega
      simp only [revAction, internalBlockAux, blockEquiv,
        Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
      rw [hr]
      apply Fin.ext
      simp
      omega
  have h := permutationIsoAux_blockSum X (revAction e) (revAction f)
  change
    tensorIso (permutationIsoAux X m (revAction e))
          (permutationIsoAux X n (revAction f)) ≪≫
        (tensorPowObj_add X m n).symm =
      (tensorPowObj_add X m n).symm ≪≫
        permutationIsoAux X (m + n)
          (internalBlockAux (revAction e) (revAction f)) at h
  rw [← hrev] at h
  simpa only [permutationIso, revAction, blockEquiv] using h

/-- The literal ordered right-successor block flip factors through the two original flips. -/
theorem finAddFlip_succ_right_factor : ∀ a b : ℕ,
    (finAddFlip : Fin (a + (b + 1)) ≃ Fin ((b + 1) + a)) =
      (finSumFinEquiv.symm.trans
        ((Equiv.sumCongr
          (finAddFlip : Fin (a + b) ≃ Fin (b + a))
          (Equiv.refl (Fin 1))).trans finSumFinEquiv)).trans
        ((finSumFinEquiv.symm.trans
          ((Equiv.sumCongr (Equiv.refl (Fin b))
            (finAddFlip : Fin (a + 1) ≃ Fin (1 + a))).trans
              finSumFinEquiv)).trans
          (finCongr (Nat.add_assoc b 1 a).symm)) := by
  intro a b
  let blockEquiv {p p' q q' : ℕ}
      (e : Fin p ≃ Fin p') (f : Fin q ≃ Fin q') :
      Fin (p + q) ≃ Fin (p' + q') :=
    finSumFinEquiv.symm.trans
      ((Equiv.sumCongr e f).trans finSumFinEquiv)
  have blockEquiv_apply_left :
      ∀ {p p' q q' : ℕ}
        (e : Fin p ≃ Fin p') (f : Fin q ≃ Fin q') (i : Fin p),
        blockEquiv e f (Fin.castAdd q i) = Fin.castAdd q' (e i) := by
    intro p p' q q' e f i
    simp [blockEquiv, Equiv.trans_apply]
  have blockEquiv_apply_right :
      ∀ {p p' q q' : ℕ}
        (e : Fin p ≃ Fin p') (f : Fin q ≃ Fin q') (i : Fin q),
        blockEquiv e f (Fin.natAdd p i) = Fin.natAdd p' (f i) := by
    intro p p' q q' e f i
    simp [blockEquiv, Equiv.trans_apply]
  change (finAddFlip : Fin (a + (b + 1)) ≃ Fin ((b + 1) + a)) =
    (blockEquiv
        (finAddFlip : Fin (a + b) ≃ Fin (b + a))
        (Equiv.refl (Fin 1))).trans
      ((blockEquiv (Equiv.refl (Fin b))
        (finAddFlip : Fin (a + 1) ≃ Fin (1 + a))).trans
          (finCongr (Nat.add_assoc b 1 a).symm))
  apply Equiv.ext
  intro i
  refine Fin.addCases (m := a) (n := b + 1) (fun x => ?_) (fun y => ?_) i
  · have h0 : Fin.castAdd (b + 1) x =
        Fin.castAdd 1 (Fin.castAdd b x) := by
      apply Fin.ext
      rfl
    have h1 : Fin.castAdd 1 (Fin.natAdd b x) =
        Fin.natAdd b (Fin.castAdd 1 x) := by
      apply Fin.ext
      simp
    simp only [Equiv.trans_apply]
    rw [finAddFlip_apply_castAdd]
    rw [h0, blockEquiv_apply_left, finAddFlip_apply_castAdd, h1,
      blockEquiv_apply_right, finAddFlip_apply_castAdd]
    apply Fin.ext
    simp
    omega
  · refine Fin.addCases (m := b) (n := 1) (fun x => ?_) (fun z => ?_) y
    · have h0 : Fin.natAdd a (Fin.castAdd 1 x) =
          Fin.castAdd 1 (Fin.natAdd a x) := by
        apply Fin.ext
        simp
      have h1 : Fin.castAdd 1 (Fin.castAdd a x) =
          Fin.castAdd (a + 1) x := by
        apply Fin.ext
        rfl
      simp only [Equiv.trans_apply]
      rw [finAddFlip_apply_natAdd, h0]
      rw [blockEquiv_apply_left, finAddFlip_apply_natAdd, h1,
        blockEquiv_apply_left]
      rfl
    · have h0 : Fin.natAdd a (Fin.natAdd b z) =
          Fin.natAdd (a + b) z := by
        apply Fin.ext
        simp
      have h1 : Fin.natAdd (b + a) z =
          Fin.natAdd b (Fin.natAdd a z) := by
        apply Fin.ext
        simp
      simp only [Equiv.trans_apply]
      rw [finAddFlip_apply_natAdd, h0]
      rw [blockEquiv_apply_right]
      simp only [Equiv.refl_apply]
      rw [h1, blockEquiv_apply_right, finAddFlip_apply_natAdd]
      apply Fin.ext
      simp
/-- The literal left-successor singleton flip factors through the degree-two flip. -/
theorem finAddFlip_succ_left_one_factor : ∀ a : ℕ,
    (finAddFlip : Fin ((a + 1) + 1) ≃ Fin (1 + (a + 1))) =
      (finCongr (Nat.add_assoc a 1 1)).trans
        ((finSumFinEquiv.symm.trans
          ((Equiv.sumCongr (Equiv.refl (Fin a))
            (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1))).trans
              finSumFinEquiv)).trans
          ((finCongr (Nat.add_assoc a 1 1).symm).trans
            (finSumFinEquiv.symm.trans
              ((Equiv.sumCongr
                (finAddFlip : Fin (a + 1) ≃ Fin (1 + a))
                (Equiv.refl (Fin 1))).trans finSumFinEquiv)))) := by
  intro a
  let blockEquiv {p p' q q' : ℕ}
      (e : Fin p ≃ Fin p') (f : Fin q ≃ Fin q') :
      Fin (p + q) ≃ Fin (p' + q') :=
    finSumFinEquiv.symm.trans
      ((Equiv.sumCongr e f).trans finSumFinEquiv)
  have blockEquiv_apply_left :
      ∀ {p p' q q' : ℕ}
        (e : Fin p ≃ Fin p') (f : Fin q ≃ Fin q') (i : Fin p),
        blockEquiv e f (Fin.castAdd q i) = Fin.castAdd q' (e i) := by
    intro p p' q q' e f i
    simp [blockEquiv, Equiv.trans_apply]
  have blockEquiv_apply_right :
      ∀ {p p' q q' : ℕ}
        (e : Fin p ≃ Fin p') (f : Fin q ≃ Fin q') (i : Fin q),
        blockEquiv e f (Fin.natAdd p i) = Fin.natAdd p' (f i) := by
    intro p p' q q' e f i
    simp [blockEquiv, Equiv.trans_apply]
  change (finAddFlip : Fin ((a + 1) + 1) ≃ Fin (1 + (a + 1))) =
    (finCongr (Nat.add_assoc a 1 1)).trans
      ((blockEquiv (Equiv.refl (Fin a))
        (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1))).trans
        ((finCongr (Nat.add_assoc a 1 1).symm).trans
          (blockEquiv
            (finAddFlip : Fin (a + 1) ≃ Fin (1 + a))
            (Equiv.refl (Fin 1)))))
  apply Equiv.ext
  intro i
  refine Fin.addCases (m := a + 1) (n := 1) (fun x => ?_) (fun y => ?_) i
  · refine Fin.addCases (m := a) (n := 1) (fun x => ?_) (fun y => ?_) x
    · have h0 :
          (finCongr (Nat.add_assoc a 1 1))
              (Fin.castAdd 1 (Fin.castAdd 1 x)) =
            Fin.castAdd 2 x := by
        apply Fin.ext
        rfl
      have h1 :
          (finCongr (Nat.add_assoc a 1 1).symm) (Fin.castAdd 2 x) =
            Fin.castAdd 1 (Fin.castAdd 1 x) := by
        apply Fin.ext
        rfl
      simp only [Equiv.trans_apply]
      rw [finAddFlip_apply_castAdd, h0]
      rw [blockEquiv_apply_left]
      simp only [Equiv.refl_apply]
      rw [h1, blockEquiv_apply_left, finAddFlip_apply_castAdd]
      apply Fin.ext
      simp
    · have h0 :
          (finCongr (Nat.add_assoc a 1 1))
              (Fin.castAdd 1 (Fin.natAdd a y)) =
            Fin.natAdd a (Fin.castAdd 1 y) := by
        apply Fin.ext
        simp
      have h1 :
          (finCongr (Nat.add_assoc a 1 1).symm)
              (Fin.natAdd a (Fin.natAdd 1 y)) =
            Fin.natAdd (a + 1) y := by
        apply Fin.ext
        simp
      simp only [Equiv.trans_apply]
      rw [finAddFlip_apply_castAdd, h0]
      rw [blockEquiv_apply_right, finAddFlip_apply_castAdd, h1,
        blockEquiv_apply_right]
      apply Fin.ext
      simp
  · have h0 :
        (finCongr (Nat.add_assoc a 1 1)) (Fin.natAdd (a + 1) y) =
          Fin.natAdd a (Fin.natAdd 1 y) := by
      apply Fin.ext
      simp
    have h1 :
        (finCongr (Nat.add_assoc a 1 1).symm)
            (Fin.natAdd a (Fin.castAdd 1 y)) =
          Fin.castAdd 1 (Fin.natAdd a y) := by
      apply Fin.ext
      simp
    simp only [Equiv.trans_apply]
    rw [finAddFlip_apply_natAdd, h0]
    rw [blockEquiv_apply_right, finAddFlip_apply_natAdd, h1,
      blockEquiv_apply_left, finAddFlip_apply_natAdd]
    apply Fin.ext
    simp

omit [SymmetricCategory C] in
/-- Original ordered three-block split as an Iso transport identity. -/
theorem tensorPowSplitAssocIso (X : C) (a b c : ℕ) :
    (tensorPowObj_add X (a + b) c).symm ≪≫
        eqToIso (congrArg (tensorPowObj X) (Nat.add_assoc a b c)) =
      tensorIso (tensorPowObj_add X a b) (Iso.refl (tensorPowObj X c)) ≪≫
        associator (tensorPowObj X a) (tensorPowObj X b) (tensorPowObj X c) ≪≫
        tensorIso (Iso.refl (tensorPowObj X a)) ((tensorPowObj_add X b c).symm) ≪≫
        (tensorPowObj_add X a (b + c)).symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  have hAssoc := tensorPowObj_add_assoc X a b c
  apply (cancel_epi (tensorPowObj_add X (a + b) c).hom).1
  calc
    (tensorPowObj_add X (a + b) c).hom ≫
        ((tensorPowObj_add X (a + b) c).inv ≫
          (eqToIso (congrArg (tensorPowObj X)
            (Nat.add_assoc a b c))).hom) =
      (eqToIso (congrArg (tensorPowObj X)
        (Nat.add_assoc a b c))).hom := by
      simp only [eqToIso.hom, Iso.hom_inv_id_assoc]
    _ = ((((eqToIso (congrArg (tensorPowObj X)
            (Nat.add_assoc a b c))).hom ≫
          (tensorPowObj_add X a (b + c)).hom) ≫
        (𝟙 (tensorPowObj X a) ⊗ₘ
          (tensorPowObj_add X b c).hom)) ≫
        (𝟙 (tensorPowObj X a) ⊗ₘ
          (tensorPowObj_add X b c).inv)) ≫
        (tensorPowObj_add X a (b + c)).inv := by
      simp only [eqToIso.hom, id_tensorHom, Category.assoc,
        whiskerLeft_hom_inv, Category.comp_id, Iso.hom_inv_id]
    _ = ((((tensorPowObj_add X (a + b) c).hom ≫
          ((tensorPowObj_add X a b).hom ⊗ₘ
            𝟙 (tensorPowObj X c))) ≫
          (associator (tensorPowObj X a) (tensorPowObj X b)
            (tensorPowObj X c)).hom) ≫
        (𝟙 (tensorPowObj X a) ⊗ₘ
          (tensorPowObj_add X b c).inv)) ≫
        (tensorPowObj_add X a (b + c)).inv := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫
          (𝟙 (tensorPowObj X a) ⊗ₘ
            (tensorPowObj_add X b c).inv) ≫
          (tensorPowObj_add X a (b + c)).inv) hAssoc
    _ = (tensorPowObj_add X (a + b) c).hom ≫
        (((tensorPowObj_add X a b).hom ⊗ₘ
            𝟙 (tensorPowObj X c)) ≫
          (associator (tensorPowObj X a) (tensorPowObj X b)
            (tensorPowObj X c)).hom ≫
          (𝟙 (tensorPowObj X a) ⊗ₘ
            (tensorPowObj_add X b c).inv) ≫
          (tensorPowObj_add X a (b + c)).inv) := by
      simp only [Category.assoc]

/-- The actual degree-two flip is the original braiding. -/
theorem blockSwap_one_one (X : C) :
    (tensorPowObj_add X 1 1).symm ≪≫
        permutationIso X
          (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1)) =
      (β_ (tensorPowObj X 1) (tensorPowObj X 1)) ≪≫
        (tensorPowObj_add X 1 1).symm := by
  have hperm : permutationIso X
      (finAddFlip (m := 1) (n := 1) : Fin 2 ≃ Fin 2) =
      permutationIsoAux X 2
        (Fin.revPerm.trans
          ((finAddFlip (m := 1) (n := 1) : Fin 2 ≃ Fin 2).trans
            Fin.revPerm)) := by
    unfold permutationIso
    rfl
  rw [hperm]
  have hrev : Fin.revPerm.trans
      ((finAddFlip (m := 1) (n := 1) : Fin 2 ≃ Fin 2).trans Fin.revPerm) =
    (finAddFlip (m := 1) (n := 1) : Fin 2 ≃ Fin 2) := by
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  rw [hrev]
  have hdec : Equiv.Perm.decomposeFin
      (finAddFlip (m := 1) (n := 1) : Equiv.Perm (Fin 2)) =
    (1, Equiv.refl (Fin 1)) := by
    apply Equiv.Perm.decomposeFin.symm.injective
    apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  rw [permutationIsoAux, hdec, permutationIsoAux_refl]
  apply Iso.ext
  simp only [Iso.trans_hom]
  let A : tensorPowObj X 2 ≅ tensorPowObj X 2 :=
    tensorIso (moveZeroIso X 1 (0 : Fin 1)) (Iso.refl X)
  let adj : tensorPowObj X 2 ≅ tensorPowObj X 2 :=
    adjacentSwapIso X 0
  have hA : A = Iso.refl _ := by
    dsimp only [A]
    have hz : moveZeroIso X 1 (0 : Fin 1) = Iso.refl _ := rfl
    rw [hz]
    apply Iso.ext
    exact id_tensorHom_id _ _
  have hMove : moveZeroIso X 2 (1 : Fin 2) = adj := by
    calc
      moveZeroIso X 2 (1 : Fin 2) = (A ≪≫ adj) ≪≫ A.symm := by
        exact moveZeroIso_succ X 0 (0 : Fin 1)
      _ = adj := by
        rw [hA, Iso.refl_trans, Iso.refl_symm, Iso.trans_refl]
  let L2 : (tensorPowObj X 0 ⊗ X) ⊗ X ≅
      (tensorPowObj X 0 ⊗ X) ⊗ X :=
    tensorIso (Iso.refl (tensorPowObj X 1)) (Iso.refl X)
  have hL2 : L2 = Iso.refl _ := by
    dsimp only [L2]
    apply Iso.ext
    exact id_tensorHom_id _ _
  change ((tensorPowObj_add X 1 1).symm).hom ≫
      (L2 ≪≫ moveZeroIso X 2 (1 : Fin 2)).hom = _
  have hLM : L2 ≪≫ moveZeroIso X 2 (1 : Fin 2) = adj :=
    (congrArg (fun z => z ≪≫ moveZeroIso X 2 (1 : Fin 2)) hL2).trans
      ((Iso.refl_trans _).trans hMove)
  rw [hLM]
  dsimp only [adj]
  unfold adjacentSwapIso
  dsimp [tensorPowObj_add, tensorPowObj]
  let u : (𝟙_ C ⊗ X) ≅ X := leftUnitor X
  let d : ((𝟙_ C ⊗ X) ⊗ (𝟙_ C ⊗ X)) ⟶
      ((𝟙_ C ⊗ X) ⊗ X) :=
    (associator (𝟙_ C ⊗ X) (𝟙_ C) X).inv ≫
      ((rightUnitor (𝟙_ C ⊗ X)).hom ⊗ₘ 𝟙 X)
  let s : ((𝟙_ C ⊗ X) ⊗ X) ⟶ ((𝟙_ C ⊗ X) ⊗ X) :=
    (associator (𝟙_ C) X X).hom ≫
      (𝟙_ C ◁ (β_ X X).hom) ≫
      (associator (𝟙_ C) X X).inv
  let v : ((𝟙_ C ⊗ X) ⊗ X) ⟶ (X ⊗ X) :=
    u.hom ⊗ₘ 𝟙 X
  change d ≫ s = (β_ (𝟙_ C ⊗ X) (𝟙_ C ⊗ X)).hom ≫ d
  have hd : d = 𝟙 (𝟙_ C ⊗ X) ⊗ₘ u.hom := by
    dsimp only [d, u]
    rw [tensorHom_id, id_tensorHom]
    exact triangle_assoc_comp_right (𝟙_ C ⊗ X) X
  have hCollapse : d ≫ v = (u.hom ⊗ₘ u.hom) := by
    rw [hd]
    dsimp only [v]
    rw [tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  have hAdjacent : s ≫ v = v ≫ (β_ X X).hom := by
    dsimp only [s, u, v]
    simp only [Category.assoc]
    rw [← leftUnitor_tensor_hom' X X]
    rw [leftUnitor_naturality]
    rw [← Category.assoc]
    exact congrArg (fun k => k ≫ (β_ X X).hom)
      (leftUnitor_tensor_hom'' X X)
  apply (cancel_mono v).1
  calc
    (d ≫ s) ≫ v = d ≫ (s ≫ v) := Category.assoc _ _ _
    _ = d ≫ (v ≫ (β_ X X).hom) :=
      congrArg (fun k => d ≫ k) hAdjacent
    _ = (d ≫ v) ≫ (β_ X X).hom := (Category.assoc _ _ _).symm
    _ = (u.hom ⊗ₘ u.hom) ≫ (β_ X X).hom :=
      congrArg (fun k => k ≫ (β_ X X).hom) hCollapse
    _ = (β_ (𝟙_ C ⊗ X) (𝟙_ C ⊗ X)).hom ≫
        (u.hom ⊗ₘ u.hom) :=
      BraidedCategory.braiding_naturality u.hom u.hom
    _ = (β_ (𝟙_ C ⊗ X) (𝟙_ C ⊗ X)).hom ≫
        (d ≫ v) :=
      congrArg
        (fun k => (β_ (𝟙_ C ⊗ X) (𝟙_ C ⊗ X)).hom ≫ k)
        hCollapse.symm
    _ = ((β_ (𝟙_ C ⊗ X) (𝟙_ C ⊗ X)).hom ≫ d) ≫ v :=
      (Category.assoc _ _ _).symm

/-- The actual original power block versus singleton flip. -/
theorem blockSwap_one_right (X : C) : ∀ a : ℕ,
    (tensorPowObj_add X a 1).symm ≪≫
        permutationIso X
          (finAddFlip : Fin (a + 1) ≃ Fin (1 + a)) =
      (β_ (tensorPowObj X a) (tensorPowObj X 1)) ≪≫
        (tensorPowObj_add X 1 a).symm := by
  intro a
  induction a with
  | zero =>
      have hflip :
          (finAddFlip : Fin (0 + 1) ≃ Fin (1 + 0)) =
            Equiv.refl (Fin 1) := by
        apply Equiv.ext
        intro i
        exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
      rw [hflip, permutationIso_refl, Iso.trans_refl]
      apply Iso.ext
      change (tensorPowObj_add X 0 1).inv =
        (β_ (𝟙_ C) (tensorPowObj X 1)).hom ≫
          (tensorPowObj_add X 1 0).inv
      rw [braiding_tensorUnit_left]
      have hright : (tensorPowObj_add X 1 0).inv =
          (rightUnitor (tensorPowObj X 1)).hom := by
        apply (cancel_epi (tensorPowObj_add X 1 0).hom).1
        rw [Iso.hom_inv_id]
        rw [tensorPowObj_add_zero_right]
        change 𝟙 (tensorPowObj X 1) =
          (rightUnitor (tensorPowObj X 1)).inv ≫
            (rightUnitor (tensorPowObj X 1)).hom
        rw [Iso.inv_hom_id]
      rw [hright, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      have hleft := tensorPowObj_add_zero_left X 1
      have hleft' : (tensorPowObj_add X 0 1).hom ≫
          (leftUnitor (tensorPowObj X 1)).hom =
            𝟙 (tensorPowObj X 1) := by
        have hp : Nat.zero_add 1 = (rfl : 0 + 1 = 1) :=
          Subsingleton.elim _ _
        rw [hp] at hleft
        simpa only [eqToIso_refl, Iso.refl_hom] using hleft
      apply (cancel_epi (tensorPowObj_add X 0 1).hom).1
      rw [Iso.hom_inv_id]
      exact hleft'.symm
  | succ a ih =>
      rw [finAddFlip_succ_left_one_factor]
      rw [permutationIso_trans, permutationIso_trans,
        permutationIso_trans]
      rw [permutationIso_finCongr]
      rw [← Iso.trans_assoc]
      rw [tensorPowSplitAssocIso X a 1 1]
      let E := tensorPowObj_add X a 1
      let K := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc a 1 1))
      let Kinv := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc a 1 1).symm)
      have hKinv : Kinv = K.symm := by
        apply Iso.ext
        dsimp only [Kinv, K]
        rfl
      let L := tensorIso E (Iso.refl (tensorPowObj X 1)) ≪≫
        associator (tensorPowObj X a) (tensorPowObj X 1) (tensorPowObj X 1)
      let T := tensorIso (Iso.refl (tensorPowObj X a))
        ((tensorPowObj_add X 1 1).symm)
      let C₂ := (tensorPowObj_add X a (1 + 1)).symm
      let D := (tensorPowObj_add X (a + 1) 1).symm
      have hSplitA : D ≪≫ K = L ≪≫ T ≪≫ C₂ := by
        dsimp only [D, K, L, E, T, C₂]
        simpa only [Iso.trans_assoc] using tensorPowSplitAssocIso X a 1 1
      have hUnsplitA : T ≪≫ C₂ ≪≫ K.symm = L.symm ≪≫ D := by
        calc
          T ≪≫ C₂ ≪≫ K.symm =
              L.symm ≪≫ (L ≪≫ T ≪≫ C₂) ≪≫ K.symm := by
            simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
          _ = L.symm ≪≫ (D ≪≫ K) ≪≫ K.symm := by rw [hSplitA]
          _ = L.symm ≪≫ D := by
            simp only [Iso.trans_assoc, Iso.self_symm_id,
              Iso.trans_refl]
      let F := tensorPowObj_add X 1 a
      let K' := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc 1 a 1))
      let L' := tensorIso F (Iso.refl (tensorPowObj X 1)) ≪≫
        associator (tensorPowObj X 1) (tensorPowObj X a) (tensorPowObj X 1)
      let T' := tensorIso (Iso.refl (tensorPowObj X 1))
        ((tensorPowObj_add X a 1).symm)
      let C' := (tensorPowObj_add X 1 (a + 1)).symm
      let D' := (tensorPowObj_add X (1 + a) 1).symm
      have hSplitB : D' ≪≫ K' = L' ≪≫ T' ≪≫ C' := by
        dsimp only [D', K', L', F, T', C']
        simpa only [Iso.trans_assoc] using tensorPowSplitAssocIso X 1 a 1
      have hK' : K' = Iso.refl _ := by
        apply Iso.ext
        dsimp only [K']
        rfl
      have hF : (tensorPowObj_add X 1 a).symm = F.symm := by
        dsimp only [F]
      have hResplitB :
          tensorIso ((tensorPowObj_add X 1 a).symm) (Iso.refl (tensorPowObj X 1)) ≪≫
              D' =
            associator (tensorPowObj X 1) (tensorPowObj X a)
                (tensorPowObj X 1) ≪≫
              T' ≪≫ C' := by
        rw [hK', Iso.trans_refl] at hSplitB
        have hTensor :
            tensorIso F.symm (Iso.refl (tensorPowObj X 1)) ≪≫
                tensorIso F (Iso.refl (tensorPowObj X 1)) =
              Iso.refl _ := by
          apply Iso.ext
          simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
            Iso.refl_hom, tensorHom_comp_tensorHom,
            Iso.inv_hom_id, Category.id_comp]
          exact id_tensorHom_id _ _
        calc
          tensorIso ((tensorPowObj_add X 1 a).symm)
                (Iso.refl (tensorPowObj X 1)) ≪≫ D' =
              tensorIso F.symm (Iso.refl (tensorPowObj X 1)) ≪≫
                (L' ≪≫ T' ≪≫ C') := by rw [hF, ← hSplitB]
          _ = associator (tensorPowObj X 1) (tensorPowObj X a)
                (tensorPowObj X 1) ≪≫ T' ≪≫ C' := by
            dsimp only [L']
            simp only [Iso.trans_assoc]
            rw [← Iso.trans_assoc
              (tensorIso F.symm (Iso.refl (tensorPowObj X 1)))
              (tensorIso F (Iso.refl (tensorPowObj X 1)))
              (associator (tensorPowObj X 1) (tensorPowObj X a)
                  (tensorPowObj X 1) ≪≫ T' ≪≫ C')]
            rw [hTensor, Iso.refl_trans]
      rw [show eqToIso (congrArg (tensorPowObj X)
        (Nat.add_assoc a 1 1).symm) = K.symm by exact hKinv]
      apply Iso.ext
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
      have hMid := congrArg Iso.hom
        (blockSumIso_natural X (Equiv.refl (Fin a))
          (finAddFlip : Fin (1 + 1) ≃ Fin (1 + 1)))
      simp only [Iso.trans_hom, tensorIso_hom] at hMid
      rw [permutationIso_refl] at hMid
      have h11 := congrArg Iso.hom (blockSwap_one_one X)
      simp only [Iso.trans_hom] at h11
      have hUnsplitHom := congrArg Iso.hom hUnsplitA
      simp only [Iso.trans_hom, L, T, C₂, D, K, E,
        tensorIso_hom, Iso.refl_hom] at hUnsplitHom
      have hFinal := congrArg Iso.hom
        (blockSumIso_natural X
          (finAddFlip : Fin (a + 1) ≃ Fin (1 + a))
          (Equiv.refl (Fin 1)))
      simp only [Iso.trans_hom, tensorIso_hom] at hFinal
      rw [permutationIso_refl] at hFinal
      have hLsym : L.symm.hom =
          (associator (tensorPowObj X a) (tensorPowObj X 1)
            (tensorPowObj X 1)).inv ≫
            (E.inv ⊗ₘ 𝟙 (tensorPowObj X 1)) := by
        dsimp only [L]
        rfl
      have hIH := congrArg Iso.hom ih
      simp only [Iso.trans_hom] at hIH
      change E.inv ≫
          (permutationIso X
            (finAddFlip : Fin (a + 1) ≃ Fin (1 + a))).hom =
        (β_ (tensorPowObj X a) (tensorPowObj X 1)).hom ≫
          ((tensorPowObj_add X 1 a).symm).hom at hIH
      have hResplitHom := congrArg Iso.hom hResplitB
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
        T', C', D'] at hResplitHom
      have hEa : (tensorPowObj_add X a 1).symm = E.symm := by
        dsimp only [E]
      slice_lhs 4 5 => rw [hMid.symm]
      slice_lhs 3 4 =>
        rw [tensorHom_comp_tensorHom]
        simp only [Iso.refl_hom, Category.id_comp]
        rw [h11]
        rw [← Category.id_comp (𝟙 (tensorPowObj X a))]
        rw [← tensorHom_comp_tensorHom]
      slice_lhs 4 6 => rw [hUnsplitHom]
      slice_lhs 5 6 => rw [hFinal.symm]
      slice_lhs 4 4 => rw [hLsym]
      slice_lhs 5 6 =>
        rw [tensorHom_comp_tensorHom]
        simp only [Iso.refl_hom, Category.comp_id]
        rw [hIH]
        rw [← Category.id_comp (𝟙 (tensorPowObj X 1))]
        rw [← tensorHom_comp_tensorHom]
      slice_lhs 6 7 => rw [hResplitHom]
      slice_lhs 2 6 =>
        rw [id_tensorHom, tensorHom_id]
        rw [← BraidedCategory.braiding_tensor_left_hom]
      slice_lhs 1 2 =>
        rw [BraidedCategory.braiding_naturality]
      slice_lhs 2 3 =>
        rw [tensorHom_comp_tensorHom, hEa]
        change ((𝟙 (tensorPowObj X 1) ≫ 𝟙 (tensorPowObj X 1)) ⊗ₘ
          (E.hom ≫ E.inv))
        rw [Category.id_comp, Iso.hom_inv_id, id_tensorHom_id]
      simp only [Category.id_comp]

/-- Swapping the two tensor-power blocks is the ambient braiding. -/
theorem blockSwap (X : C) (m n : ℕ) :
    (tensorPowObj_add X m n).symm ≪≫
        permutationIso X
          (finAddFlip : Fin (m + n) ≃ Fin (n + m)) =
      (β_ (tensorPowObj X m) (tensorPowObj X n)) ≪≫
        (tensorPowObj_add X n m).symm := by
  induction n with
  | zero =>
      let hadd : m + 0 = 0 + m :=
        (Nat.add_zero m).trans (Nat.zero_add m).symm
      have hflip :
          (finAddFlip : Fin (m + 0) ≃ Fin (0 + m)) =
            finCongr hadd := by
        apply Equiv.ext
        intro i
        refine Fin.addCases (m := m) (n := 0) (fun a => ?_)
          (fun b => Fin.elim0 b) i
        rw [finAddFlip_apply_castAdd]
        apply Fin.ext
        simp
      rw [hflip, permutationIso_finCongr]
      apply Iso.ext
      change (tensorPowObj_add X m 0).inv ≫
          (eqToIso (congrArg (tensorPowObj X) hadd)).hom =
        (β_ (tensorPowObj X m) (𝟙_ C)).hom ≫
          (tensorPowObj_add X 0 m).inv
      rw [braiding_tensorUnit_right]
      have hRight : (tensorPowObj_add X m 0).inv =
          (rightUnitor (tensorPowObj X m)).hom := by
        apply (cancel_epi (tensorPowObj_add X m 0).hom).1
        rw [Iso.hom_inv_id]
        rw [tensorPowObj_add_zero_right]
        change 𝟙 (tensorPowObj X m) =
          (rightUnitor (tensorPowObj X m)).inv ≫
            (rightUnitor (tensorPowObj X m)).hom
        rw [Iso.inv_hom_id]
      have hLeftIso :
          tensorPowObj_add X 0 m ≪≫ leftUnitor (tensorPowObj X m) =
            eqToIso (congrArg (tensorPowObj X) (Nat.zero_add m)) := by
        apply Iso.ext
        exact tensorPowObj_add_zero_left X m
      have hLeft := congrArg (fun e => e.symm.hom) hLeftIso
      change (leftUnitor (tensorPowObj X m)).inv ≫
          (tensorPowObj_add X 0 m).inv =
        (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add m))).inv at hLeft
      have hProof : hadd = (Nat.zero_add m).symm := Subsingleton.elim _ _
      have hCast :
          (eqToIso (congrArg (tensorPowObj X) hadd)).hom =
          (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add m))).inv := by
        rw [hProof, eqToIso.hom, eqToIso.inv]
      rw [hRight, hCast]
      calc
        (rightUnitor (tensorPowObj X m)).hom ≫
            (eqToIso (congrArg (tensorPowObj X) (Nat.zero_add m))).inv =
          (rightUnitor (tensorPowObj X m)).hom ≫
            ((leftUnitor (tensorPowObj X m)).inv ≫
              (tensorPowObj_add X 0 m).inv) := congrArg
                (fun k => (rightUnitor (tensorPowObj X m)).hom ≫ k)
                hLeft.symm
        _ = ((rightUnitor (tensorPowObj X m)).hom ≫
              (leftUnitor (tensorPowObj X m)).inv) ≫
            (tensorPowObj_add X 0 m).inv :=
          (Category.assoc _ _ _).symm
  | succ n ih =>
      rw [finAddFlip_succ_right_factor]
      rw [permutationIso_trans, permutationIso_trans]
      rw [permutationIso_finCongr]
      let A := tensorPowObj_add X m n
      let E := tensorPowObj_add X n 1
      let G := tensorPowObj_add X n m
      let K₀ := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc m n 1))
      let K₁ := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc n m 1))
      let K₂ := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc n 1 m))
      let K₂inv := eqToIso
        (congrArg (tensorPowObj X) (Nat.add_assoc n 1 m).symm)
      have hK₀ : K₀ = Iso.refl _ := by
        apply Iso.ext
        dsimp only [K₀]
        rfl
      have hK₁ : K₁ = Iso.refl _ := by
        apply Iso.ext
        dsimp only [K₁]
        rfl
      have hK₂inv : K₂inv = K₂.symm := by
        apply Iso.ext
        dsimp only [K₂inv, K₂]
        rfl
      let L₀ :=
        tensorIso A (Iso.refl (tensorPowObj X 1)) ≪≫
          associator (tensorPowObj X m) (tensorPowObj X n)
            (tensorPowObj X 1) ≪≫
          tensorIso (Iso.refl (tensorPowObj X m))
            ((tensorPowObj_add X n 1).symm)
      let L₁ :=
        tensorIso G (Iso.refl (tensorPowObj X 1)) ≪≫
          associator (tensorPowObj X n) (tensorPowObj X m)
            (tensorPowObj X 1) ≪≫
          tensorIso (Iso.refl (tensorPowObj X n))
            ((tensorPowObj_add X m 1).symm)
      let L₂ :=
        tensorIso E (Iso.refl (tensorPowObj X m)) ≪≫
          associator (tensorPowObj X n) (tensorPowObj X 1)
            (tensorPowObj X m) ≪≫
          tensorIso (Iso.refl (tensorPowObj X n))
            ((tensorPowObj_add X 1 m).symm)
      have hSplit₀ :
          (tensorPowObj_add X (m + n) 1).symm =
            L₀ ≪≫ (tensorPowObj_add X m (n + 1)).symm := by
        have h := tensorPowSplitAssocIso X m n 1
        change (tensorPowObj_add X (m + n) 1).symm ≪≫ K₀ = _ at h
        rw [hK₀, Iso.trans_refl] at h
        dsimp only [L₀]
        simpa only [Iso.trans_assoc] using h
      have hSplit₁ :
          (tensorPowObj_add X (n + m) 1).symm =
            L₁ ≪≫ (tensorPowObj_add X n (m + 1)).symm := by
        have h := tensorPowSplitAssocIso X n m 1
        change (tensorPowObj_add X (n + m) 1).symm ≪≫ K₁ = _ at h
        rw [hK₁, Iso.trans_refl] at h
        dsimp only [L₁]
        simpa only [Iso.trans_assoc] using h
      have hSplit₂ :
          (tensorPowObj_add X (n + 1) m).symm ≪≫ K₂ =
            L₂ ≪≫ (tensorPowObj_add X n (1 + m)).symm := by
        dsimp only [L₂, K₂, E]
        simpa only [Iso.trans_assoc] using tensorPowSplitAssocIso X n 1 m
      rw [show eqToIso (congrArg (tensorPowObj X)
        (Nat.add_assoc n 1 m).symm) = K₂.symm by exact hK₂inv]
      apply Iso.ext
      simp only [Iso.trans_hom]
      apply (cancel_mono K₂.hom).1
      simp only [Category.assoc]
      have hSplit₂hom := congrArg Iso.hom hSplit₂
      simp only [Iso.trans_hom] at hSplit₂hom
      rw [hSplit₂hom]
      apply (cancel_epi L₀.hom).1
      simp only [← Category.assoc]
      have hSplit₀hom := congrArg Iso.hom hSplit₀
      simp only [Iso.trans_hom] at hSplit₀hom
      rw [← hSplit₀hom]
      simp only [Category.assoc]
      slice_lhs 4 5 =>
        change K₂.inv ≫ K₂.hom
        rw [Iso.inv_hom_id]
      simp only [Category.comp_id]
      have hNat₁ := congrArg Iso.hom
        (blockSumIso_natural X
          (finAddFlip : Fin (m + n) ≃ Fin (n + m))
          (Equiv.refl (Fin 1)))
      have hNat₂ := congrArg Iso.hom
        (blockSumIso_natural X (Equiv.refl (Fin n))
          (finAddFlip : Fin (m + 1) ≃ Fin (1 + m)))
      simp only [Iso.trans_hom, tensorIso_hom] at hNat₁ hNat₂
      rw [permutationIso_refl] at hNat₁ hNat₂
      have hSplit₁hom := congrArg Iso.hom hSplit₁
      simp only [Iso.trans_hom] at hSplit₁hom
      have hL₁ : L₁.hom =
          (G.hom ⊗ₘ 𝟙 (tensorPowObj X 1)) ≫
            (associator (tensorPowObj X n) (tensorPowObj X m)
              (tensorPowObj X 1)).hom ≫
            (𝟙 (tensorPowObj X n) ⊗ₘ ((tensorPowObj_add X m 1).symm).hom) := by
        dsimp only [L₁]
        rfl
      have hOneHom := congrArg Iso.hom (blockSwap_one_right X m)
      simp only [Iso.trans_hom] at hOneHom
      have hIH := congrArg Iso.hom ih
      simp only [Iso.trans_hom] at hIH
      have hA : (tensorPowObj_add X m n).symm = A.symm := by
        dsimp only [A]
      have hG : (tensorPowObj_add X n m).symm = G.symm := by
        dsimp only [G]
      rw [hA, hG] at hIH
      change A.inv ≫
          (permutationIso X
            (finAddFlip : Fin (m + n) ≃ Fin (n + m))).hom =
        (β_ (tensorPowObj X m) (tensorPowObj X n)).hom ≫ G.inv at hIH
      have hIHcore :
          (permutationIso X
              (finAddFlip : Fin (m + n) ≃ Fin (n + m))).hom ≫ G.hom =
            A.hom ≫ (β_ (tensorPowObj X m) (tensorPowObj X n)).hom := by
        apply (cancel_epi A.inv).1
        calc
          A.inv ≫
              ((permutationIso X
                (finAddFlip : Fin (m + n) ≃ Fin (n + m))).hom ≫ G.hom) =
              (A.inv ≫
                (permutationIso X
                  (finAddFlip : Fin (m + n) ≃ Fin (n + m))).hom) ≫
                G.hom := (Category.assoc _ _ _).symm
          _ = ((β_ (tensorPowObj X m) (tensorPowObj X n)).hom ≫ G.inv) ≫
                G.hom := congrArg (fun k => k ≫ G.hom) hIH
          _ = (β_ (tensorPowObj X m) (tensorPowObj X n)).hom := by
            rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
          _ = A.inv ≫
              (A.hom ≫ (β_ (tensorPowObj X m) (tensorPowObj X n)).hom) := by
            rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      slice_lhs 1 2 => rw [hNat₁.symm]
      slice_lhs 2 2 => rw [hSplit₁hom]
      slice_lhs 3 4 => rw [hNat₂.symm]
      slice_lhs 2 2 => rw [hL₁]
      slice_lhs 4 5 =>
        rw [tensorHom_comp_tensorHom]
        simp only [Iso.refl_hom, Category.id_comp]
        rw [hOneHom]
        rw [← Category.id_comp (𝟙 (tensorPowObj X n))]
        rw [← tensorHom_comp_tensorHom]
      slice_lhs 1 2 =>
        rw [tensorHom_comp_tensorHom]
        simp only [Iso.refl_hom, Category.comp_id]
        rw [hIHcore]
        rw [← Category.id_comp (𝟙 (tensorPowObj X 1))]
        rw [← tensorHom_comp_tensorHom]
      have hL₀ : L₀.hom =
          (A.hom ⊗ₘ 𝟙 (tensorPowObj X 1)) ≫
            (associator (tensorPowObj X m) (tensorPowObj X n)
              (tensorPowObj X 1)).hom ≫
            (𝟙 (tensorPowObj X m) ⊗ₘ ((tensorPowObj_add X n 1).symm).hom) := by
        dsimp only [L₀]
        rfl
      have hL₂ : L₂.hom =
          (E.hom ⊗ₘ 𝟙 (tensorPowObj X m)) ≫
            (associator (tensorPowObj X n) (tensorPowObj X 1)
              (tensorPowObj X m)).hom ≫
            (𝟙 (tensorPowObj X n) ⊗ₘ ((tensorPowObj_add X 1 m).symm).hom) := by
        dsimp only [L₂]
        rfl
      have hBn : (tensorPowObj_add X n 1).symm = E.symm := by
        dsimp only [E]
      have hHexCore :
          (associator (tensorPowObj X m) (tensorPowObj X n)
              (tensorPowObj X 1)).hom ≫
            (β_ (tensorPowObj X m)
              (tensorPowObj X n ⊗ tensorPowObj X 1)).hom ≫
            (associator (tensorPowObj X n) (tensorPowObj X 1)
              (tensorPowObj X m)).hom =
          ((β_ (tensorPowObj X m) (tensorPowObj X n)).hom ⊗ₘ
              𝟙 (tensorPowObj X 1)) ≫
            (associator (tensorPowObj X n) (tensorPowObj X m)
              (tensorPowObj X 1)).hom ≫
            (𝟙 (tensorPowObj X n) ⊗ₘ
              (β_ (tensorPowObj X m) (tensorPowObj X 1)).hom) := by
        rw [BraidedCategory.braiding_tensor_right_hom]
        rw [tensorHom_id, id_tensorHom]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        slice_lhs 4 5 =>
          rw [Iso.inv_hom_id]
        simp only [Category.comp_id]
      slice_rhs 1 1 => rw [hL₀]
      slice_rhs 5 5 => rw [hL₂]
      slice_rhs 3 4 =>
        rw [BraidedCategory.braiding_naturality]
      slice_rhs 4 5 =>
        rw [tensorHom_comp_tensorHom, hBn]
        change ((E.inv ≫ E.hom) ⊗ₘ
          (𝟙 (tensorPowObj X m) ≫ 𝟙 (tensorPowObj X m)))
        rw [Iso.inv_hom_id, Category.id_comp, id_tensorHom_id]
      simp only [Category.id_comp]
      slice_rhs 2 4 => rw [hHexCore]
      simp only [Category.assoc]

end CategoryTheory.MonoidalCategory.SymmetricTensorPower
