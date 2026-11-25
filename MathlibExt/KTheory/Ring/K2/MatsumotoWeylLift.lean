/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalMonomialBridgeNaturality
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootRealization

@[expose] public section

open Matrix
open PermutationBilinearCocycle
open MatsumotoPermutationAction
open MatsumotoMonomialExtension
open MatsumotoDiagonalMonomialBridge
open MatsumotoDiagonalExtension

universe u v

namespace MatsumotoWeylLift

variable (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j) (u : Fˣ)

/-!
# Canonical Weyl lifts in HM

We construct explicit lifts `weylHM` of the simple-root Weyl monomials
`weylMonomialSLUnit i j hij u` in `HM F n`.  The ambient lift uses base
`weylWeightUnit` and permutation `swap i j` with coefficient
`weylK2Coeff`.  The choice `\{u,-1\}` when `i<j` and `\{u,u\}` when `j<i`
is field-functorial and gives the exact relation
`w(u) * w(-1) = HToHM (h_ij u)` in `HM`.  The correction is forced by
the lower cocycle; with naive coefficient `1` the product would be
`lowerSum`, not the required `h_ij` coefficient.  Using `c(-1)=\{-1,-1\}`
and `2\{-1,-1\}=0` we obtain the exact equality.
-/

def weylK2Coeff (F : Type u) [Field F] {n : ℕ} (i j : Fin n)
    (u : Fˣ) : MilnorK F 2 :=
  if i < j then MilnorK.k2Symbol F u (-1) else MilnorK.k2Symbol F u u

@[simp]
theorem weylK2Coeff_lt {F : Type u} [Field F] {n : ℕ} {i j : Fin n}
    (h : i < j) (u : Fˣ) :
    weylK2Coeff F i j u = MilnorK.k2Symbol F u (-1) := by
  simp [weylK2Coeff, h]

@[simp]
theorem weylK2Coeff_gt {F : Type u} [Field F] {n : ℕ} {i j : Fin n}
    (h : ¬ i < j) (u : Fˣ) :
    weylK2Coeff F i j u = MilnorK.k2Symbol F u u := by
  simp [weylK2Coeff, h]

def weylHAll (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (u : Fˣ) : HAll F n :=
  ⟨GeneralLinearGroup.weylWeightUnit i j hij u,
    Multiplicative.ofAdd (weylK2Coeff F i j u)⟩

def ambientWeylLift (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    MonomialLift (milnorK2Bicharacter F) (Fin n) :=
  ⟨weylHAll F n i j hij u, Equiv.swap i j⟩

theorem ambientWeylLift_proj (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    monomialProjHom (milnorK2Bicharacter F) (Fin n)
        (ambientWeylLift F n i j hij u) =
      GeneralLinearGroup.weylMonomialBaseUnit i j hij u := by
  apply SemidirectProduct.ext <;> rfl

theorem weyl_pullback (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    (monomialGroupExtension (milnorK2Bicharacter F) (Fin n)).rightHom
        (ambientWeylLift F n i j hij u) =
      Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
        (GeneralLinearGroup.weylMonomialSLUnit i j hij u) := by
  calc (monomialGroupExtension (milnorK2Bicharacter F) (Fin n)).rightHom
          (ambientWeylLift F n i j hij u)
      = monomialProjHom (milnorK2Bicharacter F) (Fin n)
          (ambientWeylLift F n i j hij u) := rfl
    _ = GeneralLinearGroup.weylMonomialBaseUnit i j hij u :=
        ambientWeylLift_proj F n i j hij u
    _ = (Matrix.GeneralLinearGroup.monomialSLToMonomialBase F (Fin n)
          (GeneralLinearGroup.weylMonomialSLUnit i j hij u)) := rfl

def weylHM (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (u : Fˣ) : HM F n :=
  ⟨(ambientWeylLift F n i j hij u,
    GeneralLinearGroup.weylMonomialSLUnit i j hij u),
    weyl_pullback F n i j hij u⟩

@[simp]
theorem weylHM_ambient (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    ambientLiftHom F n (weylHM F n i j hij u) =
      ambientWeylLift F n i j hij u := rfl

@[simp]
theorem weylHM_proj (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    projHom F n (weylHM F n i j hij u) =
      GeneralLinearGroup.weylMonomialSLUnit i j hij u := rfl

theorem weylHM_toSL (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    toSL F n (projHom F n (weylHM F n i j hij u)) =
      GeneralLinearGroup.weylSLUnit i j hij u := by
  rw [weylHM_proj]
  exact (GeneralLinearGroup.weylSLUnit_eq_monomialSLHom i j hij u).symm

/-! ### Shape lemmas -/

private theorem neg_one_inv (F : Type u) [Field F] :
    (-1 : Fˣ)⁻¹ = (-1 : Fˣ) := by ext; simp

private theorem neg_inv_neg_one (F : Type u) [Field F] :
    -((-1 : Fˣ)⁻¹ : Fˣ) = (1 : Fˣ) := by
  rw [neg_one_inv F]; ext; simp

private theorem weylWeight_neg_one_fun (F : Type u) [Field F] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) :
    GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) =
      fun k => if k = i then (-1 : Fˣ) else (1 : Fˣ) := by
  funext k
  simp only [GeneralLinearGroup.weylWeightUnit]
  by_cases hk_i : k = i
  · simp [hk_i]
  · by_cases hk_j : k = j
    · simp [hk_j]
    · simp [hk_i, hk_j]

private theorem permute_weyl_neg_one_fun (F : Type u) [Field F] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) :
    permute (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) =
      fun k => if k = j then (-1 : Fˣ) else (1 : Fˣ) := by
  funext k
  have h_inv : (Equiv.swap i j)⁻¹ = Equiv.swap i j := by
    simp [Equiv.swap_inv]
  simp only [permute_apply, h_inv]
  have h_w := weylWeight_neg_one_fun (F := F) hij
  by_cases hk_j : k = j
  · have h_swap : Equiv.swap i j k = i := by simp [hk_j]
    have : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1) i = (-1 : Fˣ) := by
      simpa using congrFun h_w i
    simp [this, hk_j]
  · by_cases hk_i : k = i
    · have h_swap : Equiv.swap i j k = j := by simp [hk_i]
      have : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1) j = (1 : Fˣ) := by
        simpa [hij.symm] using congrFun h_w j
      simp [h_swap, this, hk_j]
    · have h_swap : Equiv.swap i j k = k :=
        Equiv.swap_apply_of_ne_of_ne hk_i hk_j
      have : GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1) k = (1 : Fˣ) := by
        simpa [hk_i] using congrFun h_w k
      simp [h_swap, this, hk_j]

private theorem perm_weyl_neg_one_at (F : Type u) [Field F] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    permute (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) k =
      if k = j then (-1 : Fˣ) else (1 : Fˣ) :=
  congrFun (permute_weyl_neg_one_fun (F := F) hij) k

private theorem weyl_weight_mul_perm (F : Type u) [Field F] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (u : Fˣ) :
    GeneralLinearGroup.weylWeightUnit (R := F) i j hij u *
        MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) =
      GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
  funext k
  have h_perm : MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) k =
      if k = j then (-1 : Fˣ) else (1 : Fˣ) := by
    have h := perm_weyl_neg_one_at F hij k
    simpa [MatsumotoPermutationAction.permuteTuple] using h
  simp only [Pi.mul_apply, h_perm]
  by_cases hk_i : k = i
  · have hk_j : k ≠ j := by intro heq; rw [heq] at hk_i; exact hij.symm hk_i
    have h1 : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = u := by
      simp [GeneralLinearGroup.weylWeightUnit, hk_i]
    have h2 : GeneralLinearGroup.torusWeightUnit (R := F) i j hij u k = u := by
      simp [GeneralLinearGroup.torusWeightUnit, hk_i]
    have h3 : (if k = j then (-1 : Fˣ) else (1 : Fˣ)) = 1 := by simp [hk_j]
    rw [h1, h3, mul_one, h2]
  · by_cases hk_j : k = j
    · have h_mul : (-u⁻¹ : Fˣ) * (-1 : Fˣ) = u⁻¹ := by ext; simp
      have h1 : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = -u⁻¹ := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_j, hij.symm]
      have h2 : GeneralLinearGroup.torusWeightUnit (R := F) i j hij u k = u⁻¹ := by
        simp [GeneralLinearGroup.torusWeightUnit, hk_j, hij.symm]
      have h3 : (if k = j then (-1 : Fˣ) else (1 : Fˣ)) = (-1 : Fˣ) := by simp [hk_j]
      rw [h1, h3, h_mul, h2]
    · have h1 : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = 1 := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_i, hk_j]
      have h2 : GeneralLinearGroup.torusWeightUnit (R := F) i j hij u k = 1 := by
        simp [GeneralLinearGroup.torusWeightUnit, hk_i, hk_j]
      have h3 : (if k = j then (-1 : Fˣ) else (1 : Fˣ)) = 1 := by simp [hk_j]
      rw [h1, h3, mul_one, h2]

theorem weyl_base_mul (F : Type u) [Field F] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (u : Fˣ) :
    GeneralLinearGroup.weylWeightUnit (R := F) i j hij u *
        MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) =
      GeneralLinearGroup.torusWeightUnit (R := F) i j hij u :=
  weyl_weight_mul_perm F hij u

/-! ### Inversion sum vanishes -/

theorem qAdd_weyl_neg_one_zero (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) :
    qAdd F n (Equiv.swap i j)
        (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) = 0 := by
  unfold qAdd PermutationBilinearCocycle.inversionSum
  have h_eval : ∀ a b : Fˣ,
      (milnorK2Bicharacter F).eval a b = MilnorK.k2Symbol F a b := by intro a b; rfl
  simp_rw [h_eval]
  have h_w : ∀ k : Fin n,
      GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ) k =
        if k = i then (-1 : Fˣ) else (1 : Fˣ) := fun k =>
    congrFun (weylWeight_neg_one_fun (F := F) hij) k
  apply Finset.sum_eq_zero; intro p _
  apply Finset.sum_eq_zero; intro q hq
  have h_lt : p < q := (Finset.mem_filter.mp hq).2.1
  by_cases hp : p = i
  · by_cases hq_i : q = i
    · rw [hp, hq_i] at h_lt; exact absurd h_lt (lt_irrefl _)
    · rw [h_w q, ite_eq_right hq_i, MilnorK.k2Symbol_one_right]
  · rw [h_w p, ite_eq_right hp, MilnorK.k2Symbol_one_left]

/-! ### Lower sum -/

private theorem inner_sum_eq (F : Type u) [Field F] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (u : Fˣ) (p : Fin n) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
        MilnorK.k2Symbol F
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p)
          (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
            (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) q) =
      if _ : j ≤ p then
        MilnorK.k2Symbol F
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p) (-1 : Fˣ)
      else 0 := by
  classical
  have h_perm : ∀ q : Fin n,
      MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) q =
        if q = j then (-1 : Fˣ) else (1 : Fˣ) := by
    intro q
    have h := perm_weyl_neg_one_at F hij q
    -- permute = permuteTuple definitionally, but permuteTuple unfolds to permute
    simpa [MatsumotoPermutationAction.permuteTuple] using h
  have h_f : ∀ q : Fin n,
      MilnorK.k2Symbol F
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p)
          (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
            (GeneralLinearGroup.weylWeightUnit (R := F) i j hij (-1 : Fˣ)) q) =
        MilnorK.k2Symbol F
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p)
          (if q = j then (-1 : Fˣ) else (1 : Fˣ)) := fun q => by rw [h_perm q]
  simp_rw [h_f]
  have h_zero : ∀ q : Fin n, q ≠ j →
      MilnorK.k2Symbol F
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p)
          (if q = j then (-1 : Fˣ) else (1 : Fˣ)) = 0 := by
    intro q hq; simp [hq, MilnorK.k2Symbol_one_right]
  by_cases hj_le : j ≤ p
  · have hj_mem : j ∈ Finset.univ.filter (fun q : Fin n => q ≤ p) := by simp [hj_le]
    have h_sum := Finset.sum_eq_single_of_mem j hj_mem
        (fun q _ hq => h_zero q hq)
    calc ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
            MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p)
              (if q = j then (-1 : Fˣ) else (1 : Fˣ))
        = MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p)
            (if j = j then (-1 : Fˣ) else (1 : Fˣ)) := h_sum
      _ = MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p)
            (-1 : Fˣ) := by simp
      _ = if _ : j ≤ p then
            MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p) (-1)
          else 0 := by simp [hj_le]
  · have h_all_zero : ∀ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
        MilnorK.k2Symbol F
          (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p)
          (if q = j then (-1 : Fˣ) else (1 : Fˣ)) = 0 := by
      intro q hq
      have hq_j : q ≠ j := by
        intro heq
        rw [heq] at hq
        have h_le : j ≤ p := (Finset.mem_filter.mp hq).2
        exact hj_le h_le
      exact h_zero q hq_j
    calc ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
            MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p)
              (if q = j then (-1 : Fˣ) else (1 : Fˣ))
        = 0 := Finset.sum_eq_zero h_all_zero
      _ = if _ : j ≤ p then
            MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p) (-1)
          else 0 := by simp [hj_le]

def lowerSumWeyl (F : Type u) [Field F] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (u : Fˣ) : MilnorK F 2 :=
  PermutationBilinearCocycle.lowerSum (ι := Fin n)
    (milnorK2Bicharacter F)
    (GeneralLinearGroup.weylWeightUnit i j hij u)
    (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
      (GeneralLinearGroup.weylWeightUnit i j hij (-1 : Fˣ)))

theorem lowerSumWeyl_eq (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    lowerSumWeyl F n i j hij u =
      ∑ p : Fin n,
        if _ : j ≤ p then
          MilnorK.k2Symbol F
            (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p) (-1 : Fˣ)
        else 0 := by
  unfold lowerSumWeyl PermutationBilinearCocycle.lowerSum
  have h_eval : ∀ a b : Fˣ,
      (milnorK2Bicharacter F).eval a b = MilnorK.k2Symbol F a b := by intro a b; rfl
  simp_rw [h_eval]
  apply Finset.sum_congr rfl; intro p _; exact inner_sum_eq F hij u p

private theorem neg_inv_mul (F : Type u) [Field F] (u : Fˣ) :
    -u⁻¹ = (-1 : Fˣ) * u⁻¹ := by ext; simp

theorem lowerSumWeyl_explicit (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    lowerSumWeyl F n i j hij u =
      (if _ : j ≤ i then MilnorK.k2Symbol F u (-1 : Fˣ) else 0) +
        MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ) := by
  rw [lowerSumWeyl_eq]
  let f : Fin n → MilnorK F 2 := fun p =>
    if _ : j ≤ p then
      MilnorK.k2Symbol F (GeneralLinearGroup.weylWeightUnit i j hij u p) (-1 : Fˣ)
    else 0
  have h_f_eq : ∀ p : Fin n,
      f p = if p = i then (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0)
            else if p = j then MilnorK.k2Symbol F (-u⁻¹) (-1)
            else 0 := by
    intro p
    simp only [f]
    by_cases hp_i : p = i
    · subst hp_i
      simp [GeneralLinearGroup.weylWeightUnit]
    · by_cases hp_j : p = j
      · subst hp_j
        simp [GeneralLinearGroup.weylWeightUnit, hp_i]
      · have hw : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u p = 1 := by
          simp [GeneralLinearGroup.weylWeightUnit, hp_i, hp_j]
        simp [hw, MilnorK.k2Symbol_one_left, hp_i, hp_j]
  have h_sum_congr : (∑ p : Fin n, f p) =
      ∑ p : Fin n, (if p = i then (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0)
                    else if p = j then MilnorK.k2Symbol F (-u⁻¹) (-1)
                    else (0 : MilnorK F 2)) := by
    apply Finset.sum_congr rfl; intro p _; exact h_f_eq p
  rw [h_sum_congr]
  let g : Fin n → MilnorK F 2 := fun p =>
    if p = i then (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0)
    else if p = j then MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ)
    else 0
  have h_g : (∑ p : Fin n,
      if p = i then (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0)
      else if p = j then MilnorK.k2Symbol F (-u⁻¹) (-1)
      else (0 : MilnorK F 2)) = ∑ p ∈ Finset.univ, g p := rfl
  rw [h_g]
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hj_mem_erase : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    rw [Finset.mem_erase]; exact ⟨hij.symm, Finset.mem_univ j⟩
  have h_add1 : ∑ p ∈ Finset.univ, g p =
      g i + ∑ p ∈ (Finset.univ : Finset (Fin n)).erase i, g p :=
    (Finset.add_sum_erase _ g hi_mem).symm
  have hg_i : g i = if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0 := by simp [g]
  have h_add2 : ∑ p ∈ (Finset.univ : Finset (Fin n)).erase i, g p =
      g j + ∑ p ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, g p :=
    (Finset.add_sum_erase _ g hj_mem_erase).symm
  have hg_j : g j = MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ) := by simp [g, hij.symm]
  have h_zero : ∑ p ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, g p = 0 := by
    apply Finset.sum_eq_zero; intro k hk
    have hk_ne_j : k ≠ j := (Finset.mem_erase.mp hk).1
    have hk_mem_erase_i : k ∈ (Finset.univ : Finset (Fin n)).erase i :=
      Finset.mem_of_mem_erase hk
    have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_mem_erase_i).1
    simp [g, hk_ne_i, hk_ne_j]
  calc ∑ p ∈ Finset.univ, g p
      = g i + ∑ p ∈ Finset.univ.erase i, g p := h_add1
    _ = g i + (g j + ∑ p ∈ (Finset.univ.erase i).erase j, g p) := by rw [h_add2]
    _ = g i + (g j + 0) := by rw [h_zero]
    _ = g i + g j := by abel
    _ = (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0) +
          MilnorK.k2Symbol F (-u⁻¹) (-1) := by rw [hg_i, hg_j]

private theorem k2_neg_inv_eq (F : Type u) [Field F] (u : Fˣ) :
    MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ) =
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) +
        (- MilnorK.k2Symbol F u (-1 : Fˣ)) := by
  have h_eq : (-u⁻¹ : Fˣ) = (-1 : Fˣ) * u⁻¹ := neg_inv_mul F u
  calc MilnorK.k2Symbol F (-u⁻¹ : Fˣ) (-1 : Fˣ)
      = MilnorK.k2Symbol F ((-1 : Fˣ) * u⁻¹) (-1 : Fˣ) := by rw [← h_eq]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) +
          MilnorK.k2Symbol F (u⁻¹ : Fˣ) (-1 : Fˣ) := by
          rw [MilnorK.k2Symbol_mul_left]
    _ = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) +
          (- MilnorK.k2Symbol F u (-1 : Fˣ)) := by
          rw [MilnorK.k2Symbol_inv_left]

theorem lowerSumWeyl_lt (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) (h_lt : i < j) :
    lowerSumWeyl F n i j hij u =
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) -
        MilnorK.k2Symbol F u (-1 : Fˣ) := by
  rw [lowerSumWeyl_explicit]
  have hj_le : ¬ j ≤ i := not_le.mpr h_lt
  have h_if : (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0) = 0 := by simp [hj_le]
  rw [h_if, zero_add, k2_neg_inv_eq F u, sub_eq_add_neg]

theorem lowerSumWeyl_gt (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) (h_gt : ¬ i < j) :
    lowerSumWeyl F n i j hij u =
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) := by
  rw [lowerSumWeyl_explicit]
  have hj_le : j ≤ i := le_of_not_gt h_gt
  have h_if : (if _ : j ≤ i then MilnorK.k2Symbol F u (-1) else 0) =
      MilnorK.k2Symbol F u (-1) := by simp [hj_le]
  rw [h_if, k2_neg_inv_eq F u]
  abel

/-! ### Product relation -/

private theorem two_neg_one_zero (F : Type u) [Field F] :
    MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) +
      MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) = 0 := by
  have h_one : (-1 : Fˣ) * (-1 : Fˣ) = 1 := by ext; simp
  have h : MilnorK.k2Symbol F (-1 : Fˣ) ((-1 : Fˣ) * (-1 : Fˣ)) = 0 := by
    rw [h_one, MilnorK.k2Symbol_one_right]
  rw [MilnorK.k2Symbol_mul_right] at h; exact h

private theorem weylCoeff_neg_one (F : Type u) [Field F] {n' : ℕ}
    {i' j' : Fin n'} :
    weylK2Coeff F i' j' (-1 : Fˣ) = MilnorK.k2Symbol F (-1 : Fˣ) (-1 : Fˣ) := by
  unfold weylK2Coeff; by_cases h : i' < j' <;> simp [h]

theorem coeff_product_eq (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    weylK2Coeff F i j u + weylK2Coeff F i j (-1 : Fˣ) +
        lowerSumWeyl F n i j hij u =
      if _ : i < j then 0 else MilnorK.k2Symbol F u u := by
  by_cases h_lt : i < j
  · rw [weylK2Coeff_lt h_lt, weylCoeff_neg_one,
      lowerSumWeyl_lt F n i j hij u h_lt]
    have h2 := two_neg_one_zero (F := F)
    calc MilnorK.k2Symbol F u (-1) + MilnorK.k2Symbol F (-1) (-1) +
            (MilnorK.k2Symbol F (-1) (-1) - MilnorK.k2Symbol F u (-1))
        = MilnorK.k2Symbol F (-1) (-1) + MilnorK.k2Symbol F (-1) (-1) := by abel
      _ = 0 := h2
      _ = if _ : i < j then 0 else MilnorK.k2Symbol F u u := by simp [h_lt]
  · rw [weylK2Coeff_gt (show ¬ i < j from h_lt), weylCoeff_neg_one,
      lowerSumWeyl_gt F n i j hij u h_lt]
    have h2 := two_neg_one_zero (F := F)
    calc MilnorK.k2Symbol F u u + MilnorK.k2Symbol F (-1) (-1) +
            MilnorK.k2Symbol F (-1) (-1)
        = MilnorK.k2Symbol F u u +
          (MilnorK.k2Symbol F (-1) (-1) + MilnorK.k2Symbol F (-1) (-1)) := by abel
      _ = MilnorK.k2Symbol F u u + 0 := by rw [h2]
      _ = MilnorK.k2Symbol F u u := by abel
      _ = if _ : i < j then 0 else MilnorK.k2Symbol F u u := by simp [h_lt]

/-! ### Ambient naturality -/

private theorem units_map_neg_one (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) : Units.map f.toMonoidHom (-1 : Fˣ) = (-1 : Kˣ) := by ext; simp

private theorem units_map_inv (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) (u : Fˣ) :
    Units.map f.toMonoidHom (u⁻¹) = (Units.map f.toMonoidHom u)⁻¹ := by
  ext; simp

private theorem units_map_neg_inv (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) (u : Fˣ) :
    Units.map f.toMonoidHom (-u⁻¹ : Fˣ) =
      -(Units.map f.toMonoidHom u)⁻¹ := by
  calc Units.map f.toMonoidHom (-u⁻¹ : Fˣ)
      = Units.map f.toMonoidHom ((-1 : Fˣ) * u⁻¹) := by rw [← neg_inv_mul F u]
    _ = Units.map f.toMonoidHom (-1 : Fˣ) *
          Units.map f.toMonoidHom (u⁻¹ : Fˣ) := by
        rw [MonoidHom.map_mul]
    _ = (-1 : Kˣ) * (Units.map f.toMonoidHom u)⁻¹ := by
        rw [units_map_neg_one F K f, units_map_inv F K f u]
    _ = -(Units.map f.toMonoidHom u)⁻¹ := by rw [← neg_inv_mul K]

private theorem weylWeight_map (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) {n : ℕ} {i j : Fin n} (hij : i ≠ j) (u : Fˣ) :
    unitsTupleMap f n (GeneralLinearGroup.weylWeightUnit (R := F) i j hij u) =
      GeneralLinearGroup.weylWeightUnit (R := K) i j hij
        (Units.map f.toMonoidHom u) := by
  funext k; simp only [unitsTupleMap_apply]
  by_cases hk_i : k = i
  · have h1 : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = u := by
      simp [GeneralLinearGroup.weylWeightUnit, hk_i]
    have h2 : GeneralLinearGroup.weylWeightUnit (R := K) i j hij
        (Units.map f.toMonoidHom u) k = Units.map f.toMonoidHom u := by
      simp [GeneralLinearGroup.weylWeightUnit, hk_i]
    rw [h1, h2]
  · by_cases hk_j : k = j
    · have h1 : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = -u⁻¹ := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_j, hij.symm]
      have h2 : GeneralLinearGroup.weylWeightUnit (R := K) i j hij
          (Units.map f.toMonoidHom u) k = -(Units.map f.toMonoidHom u)⁻¹ := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_j, hij.symm]
      calc Units.map f.toMonoidHom
            (GeneralLinearGroup.weylWeightUnit i j hij u k)
          = Units.map f.toMonoidHom (-u⁻¹ : Fˣ) := by rw [h1]
        _ = -(Units.map f.toMonoidHom u)⁻¹ := units_map_neg_inv F K f u
        _ = GeneralLinearGroup.weylWeightUnit i j hij
              (Units.map f.toMonoidHom u) k := by rw [h2]
    · have h1 : GeneralLinearGroup.weylWeightUnit (R := F) i j hij u k = 1 := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_i, hk_j]
      have h2 : GeneralLinearGroup.weylWeightUnit (R := K) i j hij
          (Units.map f.toMonoidHom u) k = 1 := by
        simp [GeneralLinearGroup.weylWeightUnit, hk_i, hk_j]
      calc Units.map f.toMonoidHom
            (GeneralLinearGroup.weylWeightUnit i j hij u k)
          = Units.map f.toMonoidHom (1 : Fˣ) := by rw [h1]
        _ = 1 := by simp
        _ = GeneralLinearGroup.weylWeightUnit i j hij
              (Units.map f.toMonoidHom u) k := by rw [h2]

private theorem weylK2Coeff_map (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) {n : ℕ} {i j : Fin n} (u : Fˣ) :
    MilnorK.map f 2 (weylK2Coeff F i j u) =
      weylK2Coeff K i j (Units.map f.toMonoidHom u) := by
  unfold weylK2Coeff
  by_cases h : i < j
  · simp only [h, ↓reduceIte, MilnorK.map_k2Symbol, units_map_neg_one F K f]
  · simp only [h, ↓reduceIte, MilnorK.map_k2Symbol]

theorem ambientWeylLift_naturality (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    ambientMonomialLiftMap (F := F) (K := K) f n
        (ambientWeylLift F n i j hij u) =
      ambientWeylLift K n i j hij (Units.map f.toMonoidHom u) := by
  apply SemidirectProduct.ext
  · apply HAll.ext
    · calc (ambientMonomialLiftMap f n (ambientWeylLift F n i j hij u)).left.base
          = (HAllMap f n (weylHAll F n i j hij u)).base := rfl
        _ = unitsTupleMap f n (weylHAll F n i j hij u).base := rfl
        _ = unitsTupleMap f n (GeneralLinearGroup.weylWeightUnit i j hij u) := rfl
        _ = GeneralLinearGroup.weylWeightUnit i j hij
              (Units.map f.toMonoidHom u) :=
            weylWeight_map F K f hij u
        _ = (weylHAll K n i j hij (Units.map f.toMonoidHom u)).base := rfl
        _ = (ambientWeylLift K n i j hij (Units.map f.toMonoidHom u)).left.base := rfl
    · have h_map :
          (HAllMap (F := F) (K := K) f n
            (weylHAll F n i j hij u)).coeff =
            MilnorK.mapMultiplicative f 2 (weylHAll F n i j hij u).coeff :=
        HAllMap_coeff f n (weylHAll F n i j hij u)
      have h_coeff : (weylHAll F n i j hij u).coeff =
          Multiplicative.ofAdd (weylK2Coeff F i j u) := rfl
      have h_coeff_K : (weylHAll K n i j hij (Units.map f.toMonoidHom u)).coeff =
          Multiplicative.ofAdd (weylK2Coeff K i j (Units.map f.toMonoidHom u)) := rfl
      calc (ambientMonomialLiftMap f n (ambientWeylLift F n i j hij u)).left.coeff
          = (HAllMap f n (weylHAll F n i j hij u)).coeff := rfl
        _ = MilnorK.mapMultiplicative f 2 (weylHAll F n i j hij u).coeff := h_map
        _ = MilnorK.mapMultiplicative f 2
              (Multiplicative.ofAdd (weylK2Coeff F i j u)) := by rw [h_coeff]
        _ = Multiplicative.ofAdd (MilnorK.map f 2 (weylK2Coeff F i j u)) := by
            rw [MilnorK.mapMultiplicative_ofAdd_eq_map]
        _ = Multiplicative.ofAdd (weylK2Coeff K i j (Units.map f.toMonoidHom u)) := by
            rw [weylK2Coeff_map F K f u]
        _ = (weylHAll K n i j hij (Units.map f.toMonoidHom u)).coeff := by
            rw [h_coeff_K]
        _ = (ambientWeylLift K n i j hij (Units.map f.toMonoidHom u)).left.coeff := rfl
  · rfl

/-! ### Main product relation -/

private theorem swap_mul_swap {n : ℕ} {i j : Fin n} (_hij : i ≠ j) :
    Equiv.swap i j * Equiv.swap i j = (1 : Equiv.Perm (Fin n)) := by
  have h_inv : (Equiv.swap i j)⁻¹ = Equiv.swap i j := by simp [Equiv.swap_inv]
  calc Equiv.swap i j * Equiv.swap i j
      = Equiv.swap i j * (Equiv.swap i j)⁻¹ := by rw [h_inv]
    _ = 1 := mul_inv_cancel _

private theorem d_ij_val_eq_torus (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    (d_ij F n i j hij u).val =
      GeneralLinearGroup.torusWeightUnit (R := F) i j hij u := by
  have h_bridge := diagToMonomialBase_eq_torusWeight F n hij u
  have h_left : (diagToMonomialBase F n (d_ij F n i j hij u)).left =
      (GeneralLinearGroup.torusMonomialBaseUnit i j hij u).left := by rw [h_bridge]
  simpa [diagToMonomialBase, GeneralLinearGroup.torusMonomialBaseUnit] using h_left

theorem ambient_mul_eq (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    ambientWeylLift F n i j hij u * ambientWeylLift F n i j hij (-1 : Fˣ) =
      HAllToMonomialLift F n (HToHAll F n (h_ij F n i j hij u)) := by
  apply SemidirectProduct.ext
  · apply HAll.ext
    · calc (ambientWeylLift F n i j hij u *
            ambientWeylLift F n i j hij (-1 : Fˣ)).left.base
          = (weylHAll F n i j hij u *
              MatsumotoPermutationAction.permCompatibleHom F n
                (Equiv.swap i j) (weylHAll F n i j hij (-1 : Fˣ))).base := rfl
        _ = (weylHAll F n i j hij u).base *
            (MatsumotoPermutationAction.permCompatibleHom F n
              (Equiv.swap i j) (weylHAll F n i j hij (-1 : Fˣ))).base := rfl
        _ = GeneralLinearGroup.weylWeightUnit i j hij u *
            MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
              (GeneralLinearGroup.weylWeightUnit i j hij (-1 : Fˣ)) := rfl
        _ = GeneralLinearGroup.torusWeightUnit i j hij u :=
            weyl_base_mul F hij u
        _ = (d_ij F n i j hij u).val := (d_ij_val_eq_torus F n i j hij u).symm
        _ = (HToHAll F n (h_ij F n i j hij u)).base := by
            simp [HToHAll_base, h_ij_diag]
    · have h_q0 : Multiplicative.ofAdd
            (qAdd F n (Equiv.swap i j)
              (GeneralLinearGroup.weylWeightUnit i j hij (-1 : Fˣ))) = 1 := by
          rw [qAdd_weyl_neg_one_zero F n i j hij, ofAdd_zero]
      calc (ambientWeylLift F n i j hij u *
            ambientWeylLift F n i j hij (-1 : Fˣ)).left.coeff
          = (weylHAll F n i j hij u *
              MatsumotoPermutationAction.permCompatibleHom F n
                (Equiv.swap i j) (weylHAll F n i j hij (-1 : Fˣ))).coeff := rfl
        _ = (weylHAll F n i j hij u).coeff *
              (MatsumotoPermutationAction.permCompatibleHom F n
                (Equiv.swap i j) (weylHAll F n i j hij (-1 : Fˣ))).coeff *
              alphaAll F n
                (weylHAll F n i j hij u).base
                (MatsumotoPermutationAction.permCompatibleHom F n
                  (Equiv.swap i j) (weylHAll F n i j hij (-1 : Fˣ))).base := rfl
        _ = Multiplicative.ofAdd (weylK2Coeff F i j u) *
              (Multiplicative.ofAdd (weylK2Coeff F i j (-1 : Fˣ)) *
                Multiplicative.ofAdd (qAdd F n (Equiv.swap i j)
                  (GeneralLinearGroup.weylWeightUnit i j hij (-1 : Fˣ)))) *
              alphaAll F n
                (GeneralLinearGroup.weylWeightUnit i j hij u)
                (MatsumotoPermutationAction.permuteTuple F n (Equiv.swap i j)
                  (GeneralLinearGroup.weylWeightUnit i j hij (-1 : Fˣ))) := by
            simp only [weylHAll,
              MatsumotoPermutationAction.permCompatibleHom_coeff,
              MatsumotoPermutationAction.permCompatibleHom_base]
        _ = Multiplicative.ofAdd (weylK2Coeff F i j u) *
              (Multiplicative.ofAdd (weylK2Coeff F i j (-1 : Fˣ)) *
                Multiplicative.ofAdd (qAdd F n (Equiv.swap i j)
                  (GeneralLinearGroup.weylWeightUnit i j hij (-1 : Fˣ)))) *
              Multiplicative.ofAdd (lowerSumWeyl F n i j hij u) := rfl
        _ = Multiplicative.ofAdd (weylK2Coeff F i j u) *
              Multiplicative.ofAdd (weylK2Coeff F i j (-1 : Fˣ)) *
              Multiplicative.ofAdd (lowerSumWeyl F n i j hij u) := by
            rw [h_q0, mul_one]
        _ = Multiplicative.ofAdd
                (weylK2Coeff F i j u + weylK2Coeff F i j (-1 : Fˣ) +
                  lowerSumWeyl F n i j hij u) := by
            rw [← ofAdd_add, ← ofAdd_add]
        _ = Multiplicative.ofAdd
              (if _ : i < j then 0 else MilnorK.k2Symbol F u u) := by
            rw [coeff_product_eq F n i j hij u]
        _ = (HToHAll F n (h_ij F n i j hij u)).coeff := by
            have h_base := HToHAll_coeff (F := F) n (h_ij F n i j hij u)
            by_cases h_lt : i < j
            · have h1 : (h_ij F n i j hij u).coeff = 1 := h_ij_coeff_lt F n hij u h_lt
              simp [h_base, h1, h_lt, ofAdd_zero]
            · have h1 : (h_ij F n i j hij u).coeff =
                    Multiplicative.ofAdd (MilnorK.k2Symbol F u u) := by
                  have hgt := h_ij_coeff_gt F n hij u h_lt
                  simpa using hgt
              simp [h_base, h1, h_lt]
        _ = (HAllToMonomialLift F n (HToHAll F n (h_ij F n i j hij u))).left.coeff := rfl
  · calc (ambientWeylLift F n i j hij u *
          ambientWeylLift F n i j hij (-1 : Fˣ)).right
        = Equiv.swap i j * Equiv.swap i j := rfl
      _ = 1 := swap_mul_swap hij
      _ = (HAllToMonomialLift F n (HToHAll F n (h_ij F n i j hij u))).right := rfl

private theorem weylSL_mul_eq_torus (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    GeneralLinearGroup.weylMonomialSLUnit i j hij u *
        GeneralLinearGroup.weylMonomialSLUnit i j hij (-1 : Fˣ) =
      GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
  apply Subtype.ext
  calc (GeneralLinearGroup.weylMonomialSLUnit i j hij u *
          GeneralLinearGroup.weylMonomialSLUnit i j hij (-1 : Fˣ) : M F n).val
      = GeneralLinearGroup.weylMonomialBaseUnit i j hij u *
          GeneralLinearGroup.weylMonomialBaseUnit i j hij (-1 : Fˣ) := rfl
    _ = GeneralLinearGroup.torusMonomialBaseUnit i j hij u :=
        (GeneralLinearGroup.torusMonomialBaseUnit_eq_mul i j hij u).symm
    _ = (GeneralLinearGroup.torusMonomialSLUnit i j hij u : M F n).val := rfl

/-- Crucial exact lift relation:
`w_{ij}(u) * w_{ij}(-1) = HToHM (h_{ij}(u))` in `HM`. -/
theorem weylHM_mul_weylHM_neg_one (F : Type u) [Field F] (n : ℕ)
    (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    weylHM F n i j hij u * weylHM F n i j hij (-1 : Fˣ) =
      HToHM F n (h_ij F n i j hij u) := by
  have h_amb : ambientLiftHom F n
        (weylHM F n i j hij u * weylHM F n i j hij (-1 : Fˣ)) =
      ambientLiftHom F n (HToHM F n (h_ij F n i j hij u)) := by
    calc ambientLiftHom F n (weylHM F n i j hij u * weylHM F n i j hij (-1 : Fˣ))
        = ambientLiftHom F n (weylHM F n i j hij u) *
          ambientLiftHom F n (weylHM F n i j hij (-1 : Fˣ)) := by rw [map_mul]
      _ = ambientWeylLift F n i j hij u *
          ambientWeylLift F n i j hij (-1 : Fˣ) := by rw [weylHM_ambient, weylHM_ambient]
      _ = HAllToMonomialLift F n (HToHAll F n (h_ij F n i j hij u)) :=
          ambient_mul_eq F n i j hij u
      _ = ambientLiftHom F n (HToHM F n (h_ij F n i j hij u)) := by
          rw [HToHM_ambientLiftHom_val]
  have h_proj : projHom F n
        (weylHM F n i j hij u * weylHM F n i j hij (-1 : Fˣ)) =
      projHom F n (HToHM F n (h_ij F n i j hij u)) := by
    calc projHom F n (weylHM F n i j hij u * weylHM F n i j hij (-1 : Fˣ))
        = projHom F n (weylHM F n i j hij u) *
          projHom F n (weylHM F n i j hij (-1 : Fˣ)) := by rw [map_mul]
      _ = GeneralLinearGroup.weylMonomialSLUnit i j hij u *
          GeneralLinearGroup.weylMonomialSLUnit i j hij (-1 : Fˣ) := by
          rw [weylHM_proj, weylHM_proj]
      _ = GeneralLinearGroup.torusMonomialSLUnit i j hij u :=
          weylSL_mul_eq_torus F n i j hij u
      _ = projHom F n (HToHM F n (h_ij F n i j hij u)) := by
          rw [HToHM_h_ij_proj]
  apply Subtype.ext; exact Prod.ext h_amb h_proj

theorem weylHM_sq_neg_one (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) :
    weylHM F n i j hij (-1 : Fˣ) * weylHM F n i j hij (-1 : Fˣ) =
      HToHM F n (h_ij F n i j hij (-1 : Fˣ)) := by
  have h := weylHM_mul_weylHM_neg_one (F := F) n i j hij (-1 : Fˣ)
  simpa using h

theorem weylHM_eq_HToHM_mul_inv (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    weylHM F n i j hij u =
      HToHM F n (h_ij F n i j hij u) * (weylHM F n i j hij (-1 : Fˣ))⁻¹ := by
  have h_mul := weylHM_mul_weylHM_neg_one (F := F) n i j hij u
  calc weylHM F n i j hij u
      = weylHM F n i j hij u * 1 := by rw [mul_one]
    _ = weylHM F n i j hij u *
          (weylHM F n i j hij (-1 : Fˣ) * (weylHM F n i j hij (-1 : Fˣ))⁻¹) := by
          rw [mul_inv_cancel]
    _ = weylHM F n i j hij u * weylHM F n i j hij (-1 : Fˣ) *
          (weylHM F n i j hij (-1 : Fˣ))⁻¹ := by rw [mul_assoc]
    _ = HToHM F n (h_ij F n i j hij u) * (weylHM F n i j hij (-1 : Fˣ))⁻¹ := by
          rw [h_mul]

@[simp]
theorem projHom_weylHM_inv (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    projHom F n (weylHM F n i j hij u)⁻¹ =
      (GeneralLinearGroup.weylMonomialSLUnit i j hij u)⁻¹ := by
  rw [map_inv, weylHM_proj]

@[simp]
theorem ambientLiftHom_weylHM_inv (F : Type u) [Field F] (n : ℕ) (i j : Fin n)
    (hij : i ≠ j) (u : Fˣ) :
    ambientLiftHom F n (weylHM F n i j hij u)⁻¹ =
      (ambientWeylLift F n i j hij u)⁻¹ := by
  rw [map_inv, weylHM_ambient]

/-! ### Naturality for `weylHM` -/

theorem weylHM_naturality (F : Type u) (K : Type v) [Field F] [Field K]
    (f : F →+* K) (n : ℕ) (i j : Fin n) (hij : i ≠ j) (u : Fˣ) :
    HMMap (F := F) (K := K) f n (weylHM F n i j hij u) =
      weylHM K n i j hij (Units.map f.toMonoidHom u) := by
  apply Subtype.ext; apply Prod.ext
  · calc (HMMap f n (weylHM F n i j hij u)).val.1
        = ambientLiftHom K n (HMMap f n (weylHM F n i j hij u)) := rfl
      _ = ambientMonomialLiftMap f n (ambientLiftHom F n (weylHM F n i j hij u)) := by
          rw [HMMap_fst]
      _ = ambientMonomialLiftMap f n (ambientWeylLift F n i j hij u) := by
          rw [weylHM_ambient]
      _ = ambientWeylLift K n i j hij (Units.map f.toMonoidHom u) :=
          ambientWeylLift_naturality F K f n i j hij u
      _ = (weylHM K n i j hij (Units.map f.toMonoidHom u)).val.1 := rfl
  · calc (HMMap f n (weylHM F n i j hij u)).val.2
        = projHom K n (HMMap f n (weylHM F n i j hij u)) := rfl
      _ = MMap f n (projHom F n (weylHM F n i j hij u)) := by rw [HMMap_snd]
      _ = MMap f n (GeneralLinearGroup.weylMonomialSLUnit i j hij u) := by
          rw [weylHM_proj]
      _ = GeneralLinearGroup.weylMonomialSLUnit i j hij
            (Units.map f.toMonoidHom u) :=
          GeneralLinearGroup.weylMonomialSLUnit_map f i j hij u
      _ = (weylHM K n i j hij (Units.map f.toMonoidHom u)).val.2 := rfl

end MatsumotoWeylLift

end
