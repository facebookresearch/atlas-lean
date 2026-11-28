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

public import MathlibExt.GroupTheory.PermutationBilinearCocycle
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open Finset
open PermutationBilinearCocycle

universe uA uB uA' uB'

namespace PermutationBilinearTitsAction

variable {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]
variable {A' : Type uA'} {B' : Type uB'}
  [CommGroup A'] [AddCommGroup B']

section TupleProd

variable {n : ℕ}

/-- The product of the original finite tuple coordinates. -/
def tupleProd (u : Fin n → A) : A :=
  Finset.univ.prod fun i => u i

@[simp]
theorem tupleProd_one :
    tupleProd (n := n) (A := A) (1 : Fin n → A) = 1 := by
  unfold tupleProd
  simp

theorem tupleProd_mul (u v : Fin n → A) :
    tupleProd (u * v) = tupleProd u * tupleProd v := by
  unfold tupleProd
  have h1 : (fun i : Fin n => (u * v) i) =
      (fun i => u i * v i) := by
    funext i
    simp [Pi.mul_apply]
  rw [h1, Finset.prod_mul_distrib]

theorem tupleProd_permute (σ : Equiv.Perm (Fin n))
    (u : Fin n → A) :
    tupleProd (permute σ u) = tupleProd u := by
  unfold tupleProd permute
  calc Finset.univ.prod (fun i : Fin n => u (σ⁻¹ i))
      = Finset.univ.prod (fun i => u (σ.symm i)) := rfl
    _ = ∏ i : Fin n, u (σ.symm i) := rfl
    _ = ∏ i : Fin n, u i := Equiv.prod_comp σ.symm _
    _ = Finset.univ.prod (fun i : Fin n => u i) := rfl

theorem tupleProd_mapTuple (f : A →* A')
    (u : Fin n → A) :
    tupleProd (mapTuple (f := f) u) =
      f (tupleProd u) := by
  unfold tupleProd mapTuple
  calc Finset.univ.prod (fun i : Fin n => f (u i))
      = f (Finset.univ.prod fun i => u i) := by
        rw [← map_prod f (fun i => u i) Finset.univ]

theorem tupleProd_naturality
    {b : SkewBicharacter A B}
    {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b')
    (u : Fin n → A) :
    φ.source (tupleProd u) =
      tupleProd (mapTuple (f := φ.source) u) := by
  exact (tupleProd_mapTuple (f := φ.source) u).symm

@[simp]
theorem tupleProd_mapTuple_symm (f : A →* A')
    (u : Fin n → A) :
    f (tupleProd u) = tupleProd (mapTuple f u) :=
  (tupleProd_mapTuple f u).symm

end TupleProd

section Parity

variable {n : ℕ}

/-- The coefficient unit associated with the parity of the given permutation. -/
def parityUnit (eps : A) (σ : Equiv.Perm (Fin n)) : A :=
  if Equiv.Perm.sign σ = 1 then 1 else eps

@[simp]
theorem parityUnit_one (eps : A) :
    parityUnit (n := n) eps (1 : Equiv.Perm (Fin n)) = 1 := by
  unfold parityUnit
  have h : Equiv.Perm.sign
      (1 : Equiv.Perm (Fin n)) = 1 := by
    simp
  simp [h]

theorem parityUnit_eq_one_of_sign_eq_one
    {eps : A} {σ : Equiv.Perm (Fin n)}
    (h : Equiv.Perm.sign σ = 1) :
    parityUnit eps σ = 1 := by
  unfold parityUnit
  simp [h]

theorem parityUnit_eq_eps_of_sign_ne_one
    {eps : A} {σ : Equiv.Perm (Fin n)}
    (h : Equiv.Perm.sign σ ≠ 1) :
    parityUnit eps σ = eps := by
  unfold parityUnit
  simp [h]

private lemma intUnits_eq_one_or_neg_one
    (u : Units Int) : u = 1 ∨ u = -1 := by
  have h_isUnit : IsUnit u.val := ⟨u, rfl⟩
  have h_or : u.val = 1 ∨ u.val = -1 := by
    rwa [Int.isUnit_iff] at h_isUnit
  cases h_or with
  | inl h1 =>
    left
    ext
    simp [h1]
  | inr h2 =>
    right
    ext
    simp [h2]

private lemma sign_ne_one_imp_eq_neg_one
    {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : Equiv.Perm.sign σ ≠ 1) :
    Equiv.Perm.sign σ = -1 := by
  have h_or := intUnits_eq_one_or_neg_one
    (Equiv.Perm.sign σ)
  cases h_or with
  | inl h1 => exact absurd h1 h
  | inr h2 => exact h2

theorem parityUnit_mul {eps : A}
    (heps : eps * eps = 1)
    (σ τ : Equiv.Perm (Fin n)) :
    parityUnit eps (σ * τ) =
      parityUnit eps σ * parityUnit eps τ := by
  have hsign_mul :
      Equiv.Perm.sign (σ * τ) =
        Equiv.Perm.sign σ * Equiv.Perm.sign τ := by
    simp
  by_cases hs : Equiv.Perm.sign σ = 1
  · by_cases ht : Equiv.Perm.sign τ = 1
    · have hst : Equiv.Perm.sign (σ * τ) = 1 := by
        rw [hsign_mul, hs, ht, mul_one]
      rw [parityUnit_eq_one_of_sign_eq_one hst,
        parityUnit_eq_one_of_sign_eq_one hs,
        parityUnit_eq_one_of_sign_eq_one ht, mul_one]
    · have h_t_neg : Equiv.Perm.sign τ = -1 :=
        sign_ne_one_imp_eq_neg_one ht
      have hst : Equiv.Perm.sign (σ * τ) ≠ 1 := by
        rw [hsign_mul, hs, one_mul]
        exact ht
      have hst_eq : Equiv.Perm.sign (σ * τ) = -1 :=
        sign_ne_one_imp_eq_neg_one hst
      rw [parityUnit_eq_eps_of_sign_ne_one hst,
        parityUnit_eq_one_of_sign_eq_one hs,
        parityUnit_eq_eps_of_sign_ne_one ht, one_mul]
  · by_cases ht : Equiv.Perm.sign τ = 1
    · have h_s_neg : Equiv.Perm.sign σ = -1 :=
        sign_ne_one_imp_eq_neg_one hs
      have hst : Equiv.Perm.sign (σ * τ) ≠ 1 := by
        rw [hsign_mul, ht, mul_one]
        exact hs
      rw [parityUnit_eq_eps_of_sign_ne_one hst,
        parityUnit_eq_eps_of_sign_ne_one hs,
        parityUnit_eq_one_of_sign_eq_one ht, mul_one]
    · have h_s_neg : Equiv.Perm.sign σ = -1 :=
        sign_ne_one_imp_eq_neg_one hs
      have h_t_neg : Equiv.Perm.sign τ = -1 :=
        sign_ne_one_imp_eq_neg_one ht
      have hst : Equiv.Perm.sign (σ * τ) = 1 := by
        rw [hsign_mul, h_s_neg, h_t_neg, neg_mul_neg, one_mul]
      rw [parityUnit_eq_one_of_sign_eq_one hst,
        parityUnit_eq_eps_of_sign_ne_one hs,
        parityUnit_eq_eps_of_sign_ne_one ht, heps]

theorem parityUnit_naturality
    {b : SkewBicharacter A B}
    {b' : SkewBicharacter A' B'}
    (φ : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'}
    (hε : φ.source eps = eps')
    (σ : Equiv.Perm (Fin n)) :
    φ.source (parityUnit eps σ) =
      parityUnit eps' σ := by
  by_cases hs : Equiv.Perm.sign σ = 1
  · rw [parityUnit_eq_one_of_sign_eq_one hs,
      parityUnit_eq_one_of_sign_eq_one hs, map_one]
  · rw [parityUnit_eq_eps_of_sign_ne_one hs,
      parityUnit_eq_eps_of_sign_ne_one hs, hε]

end Parity

section EpsPow

variable {A : Type uA} [CommGroup A]

theorem eps_pow_two {eps : A} (heps : eps * eps = 1) :
    eps ^ (2 : ℕ) = 1 := by
  rw [pow_two, heps]

theorem eps_pow_two_mul {eps : A}
    (heps : eps * eps = 1) (k : ℕ) :
    eps ^ (2 * k) = (1 : A) := by
  have h : eps ^ (2 * k) = (eps ^ 2) ^ k := by
    rw [pow_mul]
  rw [h, eps_pow_two heps, one_pow]

theorem eps_pow_mul_self {eps : A}
    (heps : eps * eps = 1) (k : ℕ) :
    eps ^ k * eps ^ k = (1 : A) := by
  have h : eps ^ k * eps ^ k = eps ^ (k + k) := by
    rw [← pow_add]
  rw [h]
  have h2 : k + k = 2 * k := by
    rw [Nat.two_mul]
  rw [h2, eps_pow_two_mul heps]

end EpsPow

section OrientUnit

variable {n : ℕ} {A : Type uA} [CommGroup A]
variable {eps : A}

/-- The coefficient unit associated with the parity of the specified index. -/
def indexParityUnit (eps : A) (i : Fin n) : A :=
  eps ^ i.val

/-- The unit-valued orientation correction for the specified indices. -/
def orientUnit (eps : A)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : A :=
  parityUnit eps σ * indexParityUnit eps i *
    indexParityUnit eps (σ i)

theorem indexParityUnit_mul_self {eps : A}
    (heps : eps * eps = 1) (i : Fin n) :
    indexParityUnit (n := n) eps i *
      indexParityUnit eps i = 1 :=
  eps_pow_mul_self heps i.val

theorem indexParityUnit_naturality
    {A' : Type*} [CommGroup A']
    (f : A →* A') (i : Fin n) :
    f (indexParityUnit eps i) =
      indexParityUnit (f eps) i := by
  unfold indexParityUnit
  rw [f.map_pow]

theorem orientUnit_eq_parity_mul_index
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    orientUnit eps σ i =
      parityUnit eps σ * (eps ^ i.val) *
        (eps ^ (σ i).val) := rfl

theorem orientUnit_one (heps : eps * eps = 1)
    (i : Fin n) :
    orientUnit (n := n) eps
      (1 : Equiv.Perm (Fin n)) i = 1 := by
  unfold orientUnit
  rw [parityUnit_one]
  have hpow : indexParityUnit (n := n) eps i *
      indexParityUnit eps i = (1 : A) :=
    indexParityUnit_mul_self heps i
  have h1 : (1 : A) * indexParityUnit eps i *
      indexParityUnit eps i = 1 := by
    calc (1 : A) * indexParityUnit eps i *
        indexParityUnit eps i
        = indexParityUnit eps i *
            indexParityUnit eps i := by
          rw [one_mul]
      _ = 1 := hpow
  have hσ : (1 : Equiv.Perm (Fin n)) i = i := by
    simp
  rw [hσ] at *
  exact h1

theorem orientUnit_mul (heps : eps * eps = 1)
    (σ τ : Equiv.Perm (Fin n)) (i : Fin n) :
    orientUnit eps (σ * τ) i =
      orientUnit eps τ i * orientUnit eps σ (τ i) := by
  unfold orientUnit
  have hpar :
      parityUnit eps (σ * τ) =
        parityUnit eps σ * parityUnit eps τ :=
    parityUnit_mul heps σ τ
  have hpow : indexParityUnit eps (τ i) *
      indexParityUnit eps (τ i) = (1 : A) :=
    indexParityUnit_mul_self heps (τ i)
  have hστ : (σ * τ) i = σ (τ i) := by
    simp [Equiv.Perm.coe_mul]
  calc parityUnit eps (σ * τ) *
      indexParityUnit eps i *
      indexParityUnit eps ((σ * τ) i)
      = parityUnit eps σ * parityUnit eps τ *
          indexParityUnit eps i *
          indexParityUnit eps ((σ * τ) i) := by
        rw [hpar]
    _ = parityUnit eps τ * parityUnit eps σ *
          indexParityUnit eps i *
          indexParityUnit eps ((σ * τ) i) := by
        rw [mul_comm (parityUnit eps σ)
          (parityUnit eps τ)]
    _ = parityUnit eps τ * parityUnit eps σ *
          indexParityUnit eps i *
          (indexParityUnit eps (τ i) *
            indexParityUnit eps (τ i)) *
          indexParityUnit eps ((σ * τ) i) := by
        rw [hpow, mul_one]
    _ = parityUnit eps τ * indexParityUnit eps i *
          indexParityUnit eps (τ i) *
          (parityUnit eps σ * indexParityUnit eps (τ i) *
            indexParityUnit eps ((σ * τ) i)) := by
        ac_rfl
    _ = parityUnit eps τ * indexParityUnit eps i *
          indexParityUnit eps (τ i) *
          (parityUnit eps σ * indexParityUnit eps (τ i) *
            indexParityUnit eps (σ (τ i))) := by
        rw [hστ]

end OrientUnit

section BalancedPair

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

/-- Evaluation is additive inverses on inverses. -/
theorem _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_left
    {A : Type uA} {B : Type uB} [CommGroup A] [AddCommGroup B]
    (b : SkewBicharacter A B) (x y : A) :
    b.eval x⁻¹ y = -b.eval x y := by
  have h1 : b.eval (x * x⁻¹) y = 0 := by
    rw [mul_inv_cancel, b.eval_one_left]
  rw [b.eval_mul_left x x⁻¹ y] at h1
  have h2 : b.eval x⁻¹ y = -b.eval x y := by
    have h_eq : b.eval x y + b.eval x⁻¹ y = 0 := h1
    calc b.eval x⁻¹ y
        = b.eval x y + b.eval x⁻¹ y - b.eval x y := by abel
      _ = 0 - b.eval x y := by rw [h_eq]
      _ = -b.eval x y := by abel
  exact h2

theorem _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_right
    {A : Type uA} {B : Type uB} [CommGroup A] [AddCommGroup B]
    (b : SkewBicharacter A B) (x y : A) :
    b.eval x y⁻¹ = -b.eval x y := by
  have h1 : b.eval x (y * y⁻¹) = 0 := by
    rw [mul_inv_cancel, b.eval_one_right]
  rw [b.eval_mul_right x y y⁻¹] at h1
  have h2 : b.eval x y⁻¹ = -b.eval x y := by
    have h_eq : b.eval x y + b.eval x y⁻¹ = 0 := h1
    calc b.eval x y⁻¹
        = b.eval x y + b.eval x y⁻¹ - b.eval x y := by abel
      _ = 0 - b.eval x y := by rw [h_eq]
      _ = -b.eval x y := by abel
  exact h2

theorem skew_eval_inv_left_neg {A : Type uA} {B : Type uB} [CommGroup A] [AddCommGroup B]
    (b : SkewBicharacter A B) (x : A) :
    b.eval x⁻¹ x = -b.eval x x :=
  _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_left b x x

theorem skew_eval_inv_right_neg {A : Type uA} {B : Type uB} [CommGroup A] [AddCommGroup B]
    (b : SkewBicharacter A B) (x : A) :
    b.eval x x⁻¹ = -b.eval x x :=
  _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_right b x x

/-- Balanced two-coordinate tuple: `u` at `i`, `u⁻¹` at `j`, `1` elsewhere. -/
def balancedPairTuple {m : ℕ} (i j : Fin m) (u : A) : Fin m → A :=
  fun k => if k = i then u else if k = j then u⁻¹ else 1

@[simp]
theorem balancedPairTuple_apply_left {m : ℕ} (i j : Fin m) (u : A) :
    balancedPairTuple (A := A) i j u i = u := by
  simp [balancedPairTuple]

theorem balancedPairTuple_apply_right {m : ℕ} (i j : Fin m) (u : A)
    (h_ne : i ≠ j) :
    balancedPairTuple (A := A) i j u j = u⁻¹ := by
  unfold balancedPairTuple
  rw [ite_eq_right h_ne.symm]
  simp

theorem balancedPairTuple_apply_other {m : ℕ} (i j k : Fin m) (u : A)
    (h_ki : k ≠ i) (h_kj : k ≠ j) :
    balancedPairTuple (A := A) i j u k = 1 := by
  unfold balancedPairTuple
  rw [ite_eq_right h_ki, ite_eq_right h_kj]

theorem balancedPairTuple_eq_mul_single {m : ℕ} (i j : Fin m) (u : A)
    (h_ne : i ≠ j) :
    balancedPairTuple (A := A) i j u =
      (fun k => if k = i then u else (1 : A)) *
        (fun k => if k = j then u⁻¹ else (1 : A)) := by
  funext k
  simp only [Pi.mul_apply]
  unfold balancedPairTuple
  by_cases h_ki : k = i
  · have h_kj : k ≠ j := fun h_eq => h_ne (h_ki.symm.trans h_eq)
    simp only [ite_eq_left h_ki, ite_eq_right h_kj, mul_one]
  · by_cases h_kj : k = j
    · simp only [ite_eq_right h_ki, ite_eq_left h_kj, one_mul]
    · simp only [ite_eq_right h_ki, ite_eq_right h_kj, mul_one]

theorem tupleProd_single {m : ℕ} (k : Fin m) (a : A) :
    tupleProd (n := m) (fun q : Fin m => if q = k then a else (1 : A)) = a := by
  unfold tupleProd
  calc (Finset.univ.prod fun q : Fin m => if q = k then a else (1 : A))
      = (if k = k then a else (1 : A)) := by
        apply Finset.prod_eq_single k
        · intro b _ h_bk
          rw [ite_eq_right h_bk]
        · intro h_not
          exact absurd (Finset.mem_univ k) h_not
      _ = a := by simp

theorem tupleProd_balancedPairTuple {m : ℕ} (i j : Fin m) (u : A)
    (h_ne : i ≠ j) :
    tupleProd (n := m) (balancedPairTuple i j u) = 1 := by
  rw [balancedPairTuple_eq_mul_single i j u h_ne, tupleProd_mul]
  rw [tupleProd_single i u, tupleProd_single j u⁻¹]
  exact mul_inv_cancel u

/-- Permuting a balanced pair permutes its supporting indices. -/
theorem permute_balancedPairTuple {m : ℕ} (σ : Equiv.Perm (Fin m))
    (i j : Fin m) (u : A) :
    PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) =
      balancedPairTuple (σ i) (σ j) u := by
  funext k
  have h_iff_i : (σ.symm k = i) ↔ (k = σ i) := Equiv.symm_apply_eq σ
  have h_iff_j : (σ.symm k = j) ↔ (k = σ j) := Equiv.symm_apply_eq σ
  by_cases hk_i : k = σ i
  · have h_sym_i : σ.symm k = i := h_iff_i.mpr hk_i
    have hlhs : PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) k = u := by
      calc PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) k
          = balancedPairTuple i j u (σ.symm k) := rfl
        _ = u := by
            rw [h_sym_i]
            exact balancedPairTuple_apply_left i j u
    have hrhs : balancedPairTuple (σ i) (σ j) u k = u := by
      rw [hk_i]
      exact balancedPairTuple_apply_left (σ i) (σ j) u
    rw [hlhs, hrhs]
  · have h_sym_ne_i : σ.symm k ≠ i := fun h => hk_i (h_iff_i.mp h)
    by_cases hk_j : k = σ j
    · have h_sym_j : σ.symm k = j := h_iff_j.mpr hk_j
      have hij : i ≠ j := by
        intro h_eq
        exact hk_i (hk_j.trans (congrArg σ h_eq).symm)
      have h_ne_sigma : σ i ≠ σ j := fun h => hk_i (hk_j.trans h.symm)
      have hlhs : PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) k = u⁻¹ := by
        calc PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) k
            = balancedPairTuple i j u (σ.symm k) := rfl
          _ = balancedPairTuple i j u j := by rw [h_sym_j]
          _ = u⁻¹ := balancedPairTuple_apply_right i j u hij
      have hrhs : balancedPairTuple (σ i) (σ j) u k = u⁻¹ := by
        rw [hk_j]
        exact balancedPairTuple_apply_right (σ i) (σ j) u h_ne_sigma
      rw [hlhs, hrhs]
    · have h_sym_ne_j : σ.symm k ≠ j := fun h => hk_j (h_iff_j.mp h)
      have hlhs : PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) k = 1 := by
        calc PermutationBilinearCocycle.permute σ (balancedPairTuple i j u) k
            = balancedPairTuple i j u (σ.symm k) := rfl
          _ = 1 :=
              balancedPairTuple_apply_other i j (σ.symm k) u h_sym_ne_i h_sym_ne_j
      have hrhs : balancedPairTuple (σ i) (σ j) u k = 1 :=
        balancedPairTuple_apply_other (σ i) (σ j) k u hk_i hk_j
      rw [hlhs, hrhs]

/-- Swapping a balanced pair inverts the parameter. -/
theorem balancedPairTuple_swap {m : ℕ} (i j : Fin m) (u : A)
    (hij : i ≠ j) :
    balancedPairTuple i j u⁻¹ = balancedPairTuple j i u := by
  funext k
  by_cases hki : k = i
  · have hkj : k ≠ j := fun h => hij (hki.symm.trans h)
    have hlhs : balancedPairTuple i j u⁻¹ k = u⁻¹ := by
      rw [hki]
      exact balancedPairTuple_apply_left i j u⁻¹
    have hrhs : balancedPairTuple j i u k = u⁻¹ := by
      rw [hki]
      exact balancedPairTuple_apply_right j i u (Ne.symm hij)
    rw [hlhs, hrhs]
  · by_cases hkj : k = j
    · have hlhs : balancedPairTuple i j u⁻¹ k = u := by
        rw [hkj, balancedPairTuple_apply_right i j u⁻¹ hij, inv_inv]
      have hrhs : balancedPairTuple j i u k = u := by
        rw [hkj]
        exact balancedPairTuple_apply_left j i u
      rw [hlhs, hrhs]
    · have hlhs : balancedPairTuple i j u⁻¹ k = 1 :=
        balancedPairTuple_apply_other i j k u⁻¹ hki hkj
      have hrhs : balancedPairTuple j i u k = 1 :=
        balancedPairTuple_apply_other j i k u hkj hki
      rw [hlhs, hrhs]

/-- Permuting a balanced pair in reverse order inverts the parameter. -/
theorem permute_balancedPairTuple_of_reverse {m : ℕ}
    (σ : Equiv.Perm (Fin m)) {i j k l : Fin m}
    (hij : i ≠ j) (hli : σ l = i) (hkj : σ k = j) (u : A) :
    PermutationBilinearCocycle.permute σ (balancedPairTuple k l u) =
      balancedPairTuple i j u⁻¹ := by
  have h_perm : PermutationBilinearCocycle.permute σ (balancedPairTuple k l u) =
      balancedPairTuple (σ k) (σ l) u :=
    permute_balancedPairTuple σ k l u
  rw [h_perm, hkj, hli]
  exact (balancedPairTuple_swap i j u hij).symm

/-- Adjacency for `Fin` as `j.val = i.val + 1`. -/
def IsAdjacentPair {m : ℕ} (i j : Fin m) : Prop :=
  j.val = i.val + 1

theorem isAdjacentPair_imp_lt {m : ℕ} {i j : Fin m}
    (h : IsAdjacentPair (m := m) i j) : i < j := by
  unfold IsAdjacentPair at h
  have h_lt : i.val < j.val := by omega
  exact Fin.lt_def.mpr h_lt

theorem isAdjacentPair_imp_ne {m : ℕ} {i j : Fin m}
    (h : IsAdjacentPair (m := m) i j) : i ≠ j := by
  intro h_eq
  have h_lt := isAdjacentPair_imp_lt h
  rw [h_eq] at h_lt
  exact lt_irrefl _ h_lt

/-- Filter `≤ j` splits as `≤ i` plus singleton `j` when `j = i+1`. -/
private theorem filter_le_succ_eq {m : ℕ} {i j : Fin m}
    (h_adj : IsAdjacentPair i j) :
    Finset.univ.filter (fun q : Fin m => q ≤ j) =
      (Finset.univ.filter (fun q : Fin m => q ≤ i)) ∪ {j} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_singleton]
  constructor
  · intro h_le
    by_cases h_eq : q = j
    · right; exact h_eq
    · left
      have h_le_val : q.val ≤ j.val := (Fin.le_def.mp h_le)
      have h_j_val : j.val = i.val + 1 := h_adj
      have h_q_ne_j : q ≠ j := h_eq
      have h_lt : q.val ≤ i.val := by omega
      exact Fin.le_def.mpr h_lt
  · intro h
    cases h with
    | inl h_le_i =>
      have h_i_le_j : i ≤ j := le_of_lt (isAdjacentPair_imp_lt h_adj)
      exact le_trans h_le_i h_i_le_j
    | inr h_eq =>
      rw [h_eq]

private theorem filter_le_succ_disjoint {m : ℕ} {i j : Fin m}
    (h_adj : IsAdjacentPair i j) :
    Disjoint (Finset.univ.filter (fun q : Fin m => q ≤ i)) {j} := by
  rw [Finset.disjoint_singleton_right]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  exact isAdjacentPair_imp_lt h_adj

private theorem sum_filter_le_succ {m : ℕ} {i j : Fin m}
    (h_adj : IsAdjacentPair i j) (f : Fin m → B) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin m => q ≤ j), f q =
      (∑ q ∈ Finset.univ.filter (fun q : Fin m => q ≤ i), f q) + f j := by
  rw [filter_le_succ_eq h_adj, Finset.sum_union (filter_le_succ_disjoint h_adj),
    Finset.sum_singleton]

end BalancedPair

section SingleSupport

variable {n : ℕ} {A : Type uA} [CommGroup A]

/-- Single-support tuple: `eps` at `k`, `1` elsewhere. -/
def singleSupportTuple (k : Fin n) (eps : A) : Fin n → A :=
  fun q => if q = k then eps else (1 : A)

@[simp]
theorem singleSupportTuple_apply_self (k : Fin n) (eps : A) :
    singleSupportTuple (n := n) k eps k = eps := by
  simp [singleSupportTuple]

theorem singleSupportTuple_apply_ne {k i : Fin n} (eps : A) (h : i ≠ k) :
    singleSupportTuple (n := n) k eps i = 1 := by
  simp [singleSupportTuple, h]

theorem tupleProd_singleSupportTuple (k : Fin n) (eps : A) :
    tupleProd (n := n) (singleSupportTuple k eps) = eps := by
  unfold tupleProd singleSupportTuple
  calc (Finset.univ.prod fun q : Fin n => if q = k then eps else (1 : A))
      = (if k = k then eps else (1 : A)) := by
        apply Finset.prod_eq_single k
        · intro b _ h_bk
          rw [ite_eq_right h_bk]
        · intro h_not
          exact absurd (Finset.mem_univ k) h_not
    _ = eps := by simp

end SingleSupport

private theorem singleSupport_eq_one_of_ne {n : ℕ} {A : Type uA} [CommGroup A]
    {k : Fin n} {eps : A} {u : Fin n → A}
    (hu : ∀ q, u q = if q = k then eps else 1) {i : Fin n} (hi : i ≠ k) :
    u i = 1 := by
  have h := hu i
  rw [ite_eq_right hi] at h
  exact h

private theorem singleSupport_eq_eps {n : ℕ} {A : Type uA} [CommGroup A]
    {k : Fin n} {eps : A} {u : Fin n → A}
    (hu : ∀ q, u q = if q = k then eps else 1) :
    u k = eps := by
  have h := hu k
  rw [ite_eq_left rfl] at h
  exact h

section OrientAdd

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]
variable (b : SkewBicharacter A B) (eps : A)

/-- The additive orientation correction for the specified permutation. -/
def orientAdd (σ : Equiv.Perm (Fin n))
    (u : Fin n → A) : B :=
  ∑ i : Fin n, b.eval (orientUnit eps σ i) (u i)

theorem orientAdd_one_perm {eps : A}
    (heps : eps * eps = 1) (u : Fin n → A) :
    orientAdd (b := b) eps
      (1 : Equiv.Perm (Fin n)) u = 0 := by
  unfold orientAdd
  apply Finset.sum_eq_zero
  intro i _
  rw [orientUnit_one heps i, b.eval_one_left]

theorem orientAdd_one_tuple (σ : Equiv.Perm (Fin n)) :
    orientAdd (b := b) eps σ (1 : Fin n → A) = 0 := by
  unfold orientAdd
  apply Finset.sum_eq_zero
  intro i _
  simp [b.eval_one_right]

theorem orientAdd_mul (σ : Equiv.Perm (Fin n))
    (u v : Fin n → A) :
    orientAdd (b := b) eps σ (u * v) =
      orientAdd (b := b) eps σ u +
        orientAdd (b := b) eps σ v := by
  unfold orientAdd
  have h : ∀ i : Fin n,
      b.eval (orientUnit eps σ i) ((u * v) i) =
        b.eval (orientUnit eps σ i) (u i) +
          b.eval (orientUnit eps σ i) (v i) := by
    intro i
    have h1 : (u * v) i = u i * v i := by
      simp [Pi.mul_apply]
    rw [h1, b.eval_mul_right]
  calc ∑ i : Fin n, b.eval (orientUnit eps σ i) ((u * v) i)
      = ∑ i : Fin n,
          (b.eval (orientUnit eps σ i) (u i) +
            b.eval (orientUnit eps σ i) (v i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h i
    _ = (∑ i : Fin n, b.eval (orientUnit eps σ i) (u i)) +
          (∑ i : Fin n, b.eval (orientUnit eps σ i) (v i)) := by
        rw [Finset.sum_add_distrib]

theorem orientAdd_comp {eps : A} (heps : eps * eps = 1)
    (σ τ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    orientAdd (b := b) eps (σ * τ) u =
      orientAdd (b := b) eps τ u +
        orientAdd (b := b) eps σ (permute τ u) := by
  unfold orientAdd
  have h_orient : ∀ i : Fin n,
      orientUnit eps (σ * τ) i =
        orientUnit eps τ i * orientUnit eps σ (τ i) :=
    fun i => orientUnit_mul heps σ τ i
  have h_eval : ∀ i : Fin n,
      b.eval (orientUnit eps (σ * τ) i) (u i) =
        b.eval (orientUnit eps τ i) (u i) +
          b.eval (orientUnit eps σ (τ i)) (u i) := by
    intro i
    rw [h_orient i, b.eval_mul_left]
  calc ∑ i : Fin n, b.eval (orientUnit eps (σ * τ) i) (u i)
      = ∑ i : Fin n,
          (b.eval (orientUnit eps τ i) (u i) +
            b.eval (orientUnit eps σ (τ i)) (u i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_eval i
    _ = (∑ i : Fin n, b.eval (orientUnit eps τ i) (u i)) +
          (∑ i : Fin n, b.eval (orientUnit eps σ (τ i)) (u i)) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin n, b.eval (orientUnit eps τ i) (u i)) +
          (∑ i : Fin n,
            b.eval (orientUnit eps σ i)
              (permute τ u i)) := by
        congr 1
        let K : Fin n → B := fun j =>
          b.eval (orientUnit eps σ j) (permute τ u j)
        have hK : ∀ i : Fin n,
            K (τ i) =
              b.eval (orientUnit eps σ (τ i)) (u i) := by
          intro i
          unfold K permute
          simp
        calc ∑ i : Fin n, b.eval (orientUnit eps σ (τ i)) (u i)
            = ∑ i : Fin n, K (τ i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hK i]
          _ = ∑ i : Fin n, K i := by
              rw [← Equiv.sum_comp τ K]
          _ = ∑ i : Fin n,
                b.eval (orientUnit eps σ i)
                  (permute τ u i) := rfl

theorem orientAdd_singleSupport (σ : Equiv.Perm (Fin n)) (k : Fin n)
    {eps : A} (u : Fin n → A) (hu : ∀ q, u q = if q = k then eps else 1) :
    orientAdd (b := b) eps σ u = b.eval (orientUnit eps σ k) eps := by
  unfold orientAdd
  have h_zero : ∀ i : Fin n, i ≠ k → b.eval (orientUnit eps σ i) (u i) = 0 := by
    intro i hi
    have hu_i : u i = 1 := singleSupport_eq_one_of_ne hu hi
    rw [hu_i, b.eval_one_right]
  have hu_k : u k = eps := singleSupport_eq_eps hu
  have h_mem : k ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ k
  have h_eq : (∑ i : Fin n, b.eval (orientUnit eps σ i) (u i)) =
      b.eval (orientUnit eps σ k) (u k) := by
    apply Finset.sum_eq_single k
    · intro i _ hi
      exact h_zero i hi
    · intro hk
      exact absurd h_mem hk
  rw [h_eq, hu_k]

end OrientAdd

section TitsAlpha

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

/-- The bilinear alpha correction in the specified Tits cocycle construction. -/
def titsAlphaAdd (b : SkewBicharacter A B) (_eps : A)
    (u v : Fin n → A) : B :=
  lowerSum (ι := Fin n) b u v -
    b.eval (tupleProd (n := n) u) (tupleProd (n := n) v)

@[simp]
theorem titsAlphaAdd_one_left (b : SkewBicharacter A B)
    (eps : A) (v : Fin n → A) :
    titsAlphaAdd (n := n) b eps
      (1 : Fin n → A) v = 0 := by
  unfold titsAlphaAdd
  rw [lowerSum_one_left (ι := Fin n) b v,
    tupleProd_one (n := n) (A := A), b.eval_one_left,
    sub_self]

@[simp]
theorem titsAlphaAdd_one_right (b : SkewBicharacter A B)
    (eps : A) (u : Fin n → A) :
    titsAlphaAdd (n := n) b eps u
      (1 : Fin n → A) = 0 := by
  unfold titsAlphaAdd
  rw [lowerSum_one_right (ι := Fin n) b u,
    tupleProd_one (n := n) (A := A), b.eval_one_right,
    sub_self]

theorem titsAlphaAdd_mul_left (b : SkewBicharacter A B)
    (eps : A) (u₁ u₂ v : Fin n → A) :
    titsAlphaAdd (n := n) b eps (u₁ * u₂) v =
      titsAlphaAdd (n := n) b eps u₁ v +
        titsAlphaAdd (n := n) b eps u₂ v := by
  unfold titsAlphaAdd
  rw [lowerSum_mul_left (ι := Fin n) b u₁ u₂ v,
    tupleProd_mul (n := n) (A := A) u₁ u₂,
    b.eval_mul_left]
  abel

theorem titsAlphaAdd_mul_right (b : SkewBicharacter A B)
    (eps : A) (u v₁ v₂ : Fin n → A) :
    titsAlphaAdd (n := n) b eps u (v₁ * v₂) =
      titsAlphaAdd (n := n) b eps u v₁ +
        titsAlphaAdd (n := n) b eps u v₂ := by
  unfold titsAlphaAdd
  rw [lowerSum_mul_right (ι := Fin n) b u v₁ v₂,
    tupleProd_mul (n := n) (A := A) v₁ v₂,
    b.eval_mul_right]
  abel

theorem titsAlphaAdd_cocycle (b : SkewBicharacter A B)
    (eps : A) (u v w : Fin n → A) :
    titsAlphaAdd (n := n) b eps u v +
        titsAlphaAdd (n := n) b eps (u * v) w =
      titsAlphaAdd (n := n) b eps u (v * w) +
        titsAlphaAdd (n := n) b eps v w := by
  have h_low : lowerSum (ι := Fin n) b u v +
      lowerSum (ι := Fin n) b (u * v) w =
      lowerSum (ι := Fin n) b u (v * w) +
        lowerSum (ι := Fin n) b v w :=
    lowerAddCocycle_cocycle (ι := Fin n) b u v w
  have h_prod_uv : tupleProd (n := n) (A := A) (u * v) =
      tupleProd (n := n) u * tupleProd (n := n) v :=
    tupleProd_mul (A := A) (n := n) u v
  have h_prod_vw : tupleProd (n := n) (A := A) (v * w) =
      tupleProd (n := n) v * tupleProd (n := n) w :=
    tupleProd_mul (A := A) (n := n) v w
  have h_corr : b.eval (tupleProd (n := n) (A := A) u)
      (tupleProd (n := n) (A := A) v) +
      b.eval (tupleProd (n := n) (A := A) (u * v))
        (tupleProd (n := n) (A := A) w) =
      b.eval (tupleProd (n := n) (A := A) u)
        (tupleProd (n := n) (A := A) (v * w)) +
        b.eval (tupleProd (n := n) (A := A) v)
          (tupleProd (n := n) (A := A) w) := by
    rw [h_prod_uv, h_prod_vw, b.eval_mul_left,
      b.eval_mul_right]
    abel
  calc titsAlphaAdd (n := n) b eps u v +
      titsAlphaAdd (n := n) b eps (u * v) w
      = (lowerSum (ι := Fin n) b u v +
          lowerSum (ι := Fin n) b (u * v) w) -
          (b.eval (tupleProd (n := n) (A := A) u)
              (tupleProd (n := n) (A := A) v) +
            b.eval (tupleProd (n := n) (A := A) (u * v))
              (tupleProd (n := n) (A := A) w)) := by
        unfold titsAlphaAdd
        abel
    _ = (lowerSum (ι := Fin n) b u (v * w) +
          lowerSum (ι := Fin n) b v w) -
          (b.eval (tupleProd (n := n) (A := A) u)
              (tupleProd (n := n) (A := A) (v * w)) +
            b.eval (tupleProd (n := n) (A := A) v)
              (tupleProd (n := n) (A := A) w)) := by
        rw [h_low, h_corr]
    _ = titsAlphaAdd (n := n) b eps u (v * w) +
          titsAlphaAdd (n := n) b eps v w := by
        unfold titsAlphaAdd
        abel

end TitsAlpha

section BalancedAlpha

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

private lemma lowerSum_balanced_left_aux {b : SkewBicharacter A B}
    {i j : Fin n} {u : A} {v : Fin n → A}
    (h_adj : IsAdjacentPair i j)
    (h_ne : i ≠ j) :
    lowerSum (ι := Fin n) b (balancedPairTuple i j u) v =
      b.eval u⁻¹ (v j) := by
  let w := balancedPairTuple (A := A) i j u
  have h_w_i : w i = u := balancedPairTuple_apply_left i j u
  have h_w_j : w j = u⁻¹ := balancedPairTuple_apply_right i j u h_ne
  have h_w_other : ∀ k, k ≠ i → k ≠ j → w k = 1 := fun k hk1 hk2 =>
    balancedPairTuple_apply_other i j k u hk1 hk2
  have h_prod : tupleProd (n := n) w = 1 := tupleProd_balancedPairTuple i j u h_ne
  -- helper for inner sums
  have h_F_eq : ∀ p : Fin n, p ≠ i → p ≠ j →
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p), b.eval (w p) (v q)) = 0 := by
    intro p h_pi h_pj
    have h_wp : w p = 1 := h_w_other p h_pi h_pj
    rw [h_wp]
    apply Finset.sum_eq_zero
    intro q _
    rw [b.eval_one_left]
  have h_F_i : (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval (w i) (v q)) =
      ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval u (v q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [h_w_i]
  have h_F_j : (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ j), b.eval (w j) (v q)) =
      ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ j), b.eval u⁻¹ (v q) := by
    apply Finset.sum_congr rfl
    intro q _
    rw [h_w_j]
  -- outer sum reduces to F i + F j
  have h_outer : (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p),
      b.eval (w p) (v q)) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval u (v q)) +
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ j), b.eval u⁻¹ (v q)) := by
    have h_sum_support : ∀ p : Fin n, p ≠ i → p ≠ j →
        (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p), b.eval (w p) (v q)) = 0 :=
      h_F_eq
    have h_univ_eq : (Finset.univ : Finset (Fin n)) =
        ({i, j} : Finset (Fin n)) ∪ (Finset.univ \ {i, j}) := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ {i, j})]
    calc (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q))
        = ∑ p ∈ (Finset.univ : Finset (Fin n)),
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q)) := rfl
      _ = ∑ p ∈ ({i, j} : Finset (Fin n)) ∪ (Finset.univ \ {i, j}),
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q)) := by
          rw [← h_univ_eq]
      _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q))) +
          (∑ p ∈ Finset.univ \ {i, j},
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q))) := by
          rw [Finset.sum_union (Finset.disjoint_sdiff)]
      _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q))) + 0 := by
          congr 1
          apply Finset.sum_eq_zero
          intro p hp
          have h_mem := Finset.mem_sdiff.mp hp
          have h_pi : p ≠ i := by
            intro h_eq
            have h_in : p ∈ ({i, j} : Finset (Fin n)) := by
              rw [Finset.mem_insert, Finset.mem_singleton]
              left; exact h_eq
            exact h_mem.2 h_in
          have h_pj : p ≠ j := by
            intro h_eq
            have h_in : p ∈ ({i, j} : Finset (Fin n)) := by
              rw [Finset.mem_insert, Finset.mem_singleton]
              right; exact h_eq
            exact h_mem.2 h_in
          exact h_sum_support p h_pi h_pj
      _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q))) := by
          rw [add_zero]
      _ = (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval (w i) (v q)) +
          (∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval (w j) (v q)) := by
          rw [Finset.sum_pair h_ne]
      _ = (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval u (v q)) +
          (∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval u⁻¹ (v q)) := by
          rw [h_F_i, h_F_j]
  -- split filter ≤ j
  have h_split : (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ j), b.eval u⁻¹ (v q)) =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval u⁻¹ (v q)) +
        b.eval u⁻¹ (v j) := by
    rw [sum_filter_le_succ h_adj (fun q => b.eval u⁻¹ (v q))]
  have h_inv : ∀ q, b.eval u⁻¹ (v q) = -b.eval u (v q) := fun q =>
    _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_left b u (v q)
  have h_sum_zero : (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval u (v q)) +
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval u⁻¹ (v q)) = 0 := by
    have h_eq : (∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), b.eval u⁻¹ (v q)) =
        ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i), -b.eval u (v q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [h_inv]
    rw [h_eq, ← Finset.sum_add_distrib]
    have h_zero : ∀ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ i),
        b.eval u (v q) + -b.eval u (v q) = 0 := by
      intro q _
      abel
    rw [Finset.sum_eq_zero h_zero]
  calc lowerSum (ι := Fin n) b w v
      = (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (w p) (v q)) := rfl
    _ = (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval u (v q)) +
        (∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval u⁻¹ (v q)) := h_outer
    _ = (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval u (v q)) +
        ((∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval u⁻¹ (v q)) + b.eval u⁻¹ (v j)) := by
        rw [h_split]
    _ = ((∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval u (v q)) +
        (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval u⁻¹ (v q))) + b.eval u⁻¹ (v j) := by
        abel
    _ = 0 + b.eval u⁻¹ (v j) := by rw [h_sum_zero]
    _ = b.eval u⁻¹ (v j) := by rw [zero_add]

theorem titsAlphaAdd_balancedPair_left (b : SkewBicharacter A B) (eps : A)
    (i j : Fin n) (u : A) (v : Fin n → A)
    (h_adj : IsAdjacentPair i j) :
    titsAlphaAdd (n := n) b eps (balancedPairTuple i j u) v = b.eval u⁻¹ (v j) := by
  have h_ne : i ≠ j := isAdjacentPair_imp_ne h_adj
  have h_prod : tupleProd (n := n) (balancedPairTuple i j u) = 1 :=
    tupleProd_balancedPairTuple i j u h_ne
  unfold titsAlphaAdd
  rw [h_prod, b.eval_one_left, sub_zero]
  exact lowerSum_balanced_left_aux (b := b) h_adj h_ne

private lemma lowerSum_balanced_right_aux {b : SkewBicharacter A B}
    {i j : Fin n} {u : A} {v : Fin n → A}
    (h_adj : IsAdjacentPair i j)
    (h_ne : i ≠ j) :
    lowerSum (ι := Fin n) b v (balancedPairTuple i j u) = b.eval (v i) u := by
  let w := balancedPairTuple (A := A) i j u
  have h_w_i : w i = u := balancedPairTuple_apply_left i j u
  have h_w_j : w j = u⁻¹ := balancedPairTuple_apply_right i j u h_ne
  have h_w_other : ∀ k, k ≠ i → k ≠ j → w k = 1 := fun k hk1 hk2 =>
    balancedPairTuple_apply_other i j k u hk1 hk2
  have h_inner_eq : ∀ p : Fin n, (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q)) =
      (if i ≤ p then b.eval (v p) u else 0) + (if j ≤ p then b.eval (v p) u⁻¹ else 0) := by
    intro p
    have h_decomp : ∀ q, b.eval (v p) (w q) =
        (if q = i then b.eval (v p) u else 0) + (if q = j then b.eval (v p) u⁻¹ else 0) := by
      intro q
      by_cases h_qi : q = i
      · have h_qj : q ≠ j := fun h_eq => h_ne (h_qi.symm.trans h_eq)
        rw [ite_eq_left h_qi, ite_eq_right h_qj]
        have h_wq : w q = u := by rw [h_qi, h_w_i]
        rw [h_wq]
        simp
      · by_cases h_qj : q = j
        · rw [ite_eq_right h_qi, ite_eq_left h_qj]
          have h_wq : w q = u⁻¹ := by rw [h_qj, h_w_j]
          rw [h_wq]
          simp
        · rw [ite_eq_right h_qi, ite_eq_right h_qj]
          have h_wq : w q = 1 := h_w_other q h_qi h_qj
          rw [h_wq, b.eval_one_right]
          simp
    have h_sum_decomp : (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q)) =
        (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), (if q = i then b.eval (v p) u else 0)) +
        (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), (if q = j then b.eval (v p) u⁻¹ else 0)) := by
      calc (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q))
          = ∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
              ((if q = i then b.eval (v p) u else 0) +
                (if q = j then b.eval (v p) u⁻¹ else 0)) := by
            apply Finset.sum_congr rfl
            intro q _
            rw [h_decomp q]
        _ = _ := by rw [Finset.sum_add_distrib]
    rw [h_sum_decomp]
    have h_sum_i :
        (∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
          (if q = i then b.eval (v p) u else 0)) =
        if i ≤ p then b.eval (v p) u else 0 := by
      simp [Finset.sum_ite_eq', Finset.mem_filter]
    have h_sum_j :
        (∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
          (if q = j then b.eval (v p) u⁻¹ else 0)) =
        if j ≤ p then b.eval (v p) u⁻¹ else 0 := by
      simp [Finset.sum_ite_eq', Finset.mem_filter]
    rw [h_sum_i, h_sum_j]
  -- evaluate outer sum
  have h_lt : i < j := isAdjacentPair_imp_lt h_adj
  have h_not_j_le_i : ¬(j ≤ i) := not_le.mpr h_lt
  have h_i_le_i : i ≤ i := le_rfl
  -- helper for p relative to i,j
  have h_inner_p : ∀ p : Fin n, p ≠ i →
      (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q)) = 0 := by
    intro p h_pi
    rw [h_inner_eq p]
    by_cases h_ip : i ≤ p
    · have h_j_le_p : j ≤ p := by
        have h_i_lt_j : i < j := h_lt
        have h_p_ne_i : p ≠ i := h_pi
        -- if i ≤ p and p ≠ i then i < p, and since j = i+1, then j ≤ p
        have h_i_lt_p : i < p := lt_of_le_of_ne h_ip h_pi.symm
        have h_val : j.val = i.val + 1 := h_adj
        have h_i_val_lt_p : i.val < p.val := (Fin.lt_def.mp h_i_lt_p)
        have h_j_val_le_p : j.val ≤ p.val := by omega
        exact Fin.le_def.mpr h_j_val_le_p
      rw [ite_eq_left h_ip, ite_eq_left h_j_le_p]
      have h_inv : b.eval (v p) u⁻¹ = -b.eval (v p) u :=
        _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_right b (v p) u
      rw [h_inv]
      abel
    · have h_j_not_le : ¬(j ≤ p) := by
        intro h_jp
        exact h_ip (le_trans (le_of_lt h_lt) h_jp)
      rw [ite_eq_right h_ip, ite_eq_right h_j_not_le, add_zero]
  have h_inner_i : (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), b.eval (v i) (w q)) =
      b.eval (v i) u := by
    rw [h_inner_eq i, ite_eq_left h_i_le_i]
    have h_j_not_le_i : ¬(j ≤ i) := h_not_j_le_i
    rw [ite_eq_right h_j_not_le_i, add_zero]
  have h_outer : (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q)) =
      b.eval (v i) u := by
    calc (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q))
        = b.eval (v i) u + ∑ p ∈ Finset.univ.erase i,
            (∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q)) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          rw [h_inner_i]
        _ = b.eval (v i) u + 0 := by
          congr 1
          apply Finset.sum_eq_zero
          intro p hp
          have h_pi : p ≠ i := by
            intro h_eq
            rw [h_eq] at hp
            simp at hp
          exact h_inner_p p h_pi
        _ = b.eval (v i) u := by rw [add_zero]
  calc lowerSum (ι := Fin n) b v w
      = (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p), b.eval (v p) (w q)) := rfl
    _ = b.eval (v i) u := h_outer

theorem titsAlphaAdd_balancedPair_right (b : SkewBicharacter A B) (eps : A)
    (i j : Fin n) (u : A) (v : Fin n → A)
    (h_adj : IsAdjacentPair i j) :
    titsAlphaAdd (n := n) b eps v (balancedPairTuple i j u) = b.eval (v i) u := by
  have h_ne : i ≠ j := isAdjacentPair_imp_ne h_adj
  have h_prod : tupleProd (n := n) (balancedPairTuple i j u) = 1 :=
    tupleProd_balancedPairTuple i j u h_ne
  unfold titsAlphaAdd
  rw [h_prod, b.eval_one_right, sub_zero]
  exact lowerSum_balanced_right_aux (b := b) h_adj h_ne

end BalancedAlpha

section TitsQ

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

/-- The bilinear quadratic correction in the specified Tits cocycle construction. -/
def titsQAdd (b : SkewBicharacter A B) (eps : A)
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) : B :=
  inversionSum (ι := Fin n) b σ u +
    orientAdd (b := b) eps σ u

theorem titsQAdd_one_perm (b : SkewBicharacter A B)
    {eps : A} (heps : eps * eps = 1) (u : Fin n → A) :
    titsQAdd (n := n) b eps
      (1 : Equiv.Perm (Fin n)) u = 0 := by
  unfold titsQAdd
  rw [inversionSum_perm_one (ι := Fin n) b u,
    orientAdd_one_perm (b := b) heps u, add_zero]

theorem titsQAdd_one_tuple (b : SkewBicharacter A B)
    (eps : A) (σ : Equiv.Perm (Fin n)) :
    titsQAdd (n := n) b eps σ (1 : Fin n → A) = 0 := by
  unfold titsQAdd
  rw [inversionSum_one_tuple (ι := Fin n) b σ,
    orientAdd_one_tuple (b := b) (eps := eps) σ, add_zero]

theorem titsQAdd_comp (b : SkewBicharacter A B)
    {eps : A} (heps : eps * eps = 1)
    (σ τ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    titsQAdd (n := n) b eps (σ * τ) u =
      titsQAdd (n := n) b eps τ u +
        titsQAdd (n := n) b eps σ (permute τ u) := by
  unfold titsQAdd
  rw [inversionSum_mul (ι := Fin n) b σ τ u,
    orientAdd_comp (b := b) heps σ τ u]
  abel

theorem inversionSum_singleSupport (b : SkewBicharacter A B)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) (eps : A) (u : Fin n → A)
    (hu : ∀ q, u q = if q = k then eps else 1) :
    inversionSum (ι := Fin n) b σ u = 0 := by
  unfold inversionSum
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have h_cond : i < j ∧ σ i > σ j := (Finset.mem_filter.mp hj).2
  have hij : i ≠ j := ne_of_lt h_cond.1
  by_cases hi : i = k
  · by_cases hj_eq : j = k
    · exfalso
      exact hij (hi.trans hj_eq.symm)
    · have hu_j : u j = 1 := singleSupport_eq_one_of_ne hu hj_eq
      rw [hu_j, b.eval_one_right]
  · have hu_i : u i = 1 := singleSupport_eq_one_of_ne hu hi
    rw [hu_i, b.eval_one_left]

theorem titsQAdd_singleSupport (b : SkewBicharacter A B) (eps : A)
    (σ : Equiv.Perm (Fin n)) (k : Fin n) (u : Fin n → A)
    (hu : ∀ q, u q = if q = k then eps else 1) :
    titsQAdd (n := n) b eps σ u = b.eval (orientUnit eps σ k) eps := by
  unfold titsQAdd
  have h_inv : inversionSum (ι := Fin n) b σ u = 0 :=
    inversionSum_singleSupport b σ k eps u hu
  have h_orient : orientAdd (b := b) eps σ u =
      b.eval (orientUnit eps σ k) eps :=
    orientAdd_singleSupport (b := b) σ k u hu
  rw [h_inv, h_orient, zero_add]

end TitsQ

section BalancedQ

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

private lemma orientUnit_swap_eq {eps : A} {i j : Fin n} (h_ne : i ≠ j) :
    orientUnit (n := n) eps (Equiv.swap i j) i =
      orientUnit (n := n) eps (Equiv.swap i j) j := by
  unfold orientUnit indexParityUnit parityUnit
  have h_sign : Equiv.Perm.sign (Equiv.swap i j) = -1 := by
    rw [Equiv.Perm.sign_swap h_ne]
  have h_parity : (if Equiv.Perm.sign (Equiv.swap i j) = 1 then (1 : A) else eps) = eps := by
    rw [h_sign]
    simp
  rw [h_parity]
  have h_swap_i : (Equiv.swap i j) i = j := Equiv.swap_apply_left i j
  have h_swap_j : (Equiv.swap i j) j = i := Equiv.swap_apply_right i j
  rw [h_swap_i, h_swap_j]
  ac_rfl

private lemma orientAdd_swap_balanced_zero {b : SkewBicharacter A B} {eps : A}
    {i j : Fin n} {u : A} (h_ne : i ≠ j) :
    orientAdd (b := b) (n := n) eps (Equiv.swap i j) (balancedPairTuple i j u) = 0 := by
  let w := balancedPairTuple (A := A) i j u
  have h_w_i : w i = u := balancedPairTuple_apply_left i j u
  have h_w_j : w j = u⁻¹ := balancedPairTuple_apply_right i j u h_ne
  have h_w_other : ∀ k, k ≠ i → k ≠ j → w k = 1 := fun k hk1 hk2 =>
    balancedPairTuple_apply_other i j k u hk1 hk2
  have h_orient_eq : orientUnit (n := n) eps (Equiv.swap i j) i =
      orientUnit (n := n) eps (Equiv.swap i j) j :=
    orientUnit_swap_eq (n := n) (eps := eps) h_ne
  have h_support : ∀ p : Fin n, p ≠ i → p ≠ j →
      b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p) = 0 := by
    intro p h_pi h_pj
    have h_wp : w p = 1 := h_w_other p h_pi h_pj
    rw [h_wp, b.eval_one_right]
  have h_sum_pair : (∑ p : Fin n, b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p)) =
      b.eval (orientUnit (n := n) eps (Equiv.swap i j) i) u +
      b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u⁻¹ := by
    have h_univ_eq : (Finset.univ : Finset (Fin n)) =
        ({i, j} : Finset (Fin n)) ∪ (Finset.univ \ {i, j}) := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ {i, j})]
    calc (∑ p : Fin n, b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p))
        = ∑ p ∈ (Finset.univ : Finset (Fin n)),
            b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p) := rfl
      _ = ∑ p ∈ ({i, j} : Finset (Fin n)) ∪ (Finset.univ \ {i, j}),
            b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p) := by rw [← h_univ_eq]
      _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
            b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p)) +
          (∑ p ∈ Finset.univ \ {i, j},
            b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p)) := by
          rw [Finset.sum_union (Finset.disjoint_sdiff)]
      _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
            b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p)) + 0 := by
          congr 1
          apply Finset.sum_eq_zero
          intro p hp
          have h_mem := Finset.mem_sdiff.mp hp
          have h_pi : p ≠ i := by
            intro h_eq
            have h_in : p ∈ ({i, j} : Finset (Fin n)) := by
              rw [Finset.mem_insert, Finset.mem_singleton]
              left; exact h_eq
            exact h_mem.2 h_in
          have h_pj : p ≠ j := by
            intro h_eq
            have h_in : p ∈ ({i, j} : Finset (Fin n)) := by
              rw [Finset.mem_insert, Finset.mem_singleton]
              right; exact h_eq
            exact h_mem.2 h_in
          exact h_support p h_pi h_pj
      _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
            b.eval (orientUnit (n := n) eps (Equiv.swap i j) p) (w p)) := by
          rw [add_zero]
      _ = b.eval (orientUnit (n := n) eps (Equiv.swap i j) i) (w i) +
          b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) (w j) := by
          rw [Finset.sum_pair h_ne]
      _ = b.eval (orientUnit (n := n) eps (Equiv.swap i j) i) u +
          b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u⁻¹ := by
          rw [h_w_i, h_w_j]
  have h_orient_add : orientAdd (b := b) (n := n) eps (Equiv.swap i j) w =
      b.eval (orientUnit (n := n) eps (Equiv.swap i j) i) u +
      b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u⁻¹ := by
    unfold orientAdd
    exact h_sum_pair
  have h_inv_j : b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u⁻¹ =
      -b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u :=
    _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_right _ _ _
  calc orientAdd (b := b) (n := n) eps (Equiv.swap i j) w
      = b.eval (orientUnit (n := n) eps (Equiv.swap i j) i) u +
        b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u⁻¹ := h_orient_add
    _ = b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u +
        b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u⁻¹ := by rw [← h_orient_eq]
    _ = b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u +
        -b.eval (orientUnit (n := n) eps (Equiv.swap i j) j) u := by rw [h_inv_j]
    _ = 0 := by abel

private lemma inversionSum_swap_balanced {b : SkewBicharacter A B}
    {i j : Fin n} {u : A} (h_ne : i ≠ j) :
    inversionSum (ι := Fin n) b (Equiv.swap i j) (balancedPairTuple i j u) =
      -b.eval u u := by
  let w := balancedPairTuple (A := A) i j u
  have h_w_i : w i = u := balancedPairTuple_apply_left i j u
  have h_w_j : w j = u⁻¹ := balancedPairTuple_apply_right i j u h_ne
  have h_w_other : ∀ k, k ≠ i → k ≠ j → w k = 1 := fun k hk1 hk2 =>
    balancedPairTuple_apply_other i j k u hk1 hk2
  by_cases h_ij : i < j
  · have h_not_ji : ¬(j < i) := not_lt.mpr (le_of_lt h_ij)
    have h_swap_i : (Equiv.swap i j) i = j := Equiv.swap_apply_left i j
    have h_swap_j : (Equiv.swap i j) j = i := Equiv.swap_apply_right i j
    have h_outer : inversionSum (ι := Fin n) b (Equiv.swap i j) w =
        ∑ q ∈ Finset.univ.filter (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
          b.eval (w i) (w q) := by
      calc inversionSum (ι := Fin n) b (Equiv.swap i j) w
          = (∑ p : Fin n,
              ∑ q ∈ Finset.univ.filter
                (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
              b.eval (w p) (w q)) := rfl
        _ = (∑ q ∈ Finset.univ.filter (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
                b.eval (w i) (w q)) + ∑ p ∈ Finset.univ.erase i,
                ∑ q ∈ Finset.univ.filter (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
                  b.eval (w p) (w q) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          _ = (∑ q ∈ Finset.univ.filter (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
                b.eval (w i) (w q)) + 0 := by
              congr 1
              apply Finset.sum_eq_zero
              intro p hp
              have h_pi : p ≠ i := by
                intro h_eq
                rw [h_eq] at hp
                simp at hp
              by_cases h_pj : p = j
              · rw [h_pj]
                apply Finset.sum_eq_zero
                intro q hq
                have h_cond := (Finset.mem_filter.mp hq).2
                have h_p_lt_q : j < q := h_cond.1
                by_cases h_q_i : q = i
                · rw [h_q_i] at h_p_lt_q
                  exact absurd h_p_lt_q h_not_ji
                · by_cases h_q_j : q = j
                  · rw [h_q_j] at h_p_lt_q
                    exact absurd h_p_lt_q (lt_irrefl _)
                  · have h_wq : w q = 1 := h_w_other q h_q_i h_q_j
                    rw [h_wq, b.eval_one_right]
              · have h_wp : w p = 1 := h_w_other p h_pi h_pj
                apply Finset.sum_eq_zero
                intro q _
                rw [h_wp, b.eval_one_left]
          _ = _ := by rw [add_zero]
    have h_inner :
        (∑ q ∈ Finset.univ.filter
          (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
        b.eval (w i) (w q)) = b.eval (w i) (w j) := by
      have h_mem :
          j ∈ Finset.univ.filter
            (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q) := by
        simp [Finset.mem_filter, h_ij, h_swap_i, h_swap_j]
      have h_other :
          ∀ q ∈ Finset.univ.filter
            (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
          q ≠ j → b.eval (w i) (w q) = 0 := by
        intro q hq h_qj
        have h_cond := (Finset.mem_filter.mp hq).2
        by_cases h_q_i : q = i
        · have h_lt : i < q := h_cond.1
          rw [h_q_i] at h_lt
          exact absurd h_lt (lt_irrefl _)
        · have h_wq : w q = 1 := h_w_other q h_q_i h_qj
          rw [h_wq, b.eval_one_right]
      calc (∑ q ∈ Finset.univ.filter (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
            b.eval (w i) (w q))
          = b.eval (w i) (w j) +
              ∑ q ∈ (Finset.univ.filter
                (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q)).erase
                j,
              b.eval (w i) (w q) := by
            rw [← Finset.add_sum_erase _ _ h_mem]
        _ = b.eval (w i) (w j) + 0 := by
            congr 1
            apply Finset.sum_eq_zero
            intro q hq
            have h_mem_erase := Finset.mem_erase.mp hq
            have h_qj : q ≠ j := h_mem_erase.1
            have h_in_filter :
                q ∈ Finset.univ.filter
                  (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q) :=
              h_mem_erase.2
            exact h_other q h_in_filter h_qj
        _ = b.eval (w i) (w j) := by rw [add_zero]
    calc inversionSum (ι := Fin n) b (Equiv.swap i j) w
        = ∑ q ∈ Finset.univ.filter (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
            b.eval (w i) (w q) := h_outer
      _ = b.eval (w i) (w j) := h_inner
      _ = b.eval u u⁻¹ := by rw [h_w_i, h_w_j]
      _ = -b.eval u u :=
          _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_right b u u
  · have h_ji : j < i := by
      have h_le : j ≤ i := le_of_not_gt h_ij
      exact lt_of_le_of_ne h_le (Ne.symm h_ne)
    have h_swap_i : (Equiv.swap i j) i = j := Equiv.swap_apply_left i j
    have h_swap_j : (Equiv.swap i j) j = i := Equiv.swap_apply_right i j
    have h_outer : inversionSum (ι := Fin n) b (Equiv.swap i j) w =
        ∑ q ∈ Finset.univ.filter (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
          b.eval (w j) (w q) := by
      calc inversionSum (ι := Fin n) b (Equiv.swap i j) w
          = (∑ p : Fin n,
              ∑ q ∈ Finset.univ.filter
                (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
              b.eval (w p) (w q)) := rfl
        _ = (∑ q ∈ Finset.univ.filter (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
                b.eval (w j) (w q)) + ∑ p ∈ Finset.univ.erase j,
                ∑ q ∈ Finset.univ.filter (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
                  b.eval (w p) (w q) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          _ = (∑ q ∈ Finset.univ.filter (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
                b.eval (w j) (w q)) + 0 := by
              congr 1
              apply Finset.sum_eq_zero
              intro p hp
              have h_pj : p ≠ j := by
                intro h_eq
                rw [h_eq] at hp
                simp at hp
              by_cases h_pi : p = i
              · rw [h_pi]
                apply Finset.sum_eq_zero
                intro q hq
                have h_cond := (Finset.mem_filter.mp hq).2
                have h_p_lt_q : i < q := h_cond.1
                have h_swap_gt : (Equiv.swap i j) i > (Equiv.swap i j) q := h_cond.2
                rw [h_swap_i] at h_swap_gt
                by_cases h_q_i : q = i
                · rw [h_q_i] at h_p_lt_q
                  exact absurd h_p_lt_q (lt_irrefl _)
                · by_cases h_q_j : q = j
                  · rw [h_q_j] at h_swap_gt
                    rw [h_swap_j] at h_swap_gt
                    exact absurd h_swap_gt (not_lt.mpr (le_of_lt h_ji))
                  · have h_wq : w q = 1 := h_w_other q h_q_i h_q_j
                    rw [h_wq, b.eval_one_right]
              · have h_wp : w p = 1 := h_w_other p h_pi h_pj
                apply Finset.sum_eq_zero
                intro q _
                rw [h_wp, b.eval_one_left]
          _ = _ := by rw [add_zero]
    have h_inner :
        (∑ q ∈ Finset.univ.filter
          (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
        b.eval (w j) (w q)) = b.eval (w j) (w i) := by
      have h_mem :
          i ∈ Finset.univ.filter
            (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q) := by
        simp [Finset.mem_filter, h_ji, h_swap_i, h_swap_j]
      have h_other :
          ∀ q ∈ Finset.univ.filter
            (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
          q ≠ i → b.eval (w j) (w q) = 0 := by
        intro q hq h_qi
        have h_cond := (Finset.mem_filter.mp hq).2
        by_cases h_q_j : q = j
        · have h_lt : j < q := h_cond.1
          rw [h_q_j] at h_lt
          exact absurd h_lt (lt_irrefl _)
        · have h_wq : w q = 1 := h_w_other q h_qi h_q_j
          rw [h_wq, b.eval_one_right]
      calc (∑ q ∈ Finset.univ.filter (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
            b.eval (w j) (w q))
          = b.eval (w j) (w i) +
              ∑ q ∈ (Finset.univ.filter
                (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q)).erase
                i,
              b.eval (w j) (w q) := by
            rw [← Finset.add_sum_erase _ _ h_mem]
        _ = b.eval (w j) (w i) + 0 := by
            congr 1
            apply Finset.sum_eq_zero
            intro q hq
            have h_mem_erase := Finset.mem_erase.mp hq
            have h_qi : q ≠ i := h_mem_erase.1
            have h_in_filter :
                q ∈ Finset.univ.filter
                  (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q) :=
              h_mem_erase.2
            exact h_other q h_in_filter h_qi
        _ = b.eval (w j) (w i) := by rw [add_zero]
    calc inversionSum (ι := Fin n) b (Equiv.swap i j) w
        = ∑ q ∈ Finset.univ.filter (fun q => j < q ∧ (Equiv.swap i j) j > (Equiv.swap i j) q),
            b.eval (w j) (w q) := h_outer
      _ = b.eval (w j) (w i) := h_inner
      _ = b.eval u⁻¹ u := by rw [h_w_j, h_w_i]
      _ = -b.eval u u :=
          _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_left b u u

theorem titsQAdd_swap_balancedPair (b : SkewBicharacter A B) (eps : A)
    (i j : Fin n) (u : A) (h_ne : i ≠ j) :
    titsQAdd (n := n) b eps (Equiv.swap i j) (balancedPairTuple i j u) = -b.eval u u := by
  unfold titsQAdd
  rw [inversionSum_swap_balanced h_ne, orientAdd_swap_balanced_zero h_ne, add_zero]

end BalancedQ

section BalancedQZero

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

theorem titsQAdd_balancedPair_eq_zero_of_orientUnit_eq
    {b : SkewBicharacter A B} {eps : A} {σ : Equiv.Perm (Fin n)}
    {i j : Fin n} {u : A}
    (h_ne : i ≠ j) (h_lt : i < j) (h_sigma_lt : σ i < σ j)
    (h_orient : orientUnit (n := n) eps σ i = orientUnit (n := n) eps σ j) :
    titsQAdd (n := n) b eps σ (balancedPairTuple i j u) = 0 := by
  let w := balancedPairTuple (A := A) i j u
  have h_w_i : w i = u := balancedPairTuple_apply_left i j u
  have h_w_j : w j = u⁻¹ := balancedPairTuple_apply_right i j u h_ne
  have h_w_other : ∀ k, k ≠ i → k ≠ j → w k = 1 := fun k hk1 hk2 =>
    balancedPairTuple_apply_other i j k u hk1 hk2
  have h_inv : inversionSum (ι := Fin n) b σ w = 0 := by
    unfold inversionSum
    apply Finset.sum_eq_zero
    intro p _
    apply Finset.sum_eq_zero
    intro q hq
    have h_cond := (Finset.mem_filter.mp hq).2
    have h_p_lt_q : p < q := h_cond.1
    have h_sigma_gt : σ p > σ q := h_cond.2
    by_cases h_p_i : p = i
    · by_cases h_q_j : q = j
      · have h_not_gt : ¬(σ i > σ j) := not_lt.mpr (le_of_lt h_sigma_lt)
        exact absurd (by rw [h_p_i, h_q_j] at h_sigma_gt; exact h_sigma_gt) h_not_gt
      · by_cases h_q_i : q = i
        · have h_lt : p < q := h_p_lt_q
          rw [h_p_i, h_q_i] at h_lt
          exact absurd h_lt (lt_irrefl _)
        · have h_wq : w q = 1 := h_w_other q h_q_i h_q_j
          rw [h_wq, b.eval_one_right]
    · by_cases h_p_j : p = j
      · have h_j_lt_q : j < q := by rw [h_p_j] at h_p_lt_q; exact h_p_lt_q
        by_cases h_q_i : q = i
        · rw [h_q_i] at h_j_lt_q
          have h_not_ji : ¬(j < i) := not_lt.mpr (le_of_lt h_lt)
          exact absurd h_j_lt_q h_not_ji
        · by_cases h_q_j : q = j
          · rw [h_q_j] at h_j_lt_q
            exact absurd h_j_lt_q (lt_irrefl _)
          · have h_wq : w q = 1 := h_w_other q h_q_i h_q_j
            rw [h_wq, b.eval_one_right]
      · have h_wp : w p = 1 := h_w_other p h_p_i h_p_j
        rw [h_wp, b.eval_one_left]
  have h_orient_zero : orientAdd (b := b) (n := n) eps σ w = 0 := by
    have h_support : ∀ p : Fin n, p ≠ i → p ≠ j →
        b.eval (orientUnit (n := n) eps σ p) (w p) = 0 := by
      intro p h_pi h_pj
      have h_wp : w p = 1 := h_w_other p h_pi h_pj
      rw [h_wp, b.eval_one_right]
    have h_sum_pair : (∑ p : Fin n, b.eval (orientUnit (n := n) eps σ p) (w p)) =
        b.eval (orientUnit (n := n) eps σ i) u +
        b.eval (orientUnit (n := n) eps σ j) u⁻¹ := by
      have h_univ_eq : (Finset.univ : Finset (Fin n)) =
          ({i, j} : Finset (Fin n)) ∪ (Finset.univ \ {i, j}) := by
        rw [Finset.union_sdiff_of_subset (Finset.subset_univ {i, j})]
      calc (∑ p : Fin n, b.eval (orientUnit (n := n) eps σ p) (w p))
          = ∑ p ∈ (Finset.univ : Finset (Fin n)), b.eval (orientUnit (n := n) eps σ p) (w p) := rfl
        _ = ∑ p ∈ ({i, j} : Finset (Fin n)) ∪ (Finset.univ \ {i, j}),
              b.eval (orientUnit (n := n) eps σ p) (w p) := by rw [← h_univ_eq]
        _ = (∑ p ∈ ({i, j} : Finset (Fin n)), b.eval (orientUnit (n := n) eps σ p) (w p)) +
            (∑ p ∈ Finset.univ \ {i, j}, b.eval (orientUnit (n := n) eps σ p) (w p)) := by
            rw [Finset.sum_union (Finset.disjoint_sdiff)]
        _ = (∑ p ∈ ({i, j} : Finset (Fin n)), b.eval (orientUnit (n := n) eps σ p) (w p)) + 0 := by
            congr 1
            apply Finset.sum_eq_zero
            intro p hp
            have h_mem := Finset.mem_sdiff.mp hp
            have h_pi : p ≠ i := by
              intro h_eq
              have h_in : p ∈ ({i, j} : Finset (Fin n)) := by
                rw [Finset.mem_insert, Finset.mem_singleton]
                left; exact h_eq
              exact h_mem.2 h_in
            have h_pj : p ≠ j := by
              intro h_eq
              have h_in : p ∈ ({i, j} : Finset (Fin n)) := by
                rw [Finset.mem_insert, Finset.mem_singleton]
                right; exact h_eq
              exact h_mem.2 h_in
            exact h_support p h_pi h_pj
        _ = (∑ p ∈ ({i, j} : Finset (Fin n)),
              b.eval (orientUnit (n := n) eps σ p) (w p)) := by
          rw [add_zero]
        _ = b.eval (orientUnit (n := n) eps σ i) (w i) +
            b.eval (orientUnit (n := n) eps σ j) (w j) := by
            rw [Finset.sum_pair h_ne]
        _ = b.eval (orientUnit (n := n) eps σ i) u +
            b.eval (orientUnit (n := n) eps σ j) u⁻¹ := by
            rw [h_w_i, h_w_j]
    have h_orient_add : orientAdd (b := b) (n := n) eps σ w =
        b.eval (orientUnit (n := n) eps σ i) u +
        b.eval (orientUnit (n := n) eps σ j) u⁻¹ := by
      unfold orientAdd
      exact h_sum_pair
    have h_inv2 : b.eval (orientUnit (n := n) eps σ j) u⁻¹ =
        -b.eval (orientUnit (n := n) eps σ j) u :=
      _root_.PermutationBilinearCocycle.SkewBicharacter.eval_inv_right _ _ _
    calc orientAdd (b := b) (n := n) eps σ w
        = b.eval (orientUnit (n := n) eps σ i) u +
            b.eval (orientUnit (n := n) eps σ j) u⁻¹ := h_orient_add
      _ = b.eval (orientUnit (n := n) eps σ j) u +
            b.eval (orientUnit (n := n) eps σ j) u⁻¹ := by
        rw [h_orient]
      _ = b.eval (orientUnit (n := n) eps σ j) u +
            -b.eval (orientUnit (n := n) eps σ j) u := by
        rw [h_inv2]
      _ = 0 := by abel
  unfold titsQAdd
  rw [h_inv, h_orient_zero, add_zero]

private lemma orientUnit_adjacent_eq {eps : A} {σ : Equiv.Perm (Fin n)}
    {i j : Fin n} (heps : eps * eps = 1)
    (h_adj : IsAdjacentPair i j) (h_adj_sigma : IsAdjacentPair (σ i) (σ j)) :
    orientUnit (n := n) eps σ i = orientUnit (n := n) eps σ j := by
  unfold orientUnit indexParityUnit
  have h_pow_i : eps ^ j.val = eps ^ i.val * eps := by
    have h_j_val : j.val = i.val + 1 := h_adj
    rw [h_j_val, pow_succ]
  have h_pow_sigma : eps ^ (σ j).val = eps ^ (σ i).val * eps := by
    have h_sj_val : (σ j).val = (σ i).val + 1 := h_adj_sigma
    rw [h_sj_val, pow_succ]
  calc parityUnit eps σ * eps ^ i.val * eps ^ (σ i).val
      = parityUnit eps σ * eps ^ i.val * eps ^ (σ i).val * 1 := by rw [mul_one]
    _ = parityUnit eps σ * eps ^ i.val * eps ^ (σ i).val * (eps * eps) := by rw [heps]
    _ = parityUnit eps σ * (eps ^ i.val * eps) * (eps ^ (σ i).val * eps) := by ac_rfl
    _ = parityUnit eps σ * eps ^ j.val * eps ^ (σ j).val := by rw [← h_pow_i, ← h_pow_sigma]

theorem titsQAdd_balancedPair_adjacent
    {b : SkewBicharacter A B} {eps : A} {σ : Equiv.Perm (Fin n)}
    {i j : Fin n} {u : A}
    (heps : eps * eps = 1)
    (h_adj : IsAdjacentPair i j)
    (h_adj_sigma : IsAdjacentPair (σ i) (σ j)) :
    titsQAdd (n := n) b eps σ (balancedPairTuple i j u) = 0 := by
  have h_ne : i ≠ j := isAdjacentPair_imp_ne h_adj
  have h_lt : i < j := isAdjacentPair_imp_lt h_adj
  have h_sigma_lt : σ i < σ j := isAdjacentPair_imp_lt h_adj_sigma
  have h_orient : orientUnit (n := n) eps σ i = orientUnit (n := n) eps σ j :=
    orientUnit_adjacent_eq (n := n) (eps := eps) heps h_adj h_adj_sigma
  exact titsQAdd_balancedPair_eq_zero_of_orientUnit_eq (b := b) (eps := eps)
    (σ := σ) h_ne h_lt h_sigma_lt h_orient

end BalancedQZero

section AdjacentSwapBridge

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

/-- `b.eval` on a `tupleProd` expands to the sum of evaluations. -/
private lemma b_eval_tupleProd_left (b : SkewBicharacter A B)
    (u : Fin n → A) (y : A) :
    b.eval (tupleProd (n := n) u) y = ∑ i : Fin n, b.eval (u i) y := by
  have h_prod : tupleProd (n := n) u = (Finset.univ.prod fun i : Fin n => u i) := rfl
  rw [h_prod]
  have h_forall : ∀ s : Finset (Fin n),
      b.eval (s.prod fun i => u i) y = ∑ i ∈ s, b.eval (u i) y := by
    intro s
    induction s using Finset.induction with
    | empty => simp [b.eval_one_left]
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, b.eval_mul_left, ih]
  exact h_forall Finset.univ

private lemma b_eval_tupleProd_right (b : SkewBicharacter A B)
    (y : A) (u : Fin n → A) :
    b.eval y (tupleProd (n := n) u) = ∑ i : Fin n, b.eval y (u i) := by
  have h_prod : tupleProd (n := n) u = (Finset.univ.prod fun i : Fin n => u i) := rfl
  rw [h_prod]
  have h_forall : ∀ s : Finset (Fin n),
      b.eval y (s.prod fun i => u i) = ∑ i ∈ s, b.eval y (u i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [b.eval_one_right]
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, b.eval_mul_right, ih]
  exact h_forall Finset.univ

private lemma filter_le_eq_lt_union_single (p : Fin n) :
    Finset.univ.filter (fun q : Fin n => q ≤ p) =
      (Finset.univ.filter (fun q : Fin n => q < p)) ∪ {p} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h_eq : q = p
    · right; exact h_eq
    · left
      exact lt_of_le_of_ne h h_eq
  · intro h
    cases h with
    | inl h_lt => exact le_of_lt h_lt
    | inr h_eq => rw [h_eq]

private lemma filter_lt_disjoint_single (p : Fin n) :
    Disjoint (Finset.univ.filter (fun q : Fin n => q < p)) {p} := by
  rw [Finset.disjoint_singleton_right]
  simp

private lemma sum_filter_le_eq (p : Fin n) (f : Fin n → B) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ p), f q =
      (∑ q ∈ Finset.univ.filter (fun q : Fin n => q < p), f q) + f p := by
  rw [filter_le_eq_lt_union_single p,
    Finset.sum_union (filter_lt_disjoint_single p), Finset.sum_singleton]

private lemma sum_univ_eq_sum_ge_add_sum_lt (p : Fin n) (f : Fin n → B) :
    (∑ k : Fin n, f k) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => p ≤ k), f k) +
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < p), f k) := by
  have h_disj : Disjoint
      (Finset.univ.filter (fun k : Fin n => p ≤ k))
      (Finset.univ.filter (fun k : Fin n => k < p)) := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    exact absurd h1 (not_le.mpr h2)
  have h_union : Finset.univ.filter (fun k : Fin n => p ≤ k) ∪
      Finset.univ.filter (fun k : Fin n => k < p) = Finset.univ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      by_cases h : p ≤ k
      · left; exact h
      · right; exact lt_of_not_ge h
  calc (∑ k : Fin n, f k) = ∑ k ∈ Finset.univ, f k := rfl
    _ = ∑ k ∈ Finset.univ.filter (fun k => p ≤ k) ∪
        Finset.univ.filter (fun k => k < p), f k := by rw [h_union]
    _ = (∑ k ∈ Finset.univ.filter (fun k => p ≤ k), f k) +
        (∑ k ∈ Finset.univ.filter (fun k => k < p), f k) := by
        rw [Finset.sum_union h_disj]

private lemma sum_univ_eq_sum_le_add_sum_gt (p : Fin n) (f : Fin n → B) :
    (∑ k : Fin n, f k) =
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ p), f k) +
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => p < k), f k) := by
  have h_disj : Disjoint
      (Finset.univ.filter (fun k : Fin n => k ≤ p))
      (Finset.univ.filter (fun k : Fin n => p < k)) := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    exact absurd h1 (not_le.mpr h2)
  have h_union : Finset.univ.filter (fun k : Fin n => k ≤ p) ∪
      Finset.univ.filter (fun k : Fin n => p < k) = Finset.univ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      by_cases h : k ≤ p
      · left; exact h
      · right; exact lt_of_not_ge h
  calc (∑ k : Fin n, f k) = ∑ k ∈ Finset.univ, f k := rfl
    _ = ∑ k ∈ Finset.univ.filter (fun k => k ≤ p) ∪
        Finset.univ.filter (fun k => p < k), f k := by rw [h_union]
    _ = (∑ k ∈ Finset.univ.filter (fun k => k ≤ p), f k) +
        (∑ k ∈ Finset.univ.filter (fun k => p < k), f k) := by
        rw [Finset.sum_union h_disj]

/-- `lowerSum` with single-support on the right collapses to a filtered sum. -/
private lemma lowerSum_u_singleSupport (b : SkewBicharacter A B)
    (u : Fin n → A) (k : Fin n) (eps : A) :
    lowerSum (ι := Fin n) b u (singleSupportTuple (n := n) k eps) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n => k ≤ p), b.eval (u p) eps := by
  unfold lowerSum
  have h_inner : ∀ p : Fin n,
      (∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
          b.eval (u p) (singleSupportTuple (n := n) k eps q)) =
        if k ≤ p then b.eval (u p) eps else 0 := by
    intro p
    have h_eq : ∀ q, b.eval (u p) (singleSupportTuple (n := n) k eps q) =
        if q = k then b.eval (u p) eps else 0 := by
      intro q
      unfold singleSupportTuple
      by_cases h : q = k
      · simp [h]
      · simp [h, b.eval_one_right]
    calc (∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
          b.eval (u p) (singleSupportTuple (n := n) k eps q))
        = ∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
            (if q = k then b.eval (u p) eps else 0) := by
          apply Finset.sum_congr rfl
          intro q _; rw [h_eq q]
      _ = if k ∈ Finset.univ.filter (fun q => q ≤ p) then b.eval (u p) eps else 0 := by
          simp [Finset.sum_ite_eq', Finset.mem_filter]
      _ = if k ≤ p then b.eval (u p) eps else 0 := by
          simp [Finset.mem_filter]
  calc (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
        b.eval (u p) (singleSupportTuple (n := n) k eps q))
      = ∑ p : Fin n, if k ≤ p then b.eval (u p) eps else 0 := by
        apply Finset.sum_congr rfl; intro p _; rw [h_inner p]
    _ = ∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps := by
        rw [← Finset.sum_filter]

private lemma lowerSum_single_perm (b : SkewBicharacter A B)
    (k : Fin n) (eps : A) (u : Fin n → A) (σ : Equiv.Perm (Fin n)) :
    lowerSum (ι := Fin n) b (singleSupportTuple (n := n) k eps) (permute σ u) =
      ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ k),
        b.eval eps ((permute σ u) q) := by
  unfold lowerSum
  have h_outer : ∀ p : Fin n, p ≠ k →
      (∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
          b.eval (singleSupportTuple (n := n) k eps p) ((permute σ u) q)) = 0 := by
    intro p hp
    have h_val : singleSupportTuple (n := n) k eps p = 1 := by
      simp [singleSupportTuple, hp]
    rw [h_val]
    apply Finset.sum_eq_zero
    intro q _; rw [b.eval_one_left]
  have h_k : (∑ q ∈ Finset.univ.filter (fun q => q ≤ k),
      b.eval (singleSupportTuple (n := n) k eps k) ((permute σ u) q)) =
      ∑ q ∈ Finset.univ.filter (fun q => q ≤ k), b.eval eps ((permute σ u) q) := by
    apply Finset.sum_congr rfl; intro q _
    have h_val : singleSupportTuple (n := n) k eps k = eps := by simp [singleSupportTuple]
    rw [h_val]
  calc (∑ p : Fin n, ∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
        b.eval (singleSupportTuple (n := n) k eps p) ((permute σ u) q))
      = (∑ q ∈ Finset.univ.filter (fun q => q ≤ k), b.eval eps ((permute σ u) q)) +
        ∑ p ∈ Finset.univ.erase k,
          ∑ q ∈ Finset.univ.filter (fun q => q ≤ p),
            b.eval (singleSupportTuple (n := n) k eps p) ((permute σ u) q) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
        rw [h_k]
    _ = (∑ q ∈ Finset.univ.filter (fun q => q ≤ k), b.eval eps ((permute σ u) q)) + 0 := by
        congr 1
        apply Finset.sum_eq_zero
        intro p hp
        have h_ne : p ≠ k := by
          intro h_eq; rw [h_eq] at hp; simp at hp
        exact h_outer p h_ne
    _ = _ := by rw [add_zero]

/-- `titsAlphaAdd` with single-support on the right is a prefix sum. -/
theorem titsAlphaAdd_single_right_prefix (b : SkewBicharacter A B)
    (eps : A) (u : Fin n → A) (k : Fin n) :
    titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) k eps) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n => p < k), b.eval eps (u p) := by
  unfold titsAlphaAdd
  rw [lowerSum_u_singleSupport b u k eps, tupleProd_singleSupportTuple k eps,
    b_eval_tupleProd_left b u eps]
  have h_all := sum_univ_eq_sum_ge_add_sum_lt k (fun p => b.eval (u p) eps)
  have h_ge_sub : (∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps) -
      (∑ p : Fin n, b.eval (u p) eps) =
        -(∑ p ∈ Finset.univ.filter (fun p => p < k), b.eval (u p) eps) := by
    have h_eq : (∑ p : Fin n, b.eval (u p) eps) =
        (∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps) +
        (∑ p ∈ Finset.univ.filter (fun p => p < k), b.eval (u p) eps) := h_all
    calc (∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps) -
        (∑ p : Fin n, b.eval (u p) eps)
        = (∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps) -
          ((∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps) +
            (∑ p ∈ Finset.univ.filter (fun p => p < k), b.eval (u p) eps)) := by rw [h_eq]
      _ = -(∑ p ∈ Finset.univ.filter (fun p => p < k), b.eval (u p) eps) := by abel
  calc (∑ p ∈ Finset.univ.filter (fun p => k ≤ p), b.eval (u p) eps) -
        (∑ p : Fin n, b.eval (u p) eps)
      = -(∑ p ∈ Finset.univ.filter (fun p => p < k), b.eval (u p) eps) := h_ge_sub
    _ = ∑ p ∈ Finset.univ.filter (fun p => p < k), -b.eval (u p) eps := by
        rw [Finset.sum_neg_distrib]
    _ = ∑ p ∈ Finset.univ.filter (fun p => p < k), b.eval eps (u p) := by
        apply Finset.sum_congr rfl
        intro p _
        have h : -b.eval (u p) eps = b.eval eps (u p) := (b.skew eps (u p)).symm
        exact h

/-- Moving the right single-support index across an adjacent pair adds the intervening term. -/
theorem titsAlphaAdd_single_right_adjacent (b : SkewBicharacter A B)
    (eps : A) (u : Fin n → A) {i j : Fin n} (h_adj : IsAdjacentPair i j) :
    titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) j eps) =
      titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) +
        b.eval eps (u i) := by
  rw [titsAlphaAdd_single_right_prefix (b := b) (eps := eps) (u := u) (k := j),
    titsAlphaAdd_single_right_prefix (b := b) (eps := eps) (u := u) (k := i)]
  have h_lt_eq : Finset.univ.filter (fun p : Fin n => p < j) =
      Finset.univ.filter (fun p : Fin n => p ≤ i) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hq
      have h_lt : q < j := hq
      have h_q_lt_j : q.val < j.val := Fin.lt_def.mp h_lt
      have h_j_val : j.val = i.val + 1 := h_adj
      have h_q_le_i : q.val ≤ i.val := by omega
      exact Fin.le_def.mpr h_q_le_i
    · intro hq
      have h_le : q ≤ i := hq
      have h_q_le_i : q.val ≤ i.val := Fin.le_def.mp h_le
      have h_j_val : j.val = i.val + 1 := h_adj
      have h_q_lt_j : q.val < j.val := by omega
      exact Fin.lt_def.mpr h_q_lt_j
  have h_le_eq : Finset.univ.filter (fun p : Fin n => p ≤ i) =
      (Finset.univ.filter (fun p : Fin n => p < i)) ∪ {i} :=
    filter_le_eq_lt_union_single i
  have h_filter : Finset.univ.filter (fun p : Fin n => p < j) =
      (Finset.univ.filter (fun p : Fin n => p < i)) ∪ {i} := by
    rw [h_lt_eq, h_le_eq]
  have h_disj : Disjoint (Finset.univ.filter (fun p : Fin n => p < i)) {i} :=
    filter_lt_disjoint_single i
  calc ∑ p ∈ Finset.univ.filter (fun p => p < j), b.eval eps (u p)
      = ∑ p ∈ (Finset.univ.filter (fun p => p < i) ∪ {i}), b.eval eps (u p) := by
        rw [h_filter]
    _ = (∑ p ∈ Finset.univ.filter (fun p => p < i), b.eval eps (u p)) +
        (∑ p ∈ ({i} : Finset (Fin n)), b.eval eps (u p)) := by
        rw [Finset.sum_union h_disj]
    _ = (∑ p ∈ Finset.univ.filter (fun p => p < i), b.eval eps (u p)) + b.eval eps (u i) := by
        rw [Finset.sum_singleton]

/-- `titsAlphaAdd` of two single-support tuples with `j > i` vanishes in the `j,i` order. -/
theorem titsAlphaAdd_single_single_zero (b : SkewBicharacter A B) (eps : A)
    {i j : Fin n} (h : i < j) :
    titsAlphaAdd (n := n) b eps (singleSupportTuple (n := n) j eps)
      (singleSupportTuple (n := n) i eps) = 0 := by
  rw [titsAlphaAdd_single_right_prefix (b := b) (eps := eps)]
  apply Finset.sum_eq_zero
  intro p hp
  have hp_lt : p < i := (Finset.mem_filter.mp hp).2
  have hp_lt_j : p < j := lt_trans hp_lt h
  have hp_ne_j : p ≠ j := ne_of_lt hp_lt_j
  have h_val : singleSupportTuple (n := n) j eps p = 1 :=
    singleSupportTuple_apply_ne (n := n) eps hp_ne_j
  rw [h_val, b.eval_one_right]

/-- Swapping `i` and `j` in the left tuple does not change the prefix sum against
    `singleSupportTuple i`. -/
theorem titsAlphaAdd_single_right_swap (b : SkewBicharacter A B) (eps : A)
    (u : Fin n → A) {i j : Fin n} (h : i < j) :
    titsAlphaAdd (n := n) b eps (permute (Equiv.swap i j) u)
        (singleSupportTuple (n := n) i eps) =
      titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) := by
  rw [titsAlphaAdd_single_right_prefix (b := b) (eps := eps) (u := permute (Equiv.swap i j) u),
    titsAlphaAdd_single_right_prefix (b := b) (eps := eps) (u := u)]
  apply Finset.sum_congr rfl
  intro p hp
  have hp_lt : p < i := (Finset.mem_filter.mp hp).2
  have h_p_ne_i : p ≠ i := ne_of_lt hp_lt
  have h_p_lt_j : p < j := lt_trans hp_lt h
  have h_p_ne_j : p ≠ j := ne_of_lt h_p_lt_j
  have h_swap : (Equiv.swap i j) p = p :=
    Equiv.swap_apply_of_ne_of_ne h_p_ne_i h_p_ne_j
  have h_perm : (permute (Equiv.swap i j) u) p = u ((Equiv.swap i j) p) := by
    simp only [permute]
    have h_inv : (Equiv.swap i j)⁻¹ p = (Equiv.swap i j) p := by
      simp
    rw [h_inv]
  rw [h_perm, h_swap]

/-- Under `eps * eps = 1` the two equal prefix sums are 2-torsion, so their sum vanishes. -/
theorem titsAlphaAdd_single_right_swap_add_eq_zero (b : SkewBicharacter A B)
    {eps : A} (heps : eps * eps = 1) (u : Fin n → A) {i j : Fin n} (h : i < j) :
    titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) +
      titsAlphaAdd (n := n) b eps (permute (Equiv.swap i j) u)
        (singleSupportTuple (n := n) i eps) = 0 := by
  have h_eq : titsAlphaAdd (n := n) b eps (permute (Equiv.swap i j) u)
      (singleSupportTuple (n := n) i eps) =
      titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) :=
    titsAlphaAdd_single_right_swap (b := b) (eps := eps) (u := u) h
  have h_prefix : titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n => p < i), b.eval eps (u p) :=
    titsAlphaAdd_single_right_prefix (b := b) (eps := eps) (u := u) (k := i)
  calc titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) +
      titsAlphaAdd (n := n) b eps (permute (Equiv.swap i j) u)
        (singleSupportTuple (n := n) i eps)
      = titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) +
        titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) := by
          rw [h_eq]
    _ = (∑ p ∈ Finset.univ.filter (fun p : Fin n => p < i), b.eval eps (u p)) +
        (∑ p ∈ Finset.univ.filter (fun p : Fin n => p < i), b.eval eps (u p)) := by
          rw [h_prefix]
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin n => p < i),
        (b.eval eps (u p) + b.eval eps (u p)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin n => p < i), (0 : B) := by
          apply Finset.sum_congr rfl
          intro p _
          have h_two : b.eval eps (u p) + b.eval eps (u p) = 0 := by
            have h_mul : b.eval (eps * eps) (u p) = b.eval eps (u p) + b.eval eps (u p) :=
              b.eval_mul_left eps eps (u p)
            have h_one : b.eval (1 : A) (u p) = 0 := b.eval_one_left (u p)
            rw [heps] at h_mul
            rw [h_one] at h_mul
            exact h_mul.symm
          exact h_two
    _ = 0 := by simp

private lemma filter_le_swap_invariant {i j : Fin n}
    (h_adj : IsAdjacentPair i j) (q : Fin n) :
    q ≤ j ↔ (Equiv.swap i j) q ≤ j := by
  by_cases h_qi : q = i
  · rw [h_qi, Equiv.swap_apply_left i j]
    have h_le : i ≤ j := le_of_lt (isAdjacentPair_imp_lt h_adj)
    exact ⟨fun _ => le_rfl, fun _ => h_le⟩
  · by_cases h_qj : q = j
    · rw [h_qj, Equiv.swap_apply_right i j]
      have h_le : i ≤ j := le_of_lt (isAdjacentPair_imp_lt h_adj)
      exact ⟨fun _ => h_le, fun _ => le_rfl⟩
    · have h_swap : (Equiv.swap i j) q = q := Equiv.swap_apply_of_ne_of_ne h_qi h_qj
      rw [h_swap]

private lemma sum_swap_filter_le_j (f : Fin n → B) {i j : Fin n}
    (h_adj : IsAdjacentPair i j) :
    ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ j), f ((Equiv.swap i j) q) =
      ∑ q ∈ Finset.univ.filter (fun q : Fin n => q ≤ j), f q := by
  -- use explicit decomposition via succ filter to avoid map-bij complexity
  have h_sj_eq : Finset.univ.filter (fun q : Fin n => q ≤ j) =
      (Finset.univ.filter (fun q : Fin n => q ≤ i)) ∪ {j} :=
    filter_le_succ_eq h_adj
  have h_si_eq : Finset.univ.filter (fun q : Fin n => q ≤ i) =
      (Finset.univ.filter (fun q : Fin n => q < i)) ∪ {i} :=
    filter_le_eq_lt_union_single i
  have h_disj_sj : Disjoint (Finset.univ.filter (fun q : Fin n => q ≤ i)) {j} :=
    filter_le_succ_disjoint h_adj
  have h_disj_si : Disjoint (Finset.univ.filter (fun q : Fin n => q < i)) {i} :=
    filter_lt_disjoint_single i
  have h_swap_lt : ∀ q ∈ Finset.univ.filter (fun q : Fin n => q < i),
      (Equiv.swap i j) q = q := by
    intro q hq
    have h_lt : q < i := (Finset.mem_filter.mp hq).2
    have h_qi : q ≠ i := ne_of_lt h_lt
    have h_qj : q ≠ j := by
      intro h_eq; rw [h_eq] at h_lt
      exact absurd h_lt (not_lt.mpr (le_of_lt (isAdjacentPair_imp_lt h_adj)))
    exact Equiv.swap_apply_of_ne_of_ne h_qi h_qj
  calc ∑ q ∈ Finset.univ.filter (fun q => q ≤ j), f ((Equiv.swap i j) q)
      = (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), f ((Equiv.swap i j) q)) +
        f ((Equiv.swap i j) j) := by
        rw [h_sj_eq, Finset.sum_union h_disj_sj, Finset.sum_singleton]
    _ = ((∑ q ∈ Finset.univ.filter (fun q => q < i), f ((Equiv.swap i j) q)) +
        f ((Equiv.swap i j) i)) + f ((Equiv.swap i j) j) := by
        rw [h_si_eq, Finset.sum_union h_disj_si, Finset.sum_singleton]
    _ = ((∑ q ∈ Finset.univ.filter (fun q => q < i), f q) + f j) + f i := by
        have h1 : (∑ q ∈ Finset.univ.filter (fun q => q < i), f ((Equiv.swap i j) q)) =
            ∑ q ∈ Finset.univ.filter (fun q => q < i), f q := by
          apply Finset.sum_congr rfl; intro q hq; rw [h_swap_lt q hq]
        rw [h1, Equiv.swap_apply_left, Equiv.swap_apply_right]
    _ = (∑ q ∈ Finset.univ.filter (fun q => q < i), f q) + f i + f j := by abel
    _ = (∑ q ∈ Finset.univ.filter (fun q => q ≤ i), f q) + f j := by
        rw [h_si_eq, Finset.sum_union h_disj_si, Finset.sum_singleton]
    _ = ∑ q ∈ Finset.univ.filter (fun q => q ≤ j), f q := by
        rw [h_sj_eq, Finset.sum_union h_disj_sj, Finset.sum_singleton]

theorem titsAlphaAdd_single_perm_suffix (b : SkewBicharacter A B)
    (eps : A) (u : Fin n → A) {i j : Fin n} (h_adj : IsAdjacentPair i j) :
    titsAlphaAdd (n := n) b eps (singleSupportTuple (n := n) j eps)
      (permute (Equiv.swap i j) u) =
      -(∑ p ∈ Finset.univ.filter (fun p : Fin n => j < p), b.eval eps (u p)) := by
  unfold titsAlphaAdd
  rw [lowerSum_single_perm b j eps u (Equiv.swap i j),
    tupleProd_singleSupportTuple j eps]
  have h_lower : (∑ q ∈ Finset.univ.filter (fun q => q ≤ j),
      b.eval eps ((permute (Equiv.swap i j) u) q)) =
      ∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps (u q) := by
    have h_swap_eq := sum_swap_filter_le_j (fun q => b.eval eps (u q)) h_adj
    have h_perm : ∀ q, (permute (Equiv.swap i j) u) q = u ((Equiv.swap i j) q) := by
      intro q
      simp only [permute]
      have h_inv : (Equiv.swap i j)⁻¹ q = (Equiv.swap i j) q := by
        simp
      rw [h_inv]
    calc (∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps ((permute (Equiv.swap i j) u) q))
        = ∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps (u ((Equiv.swap i j) q)) := by
          apply Finset.sum_congr rfl; intro q _; rw [h_perm q]
      _ = ∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps (u q) := h_swap_eq
  have h_prod_perm : tupleProd (n := n) (permute (Equiv.swap i j) u) = tupleProd (n := n) u :=
    tupleProd_permute (Equiv.swap i j) u
  rw [h_lower, h_prod_perm, b_eval_tupleProd_right b eps u]
  have h_all := sum_univ_eq_sum_le_add_sum_gt j (fun p => b.eval eps (u p))
  calc (∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps (u q)) -
        (∑ p : Fin n, b.eval eps (u p))
      = (∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps (u q)) -
        ((∑ q ∈ Finset.univ.filter (fun q => q ≤ j), b.eval eps (u q)) +
          (∑ p ∈ Finset.univ.filter (fun p => j < p), b.eval eps (u p))) := by rw [h_all]
    _ = -(∑ p ∈ Finset.univ.filter (fun p => j < p), b.eval eps (u p)) := by abel

private lemma inversionSum_swap_adjacent (b : SkewBicharacter A B)
    {i j : Fin n} (h_adj : IsAdjacentPair i j) (u : Fin n → A) :
    inversionSum (ι := Fin n) b (Equiv.swap i j) u = b.eval (u i) (u j) := by
  have h_lt : i < j := isAdjacentPair_imp_lt h_adj
  have h_ne : i ≠ j := isAdjacentPair_imp_ne h_adj
  have h_swap_i : (Equiv.swap i j) i = j := Equiv.swap_apply_left i j
  have h_swap_j : (Equiv.swap i j) j = i := Equiv.swap_apply_right i j
  have h_swap_other : ∀ k, k ≠ i → k ≠ j → (Equiv.swap i j) k = k :=
    fun k hk1 hk2 => Equiv.swap_apply_of_ne_of_ne hk1 hk2
  have h_j_val : j.val = i.val + 1 := h_adj
  have h_filter_i :
      Finset.univ.filter
          (fun q : Fin n => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q) =
        {j} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ⟨h1, h2⟩
      rw [h_swap_i] at h2
      by_cases h_qi : q = i
      · rw [h_qi] at h1
        exact absurd h1 (lt_irrefl _)
      · by_cases h_qj : q = j
        · exact h_qj
        · have h_swap_q : (Equiv.swap i j) q = q := h_swap_other q h_qi h_qj
          rw [h_swap_q] at h2
          have h_i_lt_q : i.val < q.val := Fin.lt_def.mp h1
          have h_q_lt_j : q.val < j.val := Fin.lt_def.mp h2
          have : False := by omega
          exact False.elim this
    · intro h_eq
      rw [h_eq]
      simp [h_swap_i, h_swap_j, h_lt]
  have h_filter_other : ∀ p : Fin n, p ≠ i →
      Finset.univ.filter (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q) = ∅ := by
    intro p hp
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have h1_val : p.val < q.val := Fin.lt_def.mp h1
      have h2_val : (Equiv.swap i j q).val < (Equiv.swap i j p).val := Fin.lt_def.mp h2
      by_cases h_pi : p = j
      · -- p = j, swap p = i
        rw [h_pi, h_swap_j] at h2
        have h_j_lt_q : j < q := by rw [h_pi] at h1; exact h1
        by_cases h_qi : q = i
        · rw [h_qi] at h_j_lt_q
          exact absurd h_j_lt_q (not_lt.mpr (le_of_lt h_lt))
        · by_cases h_qj : q = j
          · rw [h_qj] at h_j_lt_q
            exact absurd h_j_lt_q (lt_irrefl _)
          · have h_swap_q : (Equiv.swap i j) q = q := h_swap_other q h_qi h_qj
            rw [h_swap_q] at h2
            -- h2 : i > q  => q < i
            have h_q_lt_i : q < i := h2
            have h_q_lt_i_val : q.val < i.val := Fin.lt_def.mp h_q_lt_i
            have h_j_lt_q_val : j.val < q.val := Fin.lt_def.mp h_j_lt_q
            omega
      · -- p ≠ i, p ≠ j, swap p = p
        have h_p_ne_j : p ≠ j := h_pi
        have h_swap_p : (Equiv.swap i j) p = p := h_swap_other p hp h_p_ne_j
        rw [h_swap_p] at h2
        by_cases h_qi : q = i
        · rw [h_qi, h_swap_i] at h2
          -- h1 : p < i, h2 : p > j  => j < p < i impossible since i < j
          have h_p_lt_i : p < i := by rw [h_qi] at h1; exact h1
          have h_j_lt_p : j < p := h2
          have h_p_lt_i_val : p.val < i.val := Fin.lt_def.mp h_p_lt_i
          have h_j_lt_p_val : j.val < p.val := Fin.lt_def.mp h_j_lt_p
          omega
        · by_cases h_qj : q = j
          · rw [h_qj, h_swap_j] at h2
            -- h1 : p < j, h2 : i < p  => i < p < j impossible
            have h_p_lt_j : p < j := by rw [h_qj] at h1; exact h1
            have h_i_lt_p : i < p := h2
            have h_p_lt_j_val : p.val < j.val := Fin.lt_def.mp h_p_lt_j
            have h_i_lt_p_val : i.val < p.val := Fin.lt_def.mp h_i_lt_p
            omega
          · have h_swap_q : (Equiv.swap i j) q = q := h_swap_other q h_qi h_qj
            rw [h_swap_q] at h2
            -- h1 : p < q, h2 : q < p  contradiction
            exact absurd h2 (not_lt.mpr (le_of_lt h1))
    · intro h
      simp at h
  calc inversionSum (ι := Fin n) b (Equiv.swap i j) u
      = ∑ p : Fin n,
          ∑ q ∈ Finset.univ.filter
            (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
          b.eval (u p) (u q) := rfl
    _ = (∑ q ∈ Finset.univ.filter
          (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
          b.eval (u i) (u q)) +
        ∑ p ∈ Finset.univ.erase i,
          ∑ q ∈ Finset.univ.filter (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
            b.eval (u p) (u q) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    _ = b.eval (u i) (u j) + 0 := by
        have h_inner_i :
            (∑ q ∈ Finset.univ.filter
              (fun q => i < q ∧ (Equiv.swap i j) i > (Equiv.swap i j) q),
              b.eval (u i) (u q)) =
            b.eval (u i) (u j) := by
          rw [h_filter_i, Finset.sum_singleton]
        have h_rest : (∑ p ∈ Finset.univ.erase i,
            ∑ q ∈ Finset.univ.filter (fun q => p < q ∧ (Equiv.swap i j) p > (Equiv.swap i j) q),
              b.eval (u p) (u q)) = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          have h_ne : p ≠ i := by intro h_eq; rw [h_eq] at hp; simp at hp
          rw [h_filter_other p h_ne]
          simp
        rw [h_inner_i, h_rest, add_zero]
    _ = b.eval (u i) (u j) := by rw [add_zero] -- already

private lemma orientUnit_swap_adjacent (eps : A) (heps : eps * eps = 1)
    {i j : Fin n} (h_adj : IsAdjacentPair i j) :
    orientUnit (n := n) eps (Equiv.swap i j) i = 1 ∧
    orientUnit (n := n) eps (Equiv.swap i j) j = 1 ∧
    (∀ k : Fin n, k ≠ i → k ≠ j → orientUnit (n := n) eps (Equiv.swap i j) k = eps) := by
  have h_parity : parityUnit (n := n) eps (Equiv.swap i j) = eps := by
    have h_sign : Equiv.Perm.sign (Equiv.swap i j) = -1 := by
      rw [Equiv.Perm.sign_swap (isAdjacentPair_imp_ne h_adj)]
    unfold parityUnit
    rw [h_sign]
    simp
  have h_pow_i : eps ^ j.val = eps ^ i.val * eps := by
    have h_j_val : j.val = i.val + 1 := h_adj
    rw [h_j_val, pow_succ]
  have h_pow_sigma : ∀ k, k ≠ i → k ≠ j → (Equiv.swap i j) k = k := fun k hk1 hk2 =>
    Equiv.swap_apply_of_ne_of_ne hk1 hk2
  constructor
  · unfold orientUnit indexParityUnit
    rw [h_parity, Equiv.swap_apply_left i j]
    have h1 : eps ^ i.val * eps ^ i.val = 1 := by
      simpa [indexParityUnit] using indexParityUnit_mul_self (n := n) (eps := eps) heps i
    calc eps * eps ^ i.val * eps ^ j.val
        = eps * eps ^ i.val * (eps ^ i.val * eps) := by rw [h_pow_i]
      _ = eps * (eps ^ i.val * eps ^ i.val) * eps := by ac_rfl
      _ = eps * 1 * eps := by rw [h1]
      _ = 1 := by rw [mul_one, heps]
  constructor
  · unfold orientUnit indexParityUnit
    rw [h_parity, Equiv.swap_apply_right i j]
    calc eps * eps ^ j.val * eps ^ i.val
        = eps * (eps ^ i.val * eps) * eps ^ i.val := by rw [h_pow_i]
      _ = eps * (eps ^ i.val * eps ^ i.val) * eps := by ac_rfl
      _ = eps * 1 * eps := by
          have h1 : eps ^ i.val * eps ^ i.val = 1 := by
            simpa [indexParityUnit] using indexParityUnit_mul_self (n := n) (eps := eps) heps i
          rw [h1]
      _ = 1 := by rw [mul_one, heps]
  · intro k hk1 hk2
    unfold orientUnit indexParityUnit
    rw [h_parity, h_pow_sigma k hk1 hk2]
    have h_pow : eps ^ k.val * eps ^ k.val = 1 := by
      simpa [indexParityUnit] using indexParityUnit_mul_self (n := n) (eps := eps) heps k
    calc eps * eps ^ k.val * eps ^ k.val
        = eps * (eps ^ k.val * eps ^ k.val) := by ac_rfl
      _ = eps * 1 := by rw [h_pow]
      _ = eps := by rw [mul_one]

private lemma orientAdd_swap_adjacent (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) {i j : Fin n} (h_adj : IsAdjacentPair i j)
    (u : Fin n → A) :
    orientAdd (b := b) (n := n) eps (Equiv.swap i j) u =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≠ i ∧ k ≠ j), b.eval eps (u k) := by
  unfold orientAdd
  have h_orient := orientUnit_swap_adjacent eps heps h_adj
  have h1 : orientUnit (n := n) eps (Equiv.swap i j) i = 1 := h_orient.1
  have h2 : orientUnit (n := n) eps (Equiv.swap i j) j = 1 := h_orient.2.1
  have h3 := h_orient.2.2
  have h_eq : ∀ k : Fin n, b.eval (orientUnit (n := n) eps (Equiv.swap i j) k) (u k) =
      if k = i ∨ k = j then 0 else b.eval eps (u k) := by
    intro k
    by_cases h_ki : k = i
    · have h_orient_k : orientUnit (n := n) eps (Equiv.swap i j) k = 1 := by rw [h_ki, h1]
      rw [h_orient_k, b.eval_one_left]
      simp [h_ki]
    · by_cases h_kj : k = j
      · have h_orient_k : orientUnit (n := n) eps (Equiv.swap i j) k = 1 := by rw [h_kj, h2]
        rw [h_orient_k, b.eval_one_left]
        simp [h_kj]
      · have h_orient_k : orientUnit (n := n) eps (Equiv.swap i j) k = eps := h3 k h_ki h_kj
        rw [h_orient_k]
        simp [h_ki, h_kj]
  calc (∑ k : Fin n, b.eval (orientUnit (n := n) eps (Equiv.swap i j) k) (u k))
      = ∑ k : Fin n, if k = i ∨ k = j then (0 : B) else b.eval eps (u k) := by
        apply Finset.sum_congr rfl; intro k _; rw [h_eq k]
    _ = ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), b.eval eps (u k) := by
        have h_if : ∀ k, (if k = i ∨ k = j then (0 : B) else b.eval eps (u k)) =
            (if k ≠ i ∧ k ≠ j then b.eval eps (u k) else 0) := by
          intro k
          by_cases h_ki : k = i
          · simp [h_ki]
          · by_cases h_kj : k = j
            · simp [h_kj]
            · simp [h_ki, h_kj]
        calc (∑ k : Fin n, if k = i ∨ k = j then (0 : B) else b.eval eps (u k))
            = ∑ k : Fin n, if k ≠ i ∧ k ≠ j then b.eval eps (u k) else 0 := by
              apply Finset.sum_congr rfl; intro k _; rw [h_if k]
          _ = ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), b.eval eps (u k) := by
              rw [← Finset.sum_filter]

private lemma orientAdd_swap_eq_prefix_suffix (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) {i j : Fin n} (h_adj : IsAdjacentPair i j)
    (u : Fin n → A) :
    orientAdd (b := b) (n := n) eps (Equiv.swap i j) u =
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < i), b.eval eps (u k)) +
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => j < k), b.eval eps (u k)) := by
  rw [orientAdd_swap_adjacent b eps heps h_adj u]
  have h_filter : Finset.univ.filter (fun k : Fin n => k ≠ i ∧ k ≠ j) =
      (Finset.univ.filter (fun k : Fin n => k < i)) ∪
        (Finset.univ.filter (fun k : Fin n => j < k)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      have h_ne : k ≠ i ∧ k ≠ j := h
      by_cases h_lt_i : k < i
      · left; exact h_lt_i
      · right
        have h_not_lt : ¬(k < i) := h_lt_i
        have h_le : i ≤ k := le_of_not_gt h_not_lt
        have h_ne_j : k ≠ j := h_ne.2
        have h_lt : i < j := isAdjacentPair_imp_lt h_adj
        have h_vals : k.val ≠ i.val ∧ k.val ≠ j.val :=
          ⟨fun h_eq => h_ne.1 (Fin.ext h_eq),
            fun h_eq => h_ne.2 (Fin.ext h_eq)⟩
        have h_j_val : j.val = i.val + 1 := h_adj
        have h_k_ge_i : i.val ≤ k.val := (Fin.le_def.mp h_le)
        have h_k_ne_i : k.val ≠ i.val := h_vals.1
        have h_k_gt_i : i.val < k.val := lt_of_le_of_ne h_k_ge_i (Ne.symm h_vals.1)
        have h_k_ne_j : k.val ≠ j.val := h_vals.2
        have h_k_gt_j : j.val < k.val ∨ j.val ≤ k.val := by omega
        -- Since k ≠ i,j and i < j = i+1, any k with i ≤ k and k ≠ i,j must satisfy j < k
        have h_j_lt_k : j < k := by
          have h_k_gt : i.val < k.val := h_k_gt_i
          omega
        exact h_j_lt_k
    · intro h
      cases h with
      | inl h_lt =>
        constructor
        · intro h_eq; rw [h_eq] at h_lt; exact lt_irrefl _ h_lt
        · intro h_eq; rw [h_eq] at h_lt
          have h_lt_j : i < j := isAdjacentPair_imp_lt h_adj
          exact absurd (lt_trans h_lt h_lt_j) (lt_irrefl _)
      | inr h_gt =>
        constructor
        · intro h_eq
          rw [h_eq] at h_gt
          exact absurd h_gt (not_lt.mpr (le_of_lt (isAdjacentPair_imp_lt h_adj)))
        · intro h_eq; rw [h_eq] at h_gt; exact lt_irrefl _ h_gt
  have h_disj : Disjoint
      (Finset.univ.filter (fun k : Fin n => k < i))
      (Finset.univ.filter (fun k : Fin n => j < k)) := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    have h_lt_j : i < j := isAdjacentPair_imp_lt h_adj
    exact absurd (lt_trans h1 h_lt_j) (not_lt.mpr (le_of_lt h2))
  rw [h_filter, Finset.sum_union h_disj]

theorem titsQAdd_adjacent_swap_bridge (b : SkewBicharacter A B) (eps : A)
    (heps : eps * eps = 1) {i j : Fin n} (h_adj : IsAdjacentPair i j)
    (u : Fin n → A) :
    titsQAdd (n := n) b eps (Equiv.swap i j) u =
      titsAlphaAdd (n := n) b eps u (singleSupportTuple (n := n) i eps) -
        titsAlphaAdd (n := n) b eps (singleSupportTuple (n := n) j eps)
          (permute (Equiv.swap i j) u) +
        b.eval (u i) (u j) := by
  have h_inv := inversionSum_swap_adjacent (b := b) h_adj u
  have h_orient := orientAdd_swap_eq_prefix_suffix (b := b) eps heps h_adj u
  have h_alpha1 := titsAlphaAdd_single_right_prefix (b := b) eps u i
  have h_alpha2 := titsAlphaAdd_single_perm_suffix (b := b) eps u h_adj
  have h_titsQ : titsQAdd (n := n) b eps (Equiv.swap i j) u =
      b.eval (u i) (u j) +
        ((∑ k ∈ Finset.univ.filter (fun k => k < i), b.eval eps (u k)) +
          (∑ k ∈ Finset.univ.filter (fun k => j < k), b.eval eps (u k))) := by
    unfold titsQAdd
    rw [h_inv, h_orient]
  calc titsQAdd (n := n) b eps (Equiv.swap i j) u
      = b.eval (u i) (u j) +
        ((∑ k ∈ Finset.univ.filter (fun k => k < i), b.eval eps (u k)) +
          (∑ k ∈ Finset.univ.filter (fun k => j < k), b.eval eps (u k))) := h_titsQ
    _ = (∑ k ∈ Finset.univ.filter (fun k => k < i), b.eval eps (u k)) -
        (-(∑ k ∈ Finset.univ.filter (fun k => j < k), b.eval eps (u k))) +
        b.eval (u i) (u j) := by abel
    _ = titsAlphaAdd (n := n) b eps u (singleSupportTuple i eps) -
        titsAlphaAdd (n := n) b eps (singleSupportTuple j eps) (permute (Equiv.swap i j) u) +
        b.eval (u i) (u j) := by rw [← h_alpha1, ← h_alpha2]

end AdjacentSwapBridge

section Transport

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

theorem tits_transport (b : SkewBicharacter A B)
    {eps : A} (heps : eps * eps = 1)
    (σ : Equiv.Perm (Fin n)) (u v : Fin n → A) :
    titsAlphaAdd (n := n) b eps u v +
        titsQAdd (n := n) b eps σ (u * v) =
      titsQAdd (n := n) b eps σ u +
        titsQAdd (n := n) b eps σ v +
        titsAlphaAdd (n := n) b eps
          (permute σ u) (permute σ v) := by
  have _heps : eps * eps = 1 := heps
  have h_lower := lowerSum_inversion_transport
    (ι := Fin n) (b := b) σ u v
  have h_orient_mul := orientAdd_mul
    (b := b) (eps := eps) σ u v
  have h_prod_perm_u : tupleProd (A := A) (n := n)
      (permute σ u) = tupleProd (n := n) u :=
    tupleProd_permute σ u
  have h_prod_perm_v : tupleProd (A := A) (n := n)
      (permute σ v) = tupleProd (n := n) v :=
    tupleProd_permute σ v
  calc titsAlphaAdd (n := n) b eps u v +
      titsQAdd (n := n) b eps σ (u * v)
      = (lowerSum (ι := Fin n) b u v -
          b.eval (tupleProd (n := n) u)
            (tupleProd (n := n) v) +
          (inversionSum (ι := Fin n) b σ (u * v) +
            orientAdd (b := b) eps σ (u * v))) := rfl
    _ = (lowerSum (ι := Fin n) b u v +
          inversionSum (ι := Fin n) b σ (u * v)) +
          orientAdd (b := b) eps σ (u * v) -
          b.eval (tupleProd (n := n) u)
            (tupleProd (n := n) v) := by
        abel
    _ = (inversionSum (ι := Fin n) b σ u +
          inversionSum (ι := Fin n) b σ v +
          lowerSum (ι := Fin n) b (permute σ u)
            (permute σ v)) +
          orientAdd (b := b) eps σ (u * v) -
          b.eval (tupleProd (n := n) u)
            (tupleProd (n := n) v) := by
        rw [h_lower]
    _ = (inversionSum (ι := Fin n) b σ u +
          inversionSum (ι := Fin n) b σ v +
          orientAdd (b := b) eps σ (u * v)) +
          (lowerSum (ι := Fin n) b (permute σ u)
              (permute σ v) -
            b.eval (tupleProd (n := n)
                (permute σ u))
              (tupleProd (n := n)
                (permute σ v))) := by
        rw [h_prod_perm_u, h_prod_perm_v]
        abel
    _ = (inversionSum (ι := Fin n) b σ u +
          inversionSum (ι := Fin n) b σ v +
          (orientAdd (b := b) eps σ u +
            orientAdd (b := b) eps σ v)) +
          (lowerSum (ι := Fin n) b (permute σ u)
              (permute σ v) -
            b.eval (tupleProd (n := n)
                (permute σ u))
              (tupleProd (n := n)
                (permute σ v))) := by
        rw [h_orient_mul]
    _ = titsQAdd (n := n) b eps σ u +
          titsQAdd (n := n) b eps σ v +
          titsAlphaAdd (n := n) b eps
            (permute σ u) (permute σ v) := by
        unfold titsQAdd titsAlphaAdd
        abel

end Transport

section CocyclePackage

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]

/-- The additive Tits cocycle computed from the original bicharacter and coefficient. -/
def titsAddCocycle (b : SkewBicharacter A B)
    (_eps : A) (u v : Fin n → A) : B :=
  titsAlphaAdd (n := n) b _eps u v

theorem titsAddCocycle_one_left (b : SkewBicharacter A B)
    (eps : A) (v : Fin n → A) :
    titsAddCocycle (n := n) b eps
      (1 : Fin n → A) v = 0 :=
  titsAlphaAdd_one_left (n := n) b eps v

theorem titsAddCocycle_one_right (b : SkewBicharacter A B)
    (eps : A) (u : Fin n → A) :
    titsAddCocycle (n := n) b eps u
      (1 : Fin n → A) = 0 :=
  titsAlphaAdd_one_right (n := n) b eps u

theorem titsAddCocycle_mul_left (b : SkewBicharacter A B)
    (eps : A) (u₁ u₂ v : Fin n → A) :
    titsAddCocycle (n := n) b eps (u₁ * u₂) v =
      titsAddCocycle (n := n) b eps u₁ v +
        titsAddCocycle (n := n) b eps u₂ v :=
  titsAlphaAdd_mul_left (n := n) b eps u₁ u₂ v

theorem titsAddCocycle_mul_right (b : SkewBicharacter A B)
    (eps : A) (u v₁ v₂ : Fin n → A) :
    titsAddCocycle (n := n) b eps u (v₁ * v₂) =
      titsAddCocycle (n := n) b eps u v₁ +
        titsAddCocycle (n := n) b eps u v₂ :=
  titsAlphaAdd_mul_right (n := n) b eps u v₁ v₂

theorem titsAddCocycle_cocycle (b : SkewBicharacter A B)
    (eps : A) (u v w : Fin n → A) :
    titsAddCocycle (n := n) b eps u v +
        titsAddCocycle (n := n) b eps (u * v) w =
      titsAddCocycle (n := n) b eps u (v * w) +
        titsAddCocycle (n := n) b eps v w :=
  titsAlphaAdd_cocycle (n := n) b eps u v w

/-- The Tits correction with its additive value under the multiplicative tag. -/
def titsCocycleAll (b : SkewBicharacter A B)
    (eps : A) (u v : Fin n → A) :
    Multiplicative B :=
  Multiplicative.ofAdd
    (titsAlphaAdd (n := n) b eps u v)

theorem titsCocycleAll_one_left (b : SkewBicharacter A B)
    (eps : A) (v : Fin n → A) :
    titsCocycleAll (n := n) b eps
      (1 : Fin n → A) v = 1 := by
  unfold titsCocycleAll
  rw [titsAlphaAdd_one_left (n := n) b eps v]
  rfl

theorem titsCocycleAll_one_right (b : SkewBicharacter A B)
    (eps : A) (u : Fin n → A) :
    titsCocycleAll (n := n) b eps u
      (1 : Fin n → A) = 1 := by
  unfold titsCocycleAll
  rw [titsAlphaAdd_one_right (n := n) b eps u]
  rfl

theorem titsCocycleAll_cocycle (b : SkewBicharacter A B)
    (eps : A) (u v w : Fin n → A) :
    titsCocycleAll (n := n) b eps u v *
        titsCocycleAll (n := n) b eps (u * v) w =
      titsCocycleAll (n := n) b eps u (v * w) *
        titsCocycleAll (n := n) b eps v w := by
  unfold titsCocycleAll
  have h := titsAlphaAdd_cocycle (n := n) b eps u v w
  have h1 : Multiplicative.ofAdd (titsAlphaAdd (n := n) b eps u v) *
      Multiplicative.ofAdd
        (titsAlphaAdd (n := n) b eps (u * v) w) =
      Multiplicative.ofAdd
        (titsAlphaAdd (n := n) b eps u v +
          titsAlphaAdd (n := n) b eps (u * v) w) := by
    rw [← ofAdd_add]
  have h2 : Multiplicative.ofAdd
      (titsAlphaAdd (n := n) b eps u (v * w) +
        titsAlphaAdd (n := n) b eps v w) =
      Multiplicative.ofAdd
        (titsAlphaAdd (n := n) b eps u (v * w)) *
      Multiplicative.ofAdd (titsAlphaAdd (n := n) b eps v w) := by
    rw [ofAdd_add]
  calc Multiplicative.ofAdd (titsAlphaAdd (n := n) b eps u v) *
      Multiplicative.ofAdd (titsAlphaAdd (n := n) b eps (u * v) w)
      = Multiplicative.ofAdd
          (titsAlphaAdd (n := n) b eps u v +
            titsAlphaAdd (n := n) b eps (u * v) w) := h1
    _ = Multiplicative.ofAdd
          (titsAlphaAdd (n := n) b eps u (v * w) +
            titsAlphaAdd (n := n) b eps v w) := by
        rw [h]
    _ = Multiplicative.ofAdd
          (titsAlphaAdd (n := n) b eps u (v * w)) *
        Multiplicative.ofAdd (titsAlphaAdd (n := n) b eps v w) := h2

/-- The normalized cocycle associated with the computed Tits correction. -/
def titsNormalizedCocycle (b : SkewBicharacter A B)
    (eps : A) :
    NormalizedCocycleExtension.NormalizedCocycle
      (Fin n → A) (Multiplicative B) where
  cocycle := titsCocycleAll (n := n) b eps
  one_left := titsCocycleAll_one_left (n := n) b eps
  one_right := titsCocycleAll_one_right (n := n) b eps
  cocycle_assoc := titsCocycleAll_cocycle (n := n) b eps

/-- The coefficient extension associated with the normalized Tits cocycle. -/
abbrev TitsExtension (b : SkewBicharacter A B)
    (eps : A) :=
  NormalizedCocycleExtension.Extension
    (titsNormalizedCocycle (n := n) b eps)

@[ext]
theorem TitsExtension.ext {b : SkewBicharacter A B}
    {eps : A} {x y : TitsExtension (n := n) b eps}
    (h1 : x.base = y.base) (h2 : x.coeff = y.coeff) :
    x = y :=
  NormalizedCocycleExtension.Extension.ext h1 h2

@[simp]
theorem TitsExtension.mul_base {b : SkewBicharacter A B}
    {eps : A} (x y : TitsExtension (n := n) b eps) :
    (x * y).base = x.base * y.base :=
  rfl

@[simp]
theorem TitsExtension.mul_coeff {b : SkewBicharacter A B}
    {eps : A} (x y : TitsExtension (n := n) b eps) :
    (x * y).coeff =
      x.coeff * y.coeff *
        titsCocycleAll (n := n) b eps x.base y.base :=
  rfl

@[simp]
theorem TitsExtension.one_base {b : SkewBicharacter A B}
    {eps : A} :
    (1 : TitsExtension (n := n) b eps).base =
      (1 : Fin n → A) :=
  rfl

@[simp]
theorem TitsExtension.one_coeff {b : SkewBicharacter A B}
    {eps : A} :
    (1 : TitsExtension (n := n) b eps).coeff =
      (1 : Multiplicative B) :=
  rfl

/-- The actual central group extension associated with the Tits cocycle. -/
def titsGroupExtension (b : SkewBicharacter A B)
    (eps : A) :
    GroupExtension (Multiplicative B)
      (TitsExtension (n := n) b eps) (Fin n → A) :=
  NormalizedCocycleExtension.extension
    (titsNormalizedCocycle (n := n) b eps)

end CocyclePackage

section TitsAction

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]
variable (b : SkewBicharacter A B)
  (eps : A) (heps : eps * eps = 1)

/-- The compatible map of Tits extensions associated with the given permutation. -/
def titsCompatibleMap (σ : Equiv.Perm (Fin n)) :
    NormalizedCocycleExtension.CompatibleMap
      (titsNormalizedCocycle (n := n) b eps)
      (titsNormalizedCocycle (n := n) b eps) where
  f := permuteHom (A := A) σ
  g := MonoidHom.id (Multiplicative B)
  q := fun u =>
    Multiplicative.ofAdd (titsQAdd (n := n) b eps σ u)
  q_one := by
    have h : titsQAdd (n := n) b eps σ
        (1 : Fin n → A) = 0 :=
      titsQAdd_one_tuple (n := n) b eps σ
    simp [h]
  compat := by
    intro x y
    simp only [MonoidHom.id_apply]
    have h_add := tits_transport (n := n) (b := b)
      (heps := heps) σ x y
    have h_of : titsCocycleAll (n := n) b eps x y =
        Multiplicative.ofAdd
          (titsAlphaAdd (n := n) b eps x y) := rfl
    calc titsCocycleAll (n := n) b eps x y *
        Multiplicative.ofAdd (titsQAdd (n := n) b eps σ (x * y))
        = Multiplicative.ofAdd (titsAlphaAdd (n := n) b eps x y) *
          Multiplicative.ofAdd (titsQAdd (n := n) b eps σ (x * y)) := by
          rw [h_of]
      _ = Multiplicative.ofAdd
            (titsAlphaAdd (n := n) b eps x y +
              titsQAdd (n := n) b eps σ (x * y)) := by
          rw [← ofAdd_add]
      _ = Multiplicative.ofAdd
            (titsQAdd (n := n) b eps σ x +
              titsQAdd (n := n) b eps σ y +
              titsAlphaAdd (n := n) b eps
                (permute σ x) (permute σ y)) := by
          rw [h_add]
      _ = Multiplicative.ofAdd (titsQAdd (n := n) b eps σ x) *
          Multiplicative.ofAdd (titsQAdd (n := n) b eps σ y) *
          Multiplicative.ofAdd
            (titsAlphaAdd (n := n) b eps
              (permute σ x) (permute σ y)) := by
          rw [ofAdd_add, ofAdd_add]
      _ = Multiplicative.ofAdd (titsQAdd (n := n) b eps σ x) *
          Multiplicative.ofAdd (titsQAdd (n := n) b eps σ y) *
          titsCocycleAll (n := n) b eps
            (permuteHom (A := A) σ x)
            (permuteHom (A := A) σ y) := rfl

/-- The group homomorphism induced by the compatible Tits permutation map. -/
def titsCompatibleHom (σ : Equiv.Perm (Fin n)) :
    TitsExtension (n := n) b eps →*
      TitsExtension (n := n) b eps :=
  (titsCompatibleMap (n := n) b eps heps σ).toHom

@[simp]
theorem titsCompatibleHom_base (σ : Equiv.Perm (Fin n))
    (h : TitsExtension (n := n) b eps) :
    (titsCompatibleHom (n := n) b eps heps σ h).base =
      permute σ h.base :=
  rfl

@[simp]
theorem titsCompatibleHom_coeff (σ : Equiv.Perm (Fin n))
    (h : TitsExtension (n := n) b eps) :
    (titsCompatibleHom (n := n) b eps heps σ h).coeff =
      h.coeff *
        Multiplicative.ofAdd
          (titsQAdd (n := n) b eps σ h.base) := by
  simp [titsCompatibleHom, titsCompatibleMap,
    NormalizedCocycleExtension.CompatibleMap.toHom_coeff]

theorem titsCompatibleHom_one :
    titsCompatibleHom (n := n) b eps heps
      (1 : Equiv.Perm (Fin n)) =
      MonoidHom.id (TitsExtension (n := n) b eps) := by
  apply MonoidHom.ext
  intro x
  apply TitsExtension.ext
  · simp [titsCompatibleHom, titsCompatibleMap,
      permuteHom_one]
  · simp [titsCompatibleHom, titsCompatibleMap,
      titsQAdd_one_perm (n := n) b heps x.base]

theorem titsCompatibleHom_mul (σ τ : Equiv.Perm (Fin n)) :
    titsCompatibleHom (n := n) b eps heps (σ * τ) =
      (titsCompatibleHom (n := n) b eps heps σ).comp
        (titsCompatibleHom (n := n) b eps heps τ) := by
  apply MonoidHom.ext
  intro x
  apply TitsExtension.ext
  · simp [titsCompatibleHom, titsCompatibleMap,
      permuteHom_mul]
  · simp only [titsCompatibleHom, titsCompatibleMap,
      NormalizedCocycleExtension.CompatibleMap.toHom_coeff,
      MonoidHom.comp_apply, MonoidHom.id_apply]
    have h_q := titsQAdd_comp (n := n) b heps σ τ x.base
    calc (x.coeff * Multiplicative.ofAdd
            (titsQAdd (n := n) b eps (σ * τ) x.base))
        = x.coeff * Multiplicative.ofAdd
            (titsQAdd (n := n) b eps τ x.base +
              titsQAdd (n := n) b eps σ
                (permute τ x.base)) := by
          rw [h_q]
      _ = x.coeff * (Multiplicative.ofAdd
            (titsQAdd (n := n) b eps τ x.base) *
          Multiplicative.ofAdd
            (titsQAdd (n := n) b eps σ
              (permute τ x.base))) := by
          rw [← ofAdd_add]
      _ = (x.coeff * Multiplicative.ofAdd
            (titsQAdd (n := n) b eps τ x.base)) *
          Multiplicative.ofAdd
            (titsQAdd (n := n) b eps σ
              (permute τ x.base)) := by
          rw [mul_assoc]
      _ = ((titsCompatibleHom (n := n) b eps heps σ)
            ((titsCompatibleHom (n := n) b eps heps τ) x)).coeff := by
          simp [titsCompatibleHom, titsCompatibleMap,
            NormalizedCocycleExtension.CompatibleMap.toHom_coeff]

/-- The invertible map induced by the compatible Tits permutation data. -/
def titsCompatibleEquiv (σ : Equiv.Perm (Fin n)) :
    TitsExtension (n := n) b eps ≃*
      TitsExtension (n := n) b eps where
  toFun := titsCompatibleHom (n := n) b eps heps σ
  invFun := titsCompatibleHom (n := n) b eps heps σ⁻¹
  left_inv x := by
    have h_comp :
        (titsCompatibleHom (n := n) b eps heps σ⁻¹).comp
          (titsCompatibleHom (n := n) b eps heps σ) =
          MonoidHom.id (TitsExtension (n := n) b eps) := by
      rw [← titsCompatibleHom_mul (n := n) b eps heps
        σ⁻¹ σ, inv_mul_cancel,
        titsCompatibleHom_one (n := n) b eps heps]
    have h_eq :=
      congrArg (fun f :
        TitsExtension (n := n) b eps →*
          TitsExtension (n := n) b eps => f x) h_comp
    simpa using h_eq
  right_inv x := by
    have h_comp :
        (titsCompatibleHom (n := n) b eps heps σ).comp
          (titsCompatibleHom (n := n) b eps heps σ⁻¹) =
          MonoidHom.id (TitsExtension (n := n) b eps) := by
      rw [← titsCompatibleHom_mul (n := n) b eps heps
        σ σ⁻¹, mul_inv_cancel,
        titsCompatibleHom_one (n := n) b eps heps]
    have h_eq :=
      congrArg (fun f :
        TitsExtension (n := n) b eps →*
          TitsExtension (n := n) b eps => f x) h_comp
    simpa using h_eq
  map_mul' x y := by
    have h := (titsCompatibleHom (n := n) b eps heps σ).map_mul
      x y
    exact h

@[simp]
theorem titsCompatibleEquiv_apply (σ : Equiv.Perm (Fin n))
    (x : TitsExtension (n := n) b eps) :
    titsCompatibleEquiv (n := n) b eps heps σ x =
      titsCompatibleHom (n := n) b eps heps σ x :=
  rfl

@[simp]
theorem titsCompatibleEquiv_symm_apply
    (σ : Equiv.Perm (Fin n))
    (x : TitsExtension (n := n) b eps) :
    (titsCompatibleEquiv (n := n) b eps heps σ).symm x =
      titsCompatibleHom (n := n) b eps heps σ⁻¹ x :=
  rfl

theorem titsCompatibleEquiv_one :
    titsCompatibleEquiv (n := n) b eps heps
      (1 : Equiv.Perm (Fin n)) =
      MulEquiv.refl (TitsExtension (n := n) b eps) := by
  apply MulEquiv.ext
  intro x
  simp [titsCompatibleEquiv, titsCompatibleHom_one]

theorem titsCompatibleEquiv_mul (σ τ : Equiv.Perm (Fin n))
    (x : TitsExtension (n := n) b eps) :
    titsCompatibleEquiv (n := n) b eps heps (σ * τ) x =
      titsCompatibleEquiv (n := n) b eps heps σ
        (titsCompatibleEquiv (n := n) b eps heps τ x) := by
  simp [titsCompatibleEquiv, titsCompatibleHom_mul]

/-- The permutation action on the Tits extension as a group homomorphism. -/
def titsActionHom :
    Equiv.Perm (Fin n) →* MulAut
      (TitsExtension (n := n) b eps) where
  toFun σ := titsCompatibleEquiv (n := n) b eps heps σ
  map_one' := by
    simp only [titsCompatibleEquiv_one]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    simp only [titsCompatibleEquiv_mul,
      MulAut.mul_apply]

theorem titsActionHom_apply (σ : Equiv.Perm (Fin n))
    (x : TitsExtension (n := n) b eps) :
    (titsActionHom (n := n) b eps heps σ) x =
      titsCompatibleHom (n := n) b eps heps σ x :=
  rfl

@[simp]
theorem titsActionHom_one_apply
    (x : TitsExtension (n := n) b eps) :
    (titsActionHom (n := n) b eps heps
      (1 : Equiv.Perm (Fin n))) x = x := by
  simp only [titsActionHom_apply,
    titsCompatibleHom_one, MonoidHom.id_apply]

theorem titsActionHom_mul_apply (σ τ : Equiv.Perm (Fin n))
    (x : TitsExtension (n := n) b eps) :
    (titsActionHom (n := n) b eps heps (σ * τ)) x =
      (titsActionHom (n := n) b eps heps σ)
        ((titsActionHom (n := n) b eps heps τ) x) := by
  simp only [titsActionHom_apply, titsCompatibleHom_mul,
    MonoidHom.comp_apply]

/-- The actual permutation action on the constructed Tits extension. -/
@[instance_reducible]
def titsMulAction :
    MulAction (Equiv.Perm (Fin n))
      (TitsExtension (n := n) b eps) where
  smul σ x := titsCompatibleHom (n := n) b eps heps σ x
  one_smul x := by
    change titsCompatibleHom (n := n) b eps heps
        (1 : Equiv.Perm (Fin n)) x = x
    rw [titsCompatibleHom_one, MonoidHom.id_apply]
  mul_smul σ τ x := by
    change titsCompatibleHom (n := n) b eps heps
        (σ * τ) x =
      titsCompatibleHom (n := n) b eps heps σ
        (titsCompatibleHom (n := n) b eps heps τ x)
    rw [titsCompatibleHom_mul, MonoidHom.comp_apply]

end TitsAction

section Naturality

variable {n : ℕ} {A : Type uA} {B : Type uB}
  [CommGroup A] [AddCommGroup B]
variable {A' : Type uA'} {B' : Type uB'}
  [CommGroup A'] [AddCommGroup B']
variable {b : SkewBicharacter A B}
  {b' : SkewBicharacter A' B'}

theorem orientUnit_naturality
    (φ : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (hε : φ.source eps = eps')
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    φ.source (orientUnit eps σ i) =
      orientUnit eps' σ i := by
  unfold orientUnit
  rw [map_mul, map_mul, parityUnit_naturality φ hε σ]
  have h1 : φ.source (indexParityUnit eps i) =
      indexParityUnit eps' i := by
    rw [indexParityUnit_naturality
      (f := φ.source) (eps := eps) i, hε]
  have h2 : φ.source (indexParityUnit eps (σ i)) =
      indexParityUnit eps' (σ i) := by
    rw [indexParityUnit_naturality
      (f := φ.source) (eps := eps) (σ i), hε]
  rw [h1, h2]

theorem orientAdd_naturality
    (φ : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (hε : φ.source eps = eps')
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    φ.target (orientAdd (b := b) eps σ u) =
      orientAdd (b := b') eps' σ
        (mapTuple (f := φ.source) u) := by
  unfold orientAdd
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h_eval := φ.map_eval (orientUnit eps σ i) (u i)
  rw [h_eval, orientUnit_naturality φ hε σ i]
  rfl

theorem titsAlphaAdd_naturality
    (φ : SkewBicharacter.Hom b b')
    (eps : A) (u v : Fin n → A) :
    φ.target (titsAlphaAdd (n := n) b eps u v) =
      titsAlphaAdd (n := n) b' (φ.source eps)
        (mapTuple (f := φ.source) u)
        (mapTuple (f := φ.source) v) := by
  have h_low := lowerSum_naturality
    (ι := Fin n) (b := b) (b' := b') φ u v
  have h_prod_u : φ.source (tupleProd (n := n) u) =
      tupleProd (n := n) (mapTuple (f := φ.source) u) :=
    tupleProd_naturality (b := b) (b' := b') φ u
  have h_prod_v : φ.source (tupleProd (n := n) v) =
      tupleProd (n := n) (mapTuple (f := φ.source) v) :=
    tupleProd_naturality (b := b) (b' := b') φ v
  calc φ.target (titsAlphaAdd (n := n) b eps u v)
      = φ.target
          (lowerSum (ι := Fin n) b u v -
            b.eval (tupleProd (n := n) u)
              (tupleProd (n := n) v)) := rfl
    _ = φ.target (lowerSum (ι := Fin n) b u v) -
          φ.target
            (b.eval (tupleProd (n := n) u)
              (tupleProd (n := n) v)) := by
        rw [map_sub]
    _ = lowerSum (ι := Fin n) b'
          (mapTuple (f := φ.source) u)
          (mapTuple (f := φ.source) v) -
          b'.eval (φ.source (tupleProd (n := n) u))
            (φ.source (tupleProd (n := n) v)) := by
        rw [h_low, φ.map_eval]
    _ = lowerSum (ι := Fin n) b'
          (mapTuple (f := φ.source) u)
          (mapTuple (f := φ.source) v) -
          b'.eval
            (tupleProd (n := n)
              (mapTuple (f := φ.source) u))
            (tupleProd (n := n)
              (mapTuple (f := φ.source) v)) := by
        rw [h_prod_u, h_prod_v]
    _ = titsAlphaAdd (n := n) b' (φ.source eps)
          (mapTuple (f := φ.source) u)
          (mapTuple (f := φ.source) v) := rfl

theorem titsQAdd_naturality
    (φ : SkewBicharacter.Hom b b')
    {eps : A} {eps' : A'} (hε : φ.source eps = eps')
    (σ : Equiv.Perm (Fin n)) (u : Fin n → A) :
    φ.target (titsQAdd (n := n) b eps σ u) =
      titsQAdd (n := n) b' eps' σ
        (mapTuple (f := φ.source) u) := by
  unfold titsQAdd
  rw [map_add]
  have h_inv := inversionSum_naturality
    (ι := Fin n) (b := b) (b' := b') φ σ u
  have h_orient := orientAdd_naturality
    (b := b) (b' := b') φ hε σ u
  rw [h_inv, h_orient]

end Naturality

end PermutationBilinearTitsAction

end
