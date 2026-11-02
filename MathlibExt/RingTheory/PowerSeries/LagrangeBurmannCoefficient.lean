/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

open PowerSeries Finset


private theorem coeff_X_pow_mul_coeff {R : Type*} [CommRing R] (k n : ℕ) (F : PowerSeries R) :
    coeff n (X ^ k * F) = if k ≤ n then coeff (n - k) F else 0 := by
  by_cases h : k ≤ n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have hsub : k + d - k = d := Nat.add_sub_cancel_left k d
    simp only [h, hsub, ↓reduceIte]
    rw [add_comm k d]
    exact coeff_X_pow_mul F k d
  · simp only [h, ↓reduceIte]
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨i, j⟩ hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hi : i ≤ n := by omega
    have hik : i ≠ k := by omega
    simp only [coeff_X_pow, hik, ↓reduceIte, zero_mul]

private theorem coeff_X_mul_zero {R : Type*} [CommRing R] (F : PowerSeries R) :
    coeff 0 (X * F) = 0 := by
  have h := coeff_X_pow_mul_coeff (R := R) 1 0 F
  simp

private theorem coeff_X_mul_succ {R : Type*} [CommRing R] (m : ℕ) (F : PowerSeries R) :
    coeff (m + 1) (X * F) = coeff m F := by
  have h := coeff_X_pow_mul_coeff (R := R) 1 (m + 1) F
  simp

private theorem Apow_eq {R : Type*} [CommRing R] (A phi : PowerSeries R)
    (hfix : A = X * subst A phi) (k : ℕ) :
    A ^ k = X ^ k * (subst A phi) ^ k := by
  conv_lhs => rw [hfix]
  rw [mul_pow]

private theorem coeff_Apow {R : Type*} [CommRing R] (A phi : PowerSeries R)
    (hfix : A = X * subst A phi) (k n : ℕ) :
    coeff n (A ^ k) = if k ≤ n then coeff (n - k) ((subst A phi) ^ k) else 0 := by
  rw [Apow_eq A phi hfix k]
  exact coeff_X_pow_mul_coeff k n _

private theorem coeff_subst_eq_sum_range {R : Type*} [CommRing R] (A g : PowerSeries R)
    (hsubst : HasSubst A) (phi : PowerSeries R)
    (hfix : A = X * subst A phi) (n : ℕ) :
    coeff n (subst A g) = ∑ k ∈ Finset.range (n + 1), coeff k g * coeff n (A ^ k) := by
  have hfs := coeff_subst' hsubst g n
  have hsub : Function.support (fun d => coeff d g • coeff n (A ^ d)) ⊆
      ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra hc
    simp only [Finset.coe_range, Set.mem_Iio] at hc
    have hle : ¬ d ≤ n := by omega
    have hA : coeff n (A ^ d) = 0 := by
      rw [coeff_Apow A phi hfix d n]
      simp [hle]
    simp [hA] at hd
  rw [hfs, finsum_eq_sum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_eq_mul]

private theorem deriv_X_pow {R : Type*} [CommRing R] (k : ℕ) :
    derivative (X ^ k : PowerSeries R) = C (k : R) * X ^ (k - 1) := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have hpow := derivative_pow (R := R) (X : PowerSeries R) k
    rw [derivative_X, mul_one] at hpow
    rw [hpow]
    simp

private theorem coeff_derivXk_mul {R : Type*} [CommRing R] (phi : PowerSeries R)
    (k n m' : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hm : m' = n - 1) :
    coeff m' (derivative (X ^ k : PowerSeries R) * phi ^ n)
      = (k : R) * coeff (n - k) (phi ^ n) := by
  rw [deriv_X_pow, mul_assoc, coeff_C_mul]
  congr 1
  have hk1' : k - 1 ≤ m' := by omega
  have hsub : m' - (k - 1) = n - k := by omega
  rw [coeff_X_pow_mul_coeff]
  simp only [hk1', ↓reduceIte, hsub]

private theorem coeff_derivX0_mul {R : Type*} [CommRing R] (phi : PowerSeries R) (n m' : ℕ) :
    coeff m' (derivative ((X : PowerSeries R) ^ 0) * phi ^ n) = 0 := by
  simp

private theorem reduction {R : Type*} [CommRing R] (A phi g : PowerSeries R)
    (hsubst : HasSubst A) (hfix : A = X * subst A phi) (n : ℕ) (hn : 0 < n)
    (hmono : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (n : R) * coeff n (A ^ k) = coeff (n - 1) (derivative (X ^ k : PowerSeries R) * phi ^ n)) :
    (n : R) * coeff n (subst A g) =
      coeff (n - 1) (derivative g * phi ^ n) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hmono ⊢
  push_cast at hmono ⊢
  have hLHS : (↑m' + 1 : R) * coeff (m' + 1) (subst A g)
      = ∑ k ∈ Finset.range (m' + 1 + 1), coeff k g * ((↑m' + 1 : R) * coeff (m' + 1) (A ^ k)) := by
    rw [coeff_subst_eq_sum_range A g hsubst phi hfix]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hRHS : coeff m' (derivative g * phi ^ (m' + 1))
      = ∑ k ∈ Finset.range (m' + 1 + 1), coeff k g * coeff m'
          (derivative (X ^ k : PowerSeries R) * phi ^ (m' + 1)) := by
    rw [coeff_mul]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (derivative g) * coeff j (phi ^ (m' + 1))) m']
    have hexpand : ∀ i ∈ Finset.range (m' + 1),
        coeff i (derivative g) * coeff (m' - i) (phi ^ (m' + 1))
        = coeff (i + 1) g * coeff m' (derivative (X ^ (i + 1) : PowerSeries R) * phi ^
            (m' + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hkn : i + 1 ≤ m' + 1 := by omega
      have hk1 : 1 ≤ i + 1 := by omega
      have hcd := coeff_derivative (R := R) g i
      have hck := coeff_derivXk_mul (R := R) phi (i + 1) (m' + 1) m' hk1 hkn rfl
      rw [hcd, hck]
      have e1 : ((i + 1 : ℕ) : R) = (i : R) + 1 := by push_cast; ring
      have e2 : (m' + 1 - (i + 1) : ℕ) = m' - i := by omega
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl (fun i hi => hexpand i hi)]
    rw [Finset.sum_range_succ' (fun k => coeff k g * coeff m'
        (derivative (X ^ k : PowerSeries R) * phi ^ (m' + 1))) (m' + 1)]
    simp
  rw [hLHS, hRHS]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  by_cases hk0 : k = 0
  · subst hk0
    simp
  · have hk1 : 1 ≤ k := by omega
    have hkn : k ≤ m' + 1 := by omega
    have hmk := hmono k hk1 hkn
    rw [hmk]

private theorem exact_key {R : Type*} [CommRing R] (A U : PowerSeries R)
    (hAU : A = X * U) (k m : ℕ) (hk : 0 < k) :
    (m + k : R) * coeff m (U ^ k) = (k : R) * coeff m (U ^ (k - 1) * derivative A) := by
  have hA' : derivative A = U + X * derivative U := by
    rw [hAU, Derivation.leibniz, derivative_X]
    simp only [smul_eq_mul, mul_one]
    rw [add_comm]
  have hUk : U ^ (k - 1) * U = U ^ k := by
    conv_rhs => rw [← Nat.sub_add_cancel hk, pow_add, pow_one]
  have hexpand : U ^ (k - 1) * derivative A = U ^ k + X * (U ^ (k - 1) * derivative U) := by
    rw [hA', mul_add, hUk]
    ring
  by_cases hm : m = 0
  · subst hm
    rw [hexpand, map_add, coeff_X_mul_zero, add_zero]
    simp
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp only [Nat.succ_eq_add_one] at hm ⊢
    have hX : coeff (m' + 1) (X * (U ^ (k - 1) * derivative U))
        = coeff m' (U ^ (k - 1) * derivative U) :=
      coeff_X_mul_succ m' _
    have hpow := derivative_pow (R := R) U k
    have hderiv := coeff_derivative (U ^ k) m'
    have hU : (k : R) * coeff m' (U ^ (k - 1) * derivative U)
        = coeff m' (derivative (U ^ k)) := by
      rw [hpow, mul_assoc, show (k : PowerSeries R) = C (k : R) from by simp, coeff_C_mul]
    have hUm : (k : R) * coeff m' (U ^ (k - 1) * derivative U)
        = ((m' + 1 : ℕ) : R) * coeff (m' + 1) (U ^ k) := by
      rw [hU, hderiv, Nat.cast_add, Nat.cast_one, mul_comm]
    rw [hexpand, map_add, hX]
    push_cast at hUm ⊢
    linear_combination -hUm
private theorem coeff_pow_eq_zero_of_const_zero {R : Type*} [CommRing R] (B : PowerSeries R)
    (hB : constantCoeff B = 0) (k n : ℕ) (hkn : n < k) :
    coeff n (B ^ k) = 0 := by
  obtain ⟨C, hC⟩ := X_dvd_iff.mpr hB
  have : B ^ k = X ^ k * C ^ k := by rw [hC, mul_pow]
  rw [this, coeff_X_pow_mul_coeff]
  simp only [Nat.not_le.mpr hkn, ↓reduceIte]

private theorem coeff_subst_eq_sum_range_of_const {R : Type*} [CommRing R] (B g : PowerSeries R)
    (hsubst : HasSubst B) (hB : constantCoeff B = 0) (n : ℕ) :
    coeff n (subst B g) = ∑ k ∈ Finset.range (n + 1), coeff k g * coeff n (B ^ k) := by
  have hfs := coeff_subst' hsubst g n
  have hsub : Function.support (fun d => coeff d g • coeff n (B ^ d)) ⊆
      ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_contra hc
    simp only [Finset.coe_range, Set.mem_Iio] at hc
    have hle : n < d := by omega
    have hBpow : coeff n (B ^ d) = 0 := coeff_pow_eq_zero_of_const_zero B hB d n hle
    simp [hBpow] at hd
  rw [hfs, finsum_eq_sum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro k _
  rw [smul_eq_mul]

-- powers agree if series agree up to i
private theorem pow_coeff_agree {R : Type*} [CommRing R] (B B' : PowerSeries R) (i : ℕ)
    (h : ∀ j, j ≤ i → coeff j B = coeff j B') (k a : ℕ) (ha : a ≤ i) :
    coeff a (B ^ k) = coeff a (B' ^ k) := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨u, v⟩ huv
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huv
    have hu : u ≤ i := by omega
    have hv : v ≤ i := by omega
    rw [ih u hu, h v hv]

private theorem subst_coeff_agree {R : Type*} [CommRing R] (B B' Phi : PowerSeries R)
    (hB : HasSubst B) (hB' : HasSubst B')
    (hBc : constantCoeff B = 0) (hBc' : constantCoeff B' = 0)
    (i : ℕ) (h : ∀ j, j ≤ i → coeff j B = coeff j B') :
    coeff i (subst B Phi) = coeff i (subst B' Phi) := by
  rw [coeff_subst_eq_sum_range_of_const B Phi hB hBc,
    coeff_subst_eq_sum_range_of_const B' Phi hB' hBc']
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_coeff_agree B B' i h k i (by omega)]


private theorem exists_fixed_point {S : Type*} [CommRing S] (Phi : PowerSeries S) :
    ∃ A : PowerSeries S, HasSubst A ∧ A = X * subst A Phi := by
  let f : PowerSeries S → PowerSeries S := fun P => X * subst P Phi
  let B : ℕ → PowerSeries S := fun m => f^[m] 0
  have hB0 : B 0 = 0 := rfl
  have hBstep : ∀ m, B (m + 1) = X * subst (B m) Phi := by
    intro m
    change f^[m + 1] 0 = f (f^[m] 0)
    have h := Function.iterate_succ_apply' f m 0
    have hs : m.succ = m + 1 := Nat.succ_eq_add_one m
    rw [hs] at h
    exact h
  have hBconst : ∀ m, constantCoeff (B m) = 0 := by
    intro m
    induction m with
    | zero => rw [hB0]; exact map_zero _
    | succ m ih =>
      have h := hBstep m
      rw [h, map_mul, constantCoeff_X, zero_mul]
  have hBsubst : ∀ m, HasSubst (B m) :=
    fun m => HasSubst.of_constantCoeff_zero (hBconst m)
  have hstab : ∀ m i, i ≤ m → coeff i (B m) = coeff i (B (m + 1)) := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      have h1 : B (0 + 1) = X * subst (B 0) Phi := hBstep 0
      rw [hB0, h1, map_zero]
      exact (coeff_X_mul_zero _).symm
    | succ m ih =>
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        have l0 : coeff 0 (B (m + 1)) = 0 := by
          rw [coeff_zero_eq_constantCoeff_apply, hBconst]
        have r0 : coeff 0 (B (m + 1 + 1)) = 0 := by
          rw [coeff_zero_eq_constantCoeff_apply, hBconst]
        rw [l0, r0]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        simp only [Nat.succ_eq_add_one] at hi ⊢
        have hj : j ≤ m := by omega
        have e1 : coeff (j + 1) (B (m + 1)) = coeff j (subst (B m) Phi) := by
          rw [hBstep m]
          exact coeff_X_mul_succ j _
        have e2 : coeff (j + 1) (B (m + 1 + 1)) = coeff j (subst (B (m + 1)) Phi) := by
          rw [hBstep (m + 1)]
          exact coeff_X_mul_succ j _
        rw [e1, e2]
        apply subst_coeff_agree _ _ _ (hBsubst m) (hBsubst (m + 1)) (hBconst m) (hBconst (m + 1)) j
        intro t ht
        exact ih t (by omega)
  have hstable : ∀ i m, i ≤ m → coeff i (B m) = coeff i (B (i + 1)) := by
    intro i m him
    induction m, him using Nat.le_induction with
    | base => exact hstab i i (by omega)
    | succ m hmn ih =>
      have h2 : coeff i (B m) = coeff i (B (m + 1)) := hstab m i (by omega)
      rw [h2] at ih
      exact ih
  let D : PowerSeries S := PowerSeries.mk fun i => coeff i (B (i + 1))
  have hDcoeff : ∀ i, coeff i D = coeff i (B (i + 1)) := fun i => PowerSeries.coeff_mk i _
  have hDagree : ∀ m i, i ≤ m → coeff i (B m) = coeff i D := by
    intro m i him
    rw [hDcoeff]
    exact hstable i m him
  have hDconst : constantCoeff D = 0 := by
    have h0 : coeff 0 D = 0 := by
      rw [hDcoeff]
      have h1 : B (0 + 1) = X * subst (B 0) Phi := hBstep 0
      rw [h1]
      exact coeff_X_mul_zero _
    rw [coeff_zero_eq_constantCoeff_apply] at h0
    exact h0
  refine ⟨D, HasSubst.of_constantCoeff_zero hDconst, ?_⟩
  apply PowerSeries.ext
  intro m
  by_cases hm0 : m = 0
  · subst hm0
    have l : coeff 0 D = 0 := by
      rw [hDcoeff]
      have h1 : B (0 + 1) = X * subst (B 0) Phi := hBstep 0
      rw [h1]
      exact coeff_X_mul_zero _
    have r : coeff 0 (X * subst D Phi) = 0 := coeff_X_mul_zero _
    rw [l, r]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    simp only [Nat.succ_eq_add_one] at *
    have lhs : coeff (j + 1) D = coeff (j + 1) (B (j + 1 + 1)) := by
      rw [hDcoeff]
    have rhs : coeff (j + 1) (X * subst D Phi) = coeff j (subst D Phi) :=
      coeff_X_mul_succ j _
    have hDsubst : HasSubst D := HasSubst.of_constantCoeff_zero hDconst
    have agree : coeff j (subst D Phi) = coeff j (subst (B (j + 1)) Phi) :=
      subst_coeff_agree D (B (j + 1)) Phi hDsubst (hBsubst (j + 1)) hDconst (hBconst (j + 1)) j
        (fun t ht => by rw [hDagree (j + 1) t (by omega)])
    have fin : coeff j (subst (B (j + 1)) Phi) = coeff (j + 1) (B (j + 1 + 1)) := by
      have hbj : B (j + 1 + 1) = X * subst (B (j + 1)) Phi := hBstep (j + 1)
      rw [hbj]
      exact (coeff_X_mul_succ j _).symm
    rw [lhs, rhs, agree, fin]

private theorem eq_of_fixed_point {R : Type*} [CommRing R] (Phi : PowerSeries R)
    (B1 B2 : PowerSeries R)
    (h1s : HasSubst B1) (h2s : HasSubst B2)
    (h1c : constantCoeff B1 = 0) (h2c : constantCoeff B2 = 0)
    (h1 : B1 = X * subst B1 Phi) (h2 : B2 = X * subst B2 Phi) :
    B1 = B2 := by
  apply PowerSeries.ext
  intro m
  have key : ∀ m i, i ≤ m → coeff i B1 = coeff i B2 := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h1c, h2c]
    | succ m ih =>
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h1c, h2c]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        simp only [Nat.succ_eq_add_one] at hi ⊢
        have hj : j ≤ m := by omega
        have e1 : coeff (j + 1) B1 = coeff j (subst B1 Phi) := by
          conv_lhs => rw [h1]
          exact coeff_X_mul_succ j _
        have e2 : coeff (j + 1) B2 = coeff j (subst B2 Phi) := by
          conv_lhs => rw [h2]
          exact coeff_X_mul_succ j _
        rw [e1, e2]
        apply subst_coeff_agree B1 B2 Phi h1s h2s h1c h2c j
        intro t ht
        exact ih t (by omega)
  exact key m m (by omega)

-- universal monomial identity (torsion-free)
private theorem mono_universal {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    (Phi A : PowerSeries S) (hsubst : HasSubst A) (hA0 : constantCoeff A = 0)
    (hfix : A = X * subst A Phi) :
    ∀ n' k : ℕ, 1 ≤ k → k ≤ n' →
      (n' : S) * coeff n' (A ^ k) = (k : S) * coeff (n' - k) (Phi ^ n') := by
  have hA0' : ∀ m, m = 0 → coeff m A = 0 := by
    intro m hm; subst hm; rw [coeff_zero_eq_constantCoeff_apply, hA0]
  have cum : ∀ N' n' k : ℕ, n' ≤ N' → 1 ≤ k → k ≤ n' →
      (n' : S) * coeff n' (A ^ k) = (k : S) * coeff (n' - k) (Phi ^ n') := by
    intro N'
    induction N' with
    | zero =>
      intro n' k hn' hk1 hkn
      omega
    | succ N' ih =>
      intro n' k hn' hk1 hkn
      by_cases hn0 : n' ≤ N'
      · exact ih n' k hn0 hk1 hkn
      · have hneq : n' = N' + 1 := by omega
        subst hneq
        by_cases hm0 : N' + 1 - k = 0
        · -- m = 0 so k = N'+1
          have hkN : k = N' + 1 := by omega
          have hAkk : coeff (N' + 1) (A ^ k) = coeff 0 ((subst A Phi) ^ k) := by
            have h := coeff_Apow (R := S) A Phi hfix k (N' + 1)
            rw [ite_eq_left hkn] at h
            have : N' + 1 - k = 0 := hm0
            rw [this] at h
            exact h
          have hU0 : coeff 0 (subst A Phi) = coeff 0 Phi := by
            rw [coeff_subst_eq_sum_range_of_const A Phi hsubst hA0 0]
            simp
          have hUk0 : coeff 0 ((subst A Phi) ^ k) = coeff 0 (Phi ^ k) := by
            have e1 : coeff 0 ((subst A Phi) ^ k) = (coeff 0 (subst A Phi)) ^ k := by
              rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
              exact map_pow _ _ _
            have e2 : coeff 0 (Phi ^ k) = (coeff 0 Phi) ^ k := by
              rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
              exact map_pow _ _ _
            rw [e1, e2, hU0]
          have hcast : ((N' + 1 : ℕ) : S) = ((k : ℕ) : S) := by rw [← hkN]
          have hsub : N' + 1 - k = 0 := hm0
          rw [hAkk, hUk0, hcast, hsub]
          -- goal k * [Phi^k]_0 = k * [Phi^{N'+1}]_0 with k = N'+1: exponents equal via hkN
          have hexp : Phi ^ (N' + 1) = Phi ^ k := by rw [← hkN]
          rw [hexp]
        · -- m ≥ 1
          have hmpos : 0 < N' + 1 - k := by omega
          have hmN : N' + 1 - k ≤ N' := by omega
          -- key expansion and m * G = 0
          have hAkm : coeff (N' + 1) (A ^ k) = coeff (N' + 1 - k) ((subst A Phi) ^ k) := by
            have h := coeff_Apow (R := S) A Phi hfix k (N' + 1)
            rw [ite_eq_left hkn] at h
            exact h
          have hUpow : (subst A Phi) ^ k = subst A (Phi ^ k) := by
            rw [subst_pow hsubst]
          have hexp : coeff (N' + 1 - k) ((subst A Phi) ^ k)
              = ∑ s ∈ Finset.range (N' + 1 - k + 1), coeff s (Phi ^ k) * coeff (N' + 1 - k)
                  (A ^ s) := by
            rw [hUpow]
            exact coeff_subst_eq_sum_range_of_const A (Phi ^ k) hsubst hA0 _
          have hmk : N' + 1 - k + k = N' + 1 := Nat.sub_add_cancel hkn
          -- peel s = 0 term (vanishes since m >= 1)
          have h0van : coeff (N' + 1 - k) (A ^ 0) = 0 := by
            simp only [pow_zero]
            have hne : N' + 1 - k ≠ 0 := by omega
            simp [hne]
          have hF0 : coeff 0 (Phi ^ k) * coeff (N' + 1 - k) (A ^ 0) = 0 := by
            rw [h0van, mul_zero]
          have hsplit : ∑ s ∈ Finset.range (N' + 1 - k + 1), coeff s (Phi ^ k) * coeff (N' + 1 - k)
              (A ^ s)
              = ∑ s ∈ Finset.range (N' + 1 - k), coeff (s + 1) (Phi ^ k) * coeff (N' + 1 - k)
                  (A ^ (s + 1)) := by
            rw [Finset.sum_range_succ', hF0, add_zero]
          -- n' * [U^k]_m via IH on each term
          have hmk : N' + 1 - k + k = N' + 1 := Nat.sub_add_cancel hkn
          -- m * [U^k]_m via IH (weights match, no n'/k split inside sum)
          have hMU : ((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k) ((subst A Phi) ^ k)
              = ∑ s ∈ Finset.range (N' + 1 - k),
                coeff (s + 1) (Phi ^ k) * (((s + 1 : ℕ) : S) * coeff ((N' + 1 - k) - (s + 1))
                    (Phi ^ (N' + 1 - k))) := by
            rw [hexp, hsplit, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.mem_range] at hs
            have hs1 : 1 ≤ s + 1 := by omega
            have hsk : s + 1 ≤ N' + 1 - k := by omega
            have hih := ih (N' + 1 - k) (s + 1) hmN hs1 hsk
            rw [mul_left_comm, hih]
          -- T = k * E via derivative of Phi^k
          have hT : (∑ s ∈ Finset.range (N' + 1 - k),
                coeff (s + 1) (Phi ^ k) * (((s + 1 : ℕ) : S) * coeff ((N' + 1 - k) - (s + 1))
                    (Phi ^ (N' + 1 - k))))
              = (k : S) * coeff (N' + 1 - k - 1) (derivative Phi * Phi ^ N') := by
            have hder : derivative (Phi ^ k) = C (k : S) * (Phi ^ (k - 1) * derivative Phi) := by
              rw [derivative_pow, show (k : PowerSeries S) = C (k : S) from by simp, mul_assoc]
            have hconv : (∑ s ∈ Finset.range (N' + 1 - k),
                  coeff (s + 1) (Phi ^ k) * (((s + 1 : ℕ) : S) * coeff ((N' + 1 - k) - (s + 1))
                      (Phi ^ (N' + 1 - k))))
                = coeff (N' + 1 - k - 1) (derivative (Phi ^ k) * Phi ^ (N' + 1 - k)) := by
              have hms : N' + 1 - k - 1 + 1 = N' + 1 - k := Nat.sub_add_cancel hmpos
              rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                  (fun i j => coeff i (derivative (Phi ^ k)) * coeff j (Phi ^ (N' + 1 - k)))
                      (N' + 1 - k - 1)]
              have hms2 : (N' + 1 - k - 1).succ = N' + 1 - k := by omega
              rw [hms2]
              apply Finset.sum_congr rfl
              intro s hs
              rw [Finset.mem_range] at hs
              have hidx : N' + 1 - k - 1 - s = N' + 1 - k - (s + 1) := by omega
              rw [hidx, coeff_derivative, ← Nat.cast_add_one]
              ring
            rw [hconv, hder, mul_assoc, mul_assoc, coeff_C_mul]
            congr 1
            -- [Phi^{k-1} * deriv * Phi^m] = [deriv * Phi^N']
            have hpow : Phi ^ (k - 1) * Phi ^ (N' + 1 - k) = Phi ^ N' := by
              rw [← pow_add]
              congr 1
              omega
            calc coeff (N' + 1 - k - 1) (Phi ^ (k - 1) * (derivative Phi * Phi ^ (N' + 1 - k)))
                = coeff (N' + 1 - k - 1) (derivative Phi *
                    (Phi ^ (k - 1) * Phi ^ (N' + 1 - k))) := by
                  congr 1; ring
              _ = coeff (N' + 1 - k - 1) (derivative Phi * Phi ^ N') := by
                  rw [hpow]
          -- n' * E = m * [Phi^{n'}]_m via derivative of Phi^{n'}
          have hE : ((N' + 1 : ℕ) : S) * coeff (N' + 1 - k - 1) (derivative Phi * Phi ^ N')
              = ((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1)) := by
            have hderN : derivative (Phi ^ (N' + 1)) = C ((N' + 1 : ℕ) : S) *
                (Phi ^ N' * derivative Phi) := by
              have h := derivative_pow (R := S) Phi (N' + 1)
              have hsub : N' + 1 - 1 = N' := Nat.add_sub_cancel N' 1
              rw [hsub] at h
              rw [h, show ((N' + 1 : ℕ) : PowerSeries S) = C (((N' + 1 : ℕ)) : S) from by simp]
              ring
            have hcoeff : coeff (N' + 1 - k - 1) (derivative (Phi ^ (N' + 1)))
                = ((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1)) := by
              rw [coeff_derivative]
              have hsub : N' + 1 - k - 1 + 1 = N' + 1 - k := Nat.sub_add_cancel hmpos
              rw [hsub]
              have hcast : (((N' + 1 - k - 1 : ℕ)) : S) + 1 = ((N' + 1 - k : ℕ) : S) := by
                have h : N' + 1 - k - 1 + 1 = N' + 1 - k := Nat.sub_add_cancel hmpos
                have hc : ((((N' + 1 - k - 1 + 1 : ℕ))) : S) = (((N' + 1 - k : ℕ)) : S) := by rw [h]
                push_cast at hc
                -- hc : ... = ... ; massage to goal form
                linear_combination hc
              rw [hcast]
              ring
            -- n' * E = [(Phi^{n'})'] via comm + C_mul
            have hser : derivative Phi * Phi ^ N' = Phi ^ N' * derivative Phi := by ring
            have hnite : ((N' + 1 : ℕ) : S) * coeff (N' + 1 - k - 1) (derivative Phi * Phi ^ N')
                = coeff (N' + 1 - k - 1) (derivative (Phi ^ (N' + 1))) := by
              rw [hderN, coeff_C_mul, hser]
            rw [hnite, hcoeff]
          -- combine to m * LHS = m * RHS then cancel m
          have hmU : ((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k) ((subst A Phi) ^ k)
              = (k : S) * coeff (N' + 1 - k - 1) (derivative Phi * Phi ^ N') := by
            rw [hMU, hT]
          have hMG : ((N' + 1 - k : ℕ) : S) *
              (((N' + 1 : ℕ) : S) * coeff (N' + 1 - k) ((subst A Phi) ^ k))
              = ((N' + 1 - k : ℕ) : S) * ((k : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1))) := by
            have e1 : ((N' + 1 - k : ℕ) : S) *
                (((N' + 1 : ℕ) : S) * coeff (N' + 1 - k) ((subst A Phi) ^ k))
                = ((N' + 1 : ℕ) : S) * (((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k)
                    ((subst A Phi) ^ k)) := by
              ring
            have e2 : ((N' + 1 - k : ℕ) : S) * ((k : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1)))
                = (k : S) * (((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1))) := by
              ring
            calc ((N' + 1 - k : ℕ) : S) * (((N' + 1 : ℕ) : S) * coeff (N' + 1 - k)
                ((subst A Phi) ^ k))
                = ((N' + 1 : ℕ) : S) * (((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k)
                    ((subst A Phi) ^ k)) := e1
              _ = ((N' + 1 : ℕ) : S) * ((k : S) * coeff (N' + 1 - k - 1)
                  (derivative Phi * Phi ^ N')) := by
                  rw [hmU]
              _ = (k : S) * (((N' + 1 : ℕ) : S) * coeff (N' + 1 - k - 1)
                  (derivative Phi * Phi ^ N')) := by
                  ring
              _ = (k : S) * (((N' + 1 - k : ℕ) : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1))) := by
                  rw [hE]
              _ = ((N' + 1 - k : ℕ) : S) * ((k : S) * coeff (N' + 1 - k) (Phi ^ (N' + 1))) := by
                  ring
          have hmS : ((N' + 1 - k : ℕ) : S) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hcancel := mul_left_cancel₀ hmS hMG
          -- hcancel : n' * [U^k] = k * [Phi^{n'}] ; convert [U^k] to [A^k] via hAkm
          rw [hAkm]
          exact hcancel
  intro n' k hk1 hkn
  exact cum n' n' k (by omega) hk1 hkn

-- transport: universal monomial identity implies R monomial identity
private theorem mono_transport {R : Type*} [CommRing R] (A Phi : PowerSeries R)
    (hsubst : HasSubst A) (hA0 : constantCoeff A = 0)
    (hfix : A = X * subst A Phi) (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (n : R) * coeff n (A ^ k) = (k : R) * coeff (n - k) (Phi ^ n) := by
  -- universal base S = polynomials in phi-coefficients
  let S := MvPolynomial ℕ ℤ
  let e : S →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => coeff i Phi)
  let PhiS : PowerSeries S := PowerSeries.mk fun i => MvPolynomial.X i
  have hPhiS_coeff : ∀ i, coeff i PhiS = MvPolynomial.X i := fun i => PowerSeries.coeff_mk i _
  -- map PhiS to Phi
  have hmapPhi : PowerSeries.map e PhiS = Phi := by
    apply PowerSeries.ext
    intro i
    rw [coeff_map, hPhiS_coeff]
    change (MvPolynomial.eval₂Hom (Int.castRingHom R) fun i => coeff i Phi) (MvPolynomial.X i) = _
    simp
  -- exact solution over S
  obtain ⟨AS, hASsubst, hASfix⟩ := exists_fixed_point (S := S) PhiS
  have hAS0 : constantCoeff AS = 0 := by
    have h := congrArg constantCoeff hASfix
    simp only [map_mul, constantCoeff_X, zero_mul] at h
    exact h
  -- universal identity in S
  have huni := mono_universal (S := S) PhiS AS hASsubst hAS0 hASfix n k hk1 hkn
  -- map it to R
  have hmap : PowerSeries.map e AS = A := by
    -- map AS satisfies same fixed point as A, so equal by uniqueness
    have hmsubst : HasSubst (PowerSeries.map e AS) := by
      apply HasSubst.of_constantCoeff_zero
      change PowerSeries.constantCoeff (PowerSeries.map e AS) = 0
      have h1 : PowerSeries.constantCoeff (PowerSeries.map e AS) = e (constantCoeff AS) := by
        rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
      rw [h1, hAS0, map_zero]
    have hmfix : PowerSeries.map e AS = X * subst (PowerSeries.map e AS) Phi := by
      apply PowerSeries.ext
      intro m
      -- both sides are e-images of S-side coeffs which agree by hASfix
      have hS : coeff m AS = coeff m (X * subst AS PhiS) := by rw [← hASfix]
      have hR : coeff m (PowerSeries.map e AS) = e (coeff m AS) := coeff_map e m AS
      rw [hR, hS]
      -- RHS: [X * subst (map AS) Phi]_m ; relate to e([X * subst AS PhiS]_m) via expansions
      by_cases hm0 : m = 0
      · subst hm0
        rw [coeff_X_mul_zero, coeff_X_mul_zero]
        exact map_zero e
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
        simp only [Nat.succ_eq_add_one] at *
        rw [coeff_X_mul_succ, coeff_X_mul_succ]
        -- [subst (map AS) Phi]_{j} vs e([subst AS PhiS]_{j}) via finite sums
        rw [coeff_subst_eq_sum_range_of_const (PowerSeries.map e AS) Phi hmsubst (by
          have h1 : constantCoeff (PowerSeries.map e AS) = e (constantCoeff AS) := by
            rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
          rw [h1, hAS0, map_zero]) j]
        rw [coeff_subst_eq_sum_range_of_const AS PhiS hASsubst hAS0 j]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mem_range] at hs
        -- e([PhiS]_s * [AS^s]_j) = [Phi]_s * [(map AS)^s]_j
        have h1 : e (coeff s PhiS * coeff j (AS ^ s)) = e (coeff s PhiS) * e (coeff j (AS ^ s)) :=
            map_mul e _ _
        have h2 : e (coeff s PhiS) = coeff s Phi := by
          rw [← coeff_map, hmapPhi]
        have h3 : e (coeff j (AS ^ s)) = coeff j ((PowerSeries.map e AS) ^ s) := by
          rw [← coeff_map, map_pow]
        rw [h1, h2, h3]
    have h1c : constantCoeff (PowerSeries.map e AS) = 0 := by
      have h1 : constantCoeff (PowerSeries.map e AS) = e (constantCoeff AS) := by
        rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
      rw [h1, hAS0, map_zero]
    exact eq_of_fixed_point Phi (PowerSeries.map e AS) A hmsubst hsubst h1c hA0 hmfix hfix
  -- apply e to universal identity
  have hcongr := congrArg e huni
  simp only [map_mul, map_natCast] at hcongr
  rw [← coeff_map e n (AS ^ k), ← coeff_map e (n - k) (PhiS ^ n),
    map_pow (PowerSeries.map e) AS k, map_pow (PowerSeries.map e) PhiS n,
    hmap, hmapPhi] at hcongr
  exact hcongr

section
/-- **Lagrange–Bürmann formula from the fixed-point equation alone.** Let $R$ be a commutative
ring and let $A$, $\varphi$ and $g$ be formal power series over $R$ with $A = X\,\varphi(A)$,
where $\varphi(A)$ and $g(A)$ denote the substitution of $A$ into $\varphi$ and $g$. Write
$[X^m]H$ for the coefficient of $X^m$ in a power series $H$ and $g'$ for the formal derivative
of $g$. Then for every natural number $n \ge 1$,

$$n\, [X^n]\, g(A) = [X^{n-1}]\left(g' \varphi^n\right).$$

No condition on the constant term of $\varphi$ is needed. -/
theorem fps_lagrange_burmann_coeff' {R : Type*} [CommRing R] (A phi g : PowerSeries R)
    (hfix : A = PowerSeries.X * PowerSeries.subst A phi) (n : ℕ) (hn : 0 < n) :
    (n : R) * PowerSeries.coeff n (PowerSeries.subst A g) =
      PowerSeries.coeff (n - 1) (PowerSeries.derivative g * phi ^ n) := by
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    rw [hfix, map_mul, constantCoeff_X, zero_mul]
  have hsubst : HasSubst A := HasSubst.of_constantCoeff_zero' hA0
  have hmono : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      (n : R) * coeff n (A ^ k) =
        coeff (n - 1) (derivative (X ^ k : PowerSeries R) * phi ^ n) := by
    intro k hk1 hkn
    have htrans := mono_transport A phi hsubst hA0 hfix n k hk1 hkn
    have hconv := coeff_derivXk_mul phi k n (n - 1) hk1 hkn rfl
    rw [hconv]
    exact htrans
  exact reduction A phi g hsubst hfix n hn hmono

set_option linter.unusedVariables false in
/-- **Lagrange–Bürmann formula, coefficient form.** Let $R$ be a commutative ring and let $A$,
$\varphi$ and $g$ be formal power series over $R$ such that the constant term of $A$ is
nilpotent, $\varphi$ has nonzero constant term, and $A = X\,\varphi(A)$, where $\varphi(A)$ and
$g(A)$ denote the substitution of $A$ into $\varphi$ and $g$. Write $[X^m]H$ for the coefficient
of $X^m$ in a power series $H$ and $g'$ for the formal derivative of $g$. Then for every
natural number $n \ge 1$,

$$n\, [X^n]\, g(A) = [X^{n-1}]\left(g' \varphi^n\right).$$

This is the division-free form over a commutative ring: no division by $n$ is required.

Proves `Wanted` entry `fps_lagrange_burmann_coeff`.

Source: Alexander M. Haupt, "Enumeration of S-omino Towers and
Row-Convex k-omino Towers," JIS 24 (2021), proposition at lines 400–407,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Haupt/haupt4.tex, file SHA-256
`1b412146e9dba7d9302d274268baf3e35239b8369473faf57f086f918e3b66af`, span SHA-256
`ba6bf0dfa1cffa8a22bf10e4f7528c86dbe5ced596286dee93a765f5db3774cf`.
Corroborating power specialization: Dmitry Kruchinin and Vladimir Kruchinin,
"A Method for Obtaining Generating Functions for Central Coefficients of
Triangles," JIS 15 (2012), lines 199–210,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Kruchinin/kruchinin5.tex, file SHA-256
`abb875f7d7951467436cf43c9c7d0dd662fdfd05382952f542ad53b2ebfcea8f`, span SHA-256
`805d5ab3e7352b021e119fb2bec5cfd477f4a01469758b601fb7a9ea4c5f0d36`.
Source concept `jis_grounded_b2a0ba5cfa34a62aa3e66f0f`;
variants `formal_implicit_composition` and `formal_power_specialization`.
-/
theorem fps_lagrange_burmann_coeff {R : Type*} [CommRing R] (A phi g : PowerSeries R)
    (hsubst : PowerSeries.HasSubst A) (hphi : PowerSeries.coeff 0 phi ≠ 0)
    (hfix : A = PowerSeries.X * PowerSeries.subst A phi) (n : ℕ) (hn : 0 < n) :
    (n : R) * PowerSeries.coeff n (PowerSeries.subst A g) =
      PowerSeries.coeff (n - 1) (PowerSeries.derivative g * phi ^ n) :=
  fps_lagrange_burmann_coeff' A phi g hfix n hn
