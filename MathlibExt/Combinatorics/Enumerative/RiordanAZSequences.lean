/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Finset.Range

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution

@[expose] public section

namespace MetaMathlibExt

/-! # Riordan array A- and Z-sequence characterization

This file proves the coefficientwise A- and Z-sequence characterization of integer Riordan arrays.
-/

private theorem raz_eq_X_mul_shift {R : Type*} [CommRing R] (f : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff f = 0) :
    f = PowerSeries.X * PowerSeries.mk (fun n ↦ PowerSeries.coeff (n + 1) f) := by
  simpa [hf0] using PowerSeries.eq_X_mul_shift_add_const f

private theorem raz_coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R]
    (f : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0) {n k : ℕ} (hnk : n < k) :
    PowerSeries.coeff n (f ^ k) = 0 := by
  rw [raz_eq_X_mul_shift f hf0, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hnk]

private theorem raz_coeff_pow_self {R : Type*} [CommRing R] (f : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    PowerSeries.coeff n (f ^ n) = PowerSeries.coeff 1 f ^ n := by
  conv_lhs => rw [raz_eq_X_mul_shift f hf0, mul_pow]
  calc
    PowerSeries.coeff n
        (PowerSeries.X ^ n * PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n) =
        PowerSeries.coeff 0 (PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n) := by
      simpa using PowerSeries.coeff_X_pow_mul
        (PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n) n 0
    _ = PowerSeries.coeff 1 f ^ n := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
        PowerSeries.constantCoeff_mk]

private theorem raz_coeff_mul_pow_self {R : Type*} [CommRing R]
    (g f : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0) (n : ℕ) :
    PowerSeries.coeff n (g * f ^ n) =
      PowerSeries.constantCoeff g * PowerSeries.coeff 1 f ^ n := by
  have hpow : f ^ n = PowerSeries.X ^ n *
      PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n := by
    conv_lhs => rw [raz_eq_X_mul_shift f hf0, mul_pow]
  rw [hpow]
  calc
    PowerSeries.coeff n
        (g * (PowerSeries.X ^ n *
          PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n)) =
        PowerSeries.coeff n
          (PowerSeries.X ^ n *
            (g * PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n)) := by
      congr 1
      ring
    _ = PowerSeries.coeff 0
        (g * PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n) := by
      simpa using PowerSeries.coeff_X_pow_mul
        (g * PowerSeries.mk (fun k ↦ PowerSeries.coeff (k + 1) f) ^ n) n 0
    _ = PowerSeries.constantCoeff g * PowerSeries.coeff 1 f ^ n := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
        PowerSeries.constantCoeff_mk]

private theorem raz_coeff_mul_pow_eq_zero_of_lt {R : Type*} [CommRing R]
    (g f : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0)
    {n k : ℕ} (hnk : n < k) : PowerSeries.coeff n (g * f ^ k) = 0 := by
  have hpow : f ^ k = PowerSeries.X ^ k *
      PowerSeries.mk (fun m ↦ PowerSeries.coeff (m + 1) f) ^ k := by
    conv_lhs => rw [raz_eq_X_mul_shift f hf0, mul_pow]
  rw [hpow]
  calc
    PowerSeries.coeff n
        (g * (PowerSeries.X ^ k *
          PowerSeries.mk (fun m ↦ PowerSeries.coeff (m + 1) f) ^ k)) =
        PowerSeries.coeff n
          (PowerSeries.X ^ k *
            (g * PowerSeries.mk (fun m ↦ PowerSeries.coeff (m + 1) f) ^ k)) := by
      congr 1
      ring
    _ = 0 := by
      rw [PowerSeries.coeff_X_pow_mul']
      simp [Nat.not_le.mpr hnk]

private noncomputable def raz_triangularCoeff (a : ℕ → ℚ) (b : ℕ → ℕ → ℚ)
    (n : ℕ) : ℚ :=
  Nat.strongRec (motive := fun _ ↦ ℚ) (fun n ih ↦
    (a n - ∑ j ∈ Finset.range n, (if h : j < n then ih j h else 0) * b n j) / b n n) n

private theorem raz_triangularCoeff_eq (a : ℕ → ℚ) (b : ℕ → ℕ → ℚ) (n : ℕ) :
    raz_triangularCoeff a b n =
      (a n - ∑ j ∈ Finset.range n, raz_triangularCoeff a b j * b n j) / b n n := by
  unfold raz_triangularCoeff
  rw [Nat.strongRec_eq]
  apply congrArg (fun s : ℚ ↦ (a n - s) / b n n)
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]

private theorem raz_triangularCoeff_spec (a : ℕ → ℚ) (b : ℕ → ℕ → ℚ)
    (hdiag : ∀ n, b n n ≠ 0) (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), raz_triangularCoeff a b j * b n j := by
  rw [Finset.sum_range_succ, raz_triangularCoeff_eq,
    div_mul_cancel₀ _ (hdiag n)]
  ring

private theorem raz_coeff_subst_mk (f : PowerSeries ℚ)
    (hf0 : PowerSeries.constantCoeff f = 0) (a : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.mk a).subst f) =
      ∑ j ∈ Finset.range (n + 1), a j * PowerSeries.coeff n (f ^ j) := by
  have hf : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hs : Function.support (fun j : ℕ ↦
      PowerSeries.coeff j (PowerSeries.mk a) • PowerSeries.coeff n (f ^ j)) ⊆
      (Finset.range (n + 1) : Set ℕ) := by
    intro j hj
    change PowerSeries.coeff j (PowerSeries.mk a) • PowerSeries.coeff n (f ^ j) ≠ 0 at hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    have hnj : n < j := by omega
    exact hj (by simp [raz_coeff_pow_eq_zero_of_lt f hf0 hnj])
  rw [PowerSeries.coeff_subst' hf,
    finsum_eq_sum_of_support_subset _ hs]
  simp only [PowerSeries.coeff_mk, smul_eq_mul]

private theorem raz_coeff_mul_subst_mk (f p : PowerSeries ℚ)
    (hf0 : PowerSeries.constantCoeff f = 0) (a : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (p * (PowerSeries.mk a).subst f) =
      ∑ j ∈ Finset.range (n + 1), a j * PowerSeries.coeff n (p * f ^ j) := by
  rw [PowerSeries.coeff_mul]
  simp_rw [raz_coeff_subst_mk f hf0 a]
  calc
    (∑ q ∈ Finset.antidiagonal n, PowerSeries.coeff q.1 p *
        ∑ j ∈ Finset.range (q.2 + 1), a j * PowerSeries.coeff q.2 (f ^ j)) =
        ∑ q ∈ Finset.antidiagonal n, ∑ j ∈ Finset.range (n + 1),
          PowerSeries.coeff q.1 p * (a j * PowerSeries.coeff q.2 (f ^ j)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        have hqsum := Finset.mem_antidiagonal.mp hq
        omega
      · intro j hjn hjq
        simp only [Finset.mem_range] at hjn hjq
        rw [raz_coeff_pow_eq_zero_of_lt f hf0 (by omega)]
        simp
    _ = ∑ j ∈ Finset.range (n + 1), ∑ q ∈ Finset.antidiagonal n,
        PowerSeries.coeff q.1 p * (a j * PowerSeries.coeff q.2 (f ^ j)) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range (n + 1), a j * PowerSeries.coeff n (p * f ^ j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PowerSeries.coeff_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

private theorem raz_exists_A (f : PowerSeries ℚ)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0) :
    ∃ A : ℕ → ℚ, A 0 ≠ 0 ∧ ∀ n : ℕ,
      PowerSeries.coeff (n + 1) f =
        ∑ j ∈ Finset.range (n + 1), A j * PowerSeries.coeff n (f ^ j) := by
  let A := raz_triangularCoeff (fun n ↦ PowerSeries.coeff (n + 1) f)
    (fun n j ↦ PowerSeries.coeff n (f ^ j))
  have hdiag : ∀ n, PowerSeries.coeff n (f ^ n) ≠ 0 := by
    intro n
    rw [raz_coeff_pow_self f hf0]
    exact pow_ne_zero n hf1
  refine ⟨A, ?_, ?_⟩
  · have hA0 : PowerSeries.coeff 1 f = A 0 := by
      change PowerSeries.coeff 1 f =
        raz_triangularCoeff (fun n ↦ PowerSeries.coeff (n + 1) f)
          (fun n j ↦ PowerSeries.coeff n (f ^ j)) 0
      simpa using (raz_triangularCoeff_spec
        (fun n ↦ PowerSeries.coeff (n + 1) f)
        (fun n j ↦ PowerSeries.coeff n (f ^ j)) hdiag 0)
    exact fun h ↦ hf1 (hA0.trans h)
  · exact raz_triangularCoeff_spec _ _ hdiag

private theorem raz_A_recurrence (g f : PowerSeries ℚ)
    (hf0 : PowerSeries.constantCoeff f = 0) (A : ℕ → ℚ)
    (hA : ∀ n : ℕ, PowerSeries.coeff (n + 1) f =
      ∑ j ∈ Finset.range (n + 1), A j * PowerSeries.coeff n (f ^ j))
    (n k : ℕ) :
    PowerSeries.coeff (n + 1) (g * f ^ (k + 1)) =
      ∑ j ∈ Finset.range (n + 1), A j * PowerSeries.coeff n (g * f ^ (k + j)) := by
  have hfA : f = PowerSeries.X * (PowerSeries.mk A).subst f := by
    apply PowerSeries.ext
    intro m
    cases m with
    | zero =>
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf0]
    | succ m =>
        rw [PowerSeries.coeff_succ_X_mul, raz_coeff_subst_mk f hf0 A]
        exact hA m
  calc
    PowerSeries.coeff (n + 1) (g * f ^ (k + 1)) =
        PowerSeries.coeff (n + 1) ((g * f ^ k) * f) := by
      rw [pow_succ, mul_assoc]
    _ = PowerSeries.coeff (n + 1)
        ((g * f ^ k) * (PowerSeries.X * (PowerSeries.mk A).subst f)) :=
      congrArg (fun q ↦ PowerSeries.coeff (n + 1) ((g * f ^ k) * q)) hfA
    _ =
        PowerSeries.coeff (n + 1)
          (PowerSeries.X * ((g * f ^ k) * (PowerSeries.mk A).subst f)) := by
      congr 1
      ring
    _ = PowerSeries.coeff n ((g * f ^ k) * (PowerSeries.mk A).subst f) := by
      rw [PowerSeries.coeff_succ_X_mul]
    _ = ∑ j ∈ Finset.range (n + 1),
        A j * PowerSeries.coeff n ((g * f ^ k) * f ^ j) :=
      raz_coeff_mul_subst_mk f (g * f ^ k) hf0 A n
    _ = ∑ j ∈ Finset.range (n + 1),
        A j * PowerSeries.coeff n (g * f ^ (k + j)) := by
      simp only [pow_add, mul_assoc]

private theorem raz_exists_Z (g f : PowerSeries ℚ)
    (hg0 : PowerSeries.constantCoeff g = 1)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0) :
    ∃ Z : ℕ → ℚ, ∀ n : ℕ,
      PowerSeries.coeff (n + 1) g =
        ∑ j ∈ Finset.range (n + 1), Z j * PowerSeries.coeff n (g * f ^ j) := by
  let Z := raz_triangularCoeff (fun n ↦ PowerSeries.coeff (n + 1) g)
    (fun n j ↦ PowerSeries.coeff n (g * f ^ j))
  have hdiag : ∀ n, PowerSeries.coeff n (g * f ^ n) ≠ 0 := by
    intro n
    rw [raz_coeff_mul_pow_self g f hf0, hg0, one_mul]
    exact pow_ne_zero n hf1
  exact ⟨Z, raz_triangularCoeff_spec _ _ hdiag⟩

private theorem raz_forward_rat (g f : PowerSeries ℚ)
    (hg0 : PowerSeries.constantCoeff g = 1)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0) :
    ∃ A Z : ℕ → ℚ, A 0 ≠ 0 ∧
      (∀ n k : ℕ, PowerSeries.coeff (n + 1) (g * f ^ (k + 1)) =
        ∑ j ∈ Finset.range (n + 1), A j *
          PowerSeries.coeff n (g * f ^ (k + j))) ∧
      (∀ n : ℕ, PowerSeries.coeff (n + 1) g =
        ∑ j ∈ Finset.range (n + 1), Z j * PowerSeries.coeff n (g * f ^ j)) := by
  obtain ⟨A, hA0, hA⟩ := raz_exists_A f hf0 hf1
  obtain ⟨Z, hZ⟩ := raz_exists_Z g f hg0 hf0 hf1
  exact ⟨A, Z, hA0, raz_A_recurrence g f hf0 A hA, hZ⟩

private theorem raz_forward_int (d : ℕ → ℕ → ℤ) (g f : PowerSeries ℤ)
    (hg0 : PowerSeries.constantCoeff g = 1)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : ∀ n k : ℕ, d n k = PowerSeries.coeff n (g * f ^ k)) :
    ∃ A Z : ℕ → ℚ, A 0 ≠ 0 ∧ d 0 0 = 1 ∧
      (∀ n k : ℕ, (d (n + 1) (k + 1) : ℚ) =
        ∑ j ∈ Finset.range (n + 1), A j * d n (k + j)) ∧
      (∀ n : ℕ, (d (n + 1) 0 : ℚ) =
        ∑ j ∈ Finset.range (n + 1), Z j * d n j) := by
  let gq := PowerSeries.map (Int.castRingHom ℚ) g
  let fq := PowerSeries.map (Int.castRingHom ℚ) f
  have hg0q : PowerSeries.constantCoeff gq = 1 := by
    change ((PowerSeries.constantCoeff g : ℤ) : ℚ) = 1
    exact_mod_cast hg0
  have hf0q : PowerSeries.constantCoeff fq = 0 := by
    change ((PowerSeries.constantCoeff f : ℤ) : ℚ) = 0
    exact_mod_cast hf0
  have hf1q : PowerSeries.coeff 1 fq ≠ 0 := by
    change ((PowerSeries.coeff 1 f : ℤ) : ℚ) ≠ 0
    exact_mod_cast hf1
  have hdq : ∀ n k : ℕ, (d n k : ℚ) = PowerSeries.coeff n (gq * fq ^ k) := by
    intro n k
    rw [hd]
    calc
      ((PowerSeries.coeff n (g * f ^ k) : ℤ) : ℚ) =
          PowerSeries.coeff n (PowerSeries.map (Int.castRingHom ℚ) (g * f ^ k)) :=
        (PowerSeries.coeff_map (Int.castRingHom ℚ) n (g * f ^ k)).symm
      _ = PowerSeries.coeff n (gq * fq ^ k) := by
        congr 1
        simp [gq, fq]
  obtain ⟨A, Z, hA0, hA, hZ⟩ := raz_forward_rat gq fq hg0q hf0q hf1q
  refine ⟨A, Z, hA0, ?_, ?_, ?_⟩
  · rw [hd, pow_zero, mul_one, PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]
  · intro n k
    simpa only [hdq] using hA n k
  · intro n
    simpa [hdq] using hZ n

private theorem raz_diagonal (d : ℕ → ℕ → ℤ)
    (htri : ∀ n k : ℕ, n < k → d n k = 0) (A : ℕ → ℚ)
    (hd00 : d 0 0 = 1)
    (hA : ∀ n k : ℕ, (d (n + 1) (k + 1) : ℚ) =
      ∑ j ∈ Finset.range (n + 1), A j * d n (k + j)) :
    ∀ n : ℕ, (d n n : ℚ) = A 0 ^ n := by
  intro n
  induction n with
  | zero => simp [hd00]
  | succ n ih =>
      rw [hA n n, Finset.sum_eq_single 0]
      · simp [ih, pow_succ]
        ring
      · intro j hj hj0
        have hdj : d n (n + j) = 0 := htri n (n + j) (by omega)
        simp [hdj]
      · simp

private theorem raz_construct_pair (d : ℕ → ℕ → ℤ)
    (htri : ∀ n k : ℕ, n < k → d n k = 0) (A : ℕ → ℚ) (hA0 : A 0 ≠ 0)
    (hd00 : d 0 0 = 1)
    (hA : ∀ n k : ℕ, (d (n + 1) (k + 1) : ℚ) =
      ∑ j ∈ Finset.range (n + 1), A j * d n (k + j)) :
    ∃ g f : PowerSeries ℤ, PowerSeries.constantCoeff g = 1 ∧
      PowerSeries.constantCoeff f = 0 ∧ PowerSeries.coeff 1 f ≠ 0 ∧
      (∀ n : ℕ, d n 0 = PowerSeries.coeff n (g * f ^ 0)) ∧
      (∀ n : ℕ, d n 1 = PowerSeries.coeff n (g * f ^ 1)) := by
  let g : PowerSeries ℤ := PowerSeries.mk (fun n ↦ d n 0)
  let h : PowerSeries ℤ := PowerSeries.mk (fun n ↦ d n 1)
  let gi : PowerSeries ℤ := PowerSeries.invOfUnit g (1 : ℤˣ)
  let f : PowerSeries ℤ := h * gi
  have hg0 : PowerSeries.constantCoeff g = 1 := by
    simp [g, hd00]
  have hginv : g * gi = 1 := by
    dsimp [gi]
    apply PowerSeries.mul_invOfUnit
    simpa using hg0
  have hgf : g * f = h := by
    calc
      g * f = g * (h * gi) := by rfl
      _ = h * (g * gi) := by ring
      _ = h := by rw [hginv, mul_one]
  have hd01 : d 0 1 = 0 := htri 0 1 (by omega)
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simp [f, h, gi, hd01]
  have hf1eq : PowerSeries.coeff 1 f = d 1 1 := by
    have hc := congrArg (PowerSeries.coeff (R := ℤ) 1) hgf
    simpa [PowerSeries.coeff_one_mul, hf0, hg0, h] using hc
  have hd11q : (d 1 1 : ℚ) = A 0 := by
    simpa [hd00] using hA 0 0
  have hd11 : d 1 1 ≠ 0 := by
    intro hd
    apply hA0
    rw [← hd11q, hd]
    norm_num
  refine ⟨g, f, hg0, hf0, ?_, ?_, ?_⟩
  · exact fun hf ↦ hd11 (hf1eq ▸ hf)
  · intro n
    simp [g]
  · intro n
    simp [hgf, h]

private theorem raz_recurrence_unique (d r : ℕ → ℕ → ℚ)
    (htriD : ∀ n k : ℕ, n < k → d n k = 0)
    (htriR : ∀ n k : ℕ, n < k → r n k = 0)
    (hdiag : ∀ n : ℕ, d n n ≠ 0)
    (hcol0 : ∀ n : ℕ, d n 0 = r n 0) (hcol1 : ∀ n : ℕ, d n 1 = r n 1)
    (A B : ℕ → ℚ)
    (hD : ∀ n k : ℕ, d (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), A j * d n (k + j))
    (hR : ∀ n k : ℕ, r (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), B j * r n (k + j)) :
    d = r := by
  have hind : ∀ n : ℕ, (∀ k : ℕ, d n k = r n k) ∧
      (∀ j < n, A j = B j) := by
    intro n
    induction n with
    | zero =>
        constructor
        · intro k
          cases k with
          | zero => exact hcol0 0
          | succ k => rw [htriD 0 (k + 1) (by omega), htriR 0 (k + 1) (by omega)]
        · intro j hj
          omega
    | succ n ih =>
        rcases ih with ⟨hrow, hseq⟩
        have hsum :
            (∑ j ∈ Finset.range (n + 1), A j * d n j) =
              ∑ j ∈ Finset.range (n + 1), B j * r n j := by
          calc
            (∑ j ∈ Finset.range (n + 1), A j * d n j) = d (n + 1) 1 :=
              by simpa only [Nat.zero_add] using (hD n 0).symm
            _ = r (n + 1) 1 := hcol1 (n + 1)
            _ = ∑ j ∈ Finset.range (n + 1), B j * r n j := by
              simpa only [Nat.zero_add] using hR n 0
        have hprefix :
            (∑ j ∈ Finset.range n, A j * d n j) =
              ∑ j ∈ Finset.range n, B j * r n j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hseq j (Finset.mem_range.mp hj), hrow j]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, hprefix, ← hrow n] at hsum
        have hAn : A n = B n :=
          mul_right_cancel₀ (hdiag n) (add_left_cancel hsum)
        have hAB : ∀ j ∈ Finset.range (n + 1), A j = B j := by
          intro j hj
          by_cases hjn : j = n
          · simpa [hjn] using hAn
          · exact hseq j (by
              simp only [Finset.mem_range] at hj
              omega)
        constructor
        · intro k
          cases k with
          | zero => exact hcol0 (n + 1)
          | succ k =>
              calc
                d (n + 1) (k + 1) =
                    ∑ j ∈ Finset.range (n + 1), A j * d n (k + j) := hD n k
                _ = ∑ j ∈ Finset.range (n + 1), B j * r n (k + j) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hAB j hj, hrow (k + j)]
                _ = r (n + 1) (k + 1) := (hR n k).symm
        · intro j hj
          by_cases hjn : j = n
          · simpa [hjn] using hAn
          · exact hseq j (by omega)
  funext n k
  exact (hind n).1 k

private theorem raz_backward_int (d : ℕ → ℕ → ℤ)
    (htri : ∀ n k : ℕ, n < k → d n k = 0) (A : ℕ → ℚ) (hA0 : A 0 ≠ 0)
    (hd00 : d 0 0 = 1)
    (hA : ∀ n k : ℕ, (d (n + 1) (k + 1) : ℚ) =
      ∑ j ∈ Finset.range (n + 1), A j * d n (k + j)) :
    ∃ g f : PowerSeries ℤ, PowerSeries.constantCoeff g = 1 ∧
      PowerSeries.constantCoeff f = 0 ∧ PowerSeries.coeff 1 f ≠ 0 ∧
      ∀ n k : ℕ, d n k = PowerSeries.coeff n (g * f ^ k) := by
  obtain ⟨g, f, hg0, hf0, hf1, hcol0, hcol1⟩ :=
    raz_construct_pair d htri A hA0 hd00 hA
  let r : ℕ → ℕ → ℤ := fun n k ↦ PowerSeries.coeff n (g * f ^ k)
  obtain ⟨B, _, hB0, _, hR, _⟩ :=
    raz_forward_int r g f hg0 hf0 hf1 (fun _ _ ↦ rfl)
  let dQ : ℕ → ℕ → ℚ := fun n k ↦ d n k
  let rQ : ℕ → ℕ → ℚ := fun n k ↦ r n k
  have htriD : ∀ n k : ℕ, n < k → dQ n k = 0 := by
    intro n k hnk
    simp [dQ, htri n k hnk]
  have htriR : ∀ n k : ℕ, n < k → rQ n k = 0 := by
    intro n k hnk
    change ((PowerSeries.coeff n (g * f ^ k) : ℤ) : ℚ) = 0
    rw [raz_coeff_mul_pow_eq_zero_of_lt g f hf0 hnk]
    norm_num
  have hdiag : ∀ n : ℕ, dQ n n ≠ 0 := by
    intro n
    change (d n n : ℚ) ≠ 0
    rw [raz_diagonal d htri A hd00 hA n]
    exact pow_ne_zero n hA0
  have hcol0Q : ∀ n : ℕ, dQ n 0 = rQ n 0 := by
    intro n
    change (d n 0 : ℚ) = (r n 0 : ℚ)
    exact_mod_cast hcol0 n
  have hcol1Q : ∀ n : ℕ, dQ n 1 = rQ n 1 := by
    intro n
    change (d n 1 : ℚ) = (r n 1 : ℚ)
    exact_mod_cast hcol1 n
  have hDQ : ∀ n k : ℕ, dQ (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), A j * dQ n (k + j) := by
    exact hA
  have hRQ : ∀ n k : ℕ, rQ (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), B j * rQ n (k + j) := by
    exact hR
  have heq : dQ = rQ :=
    raz_recurrence_unique dQ rQ htriD htriR hdiag hcol0Q hcol1Q A B hDQ hRQ
  refine ⟨g, f, hg0, hf0, hf1, ?_⟩
  intro n k
  have hq := congrFun (congrFun heq n) k
  change (d n k : ℚ) = (PowerSeries.coeff n (g * f ^ k) : ℤ) at hq
  exact_mod_cast hq

/--
**A- and Z-sequence characterization of integer Riordan arrays.** Let $(d_{n,k})_{n,k \ge 0}$ be
an integer matrix that is lower triangular, that is, $d_{n,k} = 0$ whenever $n < k$. Then the
following are equivalent: (i) there are power series $g, f \in \mathbb{Z}[[x]]$ with $g(0) = 1$,
$f(0) = 0$ and $[x^1]\, f \ne 0$ such that $d_{n,k} = [x^n]\, g f^k$ for all $n, k \ge 0$;
(ii) $d_{0,0} = 1$ and there are rational sequences $(A_j)_{j \ge 0}$ and $(Z_j)_{j \ge 0}$ with
$A_0 \ne 0$ such that, for all $n, k \ge 0$,
$$d_{n+1,k+1} = \sum_{j=0}^{n} A_j\, d_{n,k+j} \quad\text{and}\quad
d_{n+1,0} = \sum_{j=0}^{n} Z_j\, d_{n,j}.$$

The sequences are rational because $A_0 = [x^1]\, f$ need not be a unit in $\mathbb{Z}$.

Correction to the cited source: Barry's Proposition displays the hypothesis $Z_0 \ne 0$, but the
identity Riordan array has $Z_0 = 0$, so that condition cannot hold in general. This statement
therefore drops $Z_0 \ne 0$ — a deliberate correction to the source, not just a normalization —
and instead imposes the Riordan normalization $d_{0,0} = 1$.

Proof: The forward implication uses coefficientwise triangular expansions in powers of $f$; the
converse reconstructs $g$ and $f$ from columns zero and one and proves rowwise uniqueness. This is
the route of Barry's Proposition Char following He and Sprugnoli's Theorems 2.1 and 2.2.

Proves `Wanted` entry `riordan_iff_AZ_sequences`.

Source: P. Barry, *A Note on a Family of Generalized Pascal Matrices Defined by
Riordan Arrays*, Journal of Integer Sequences 16 (2013), Article 13.5.4,
Proposition Char, lines 173-180,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.tex>, after Theorems 2.1
and 2.2 of He.
-/
public theorem riordan_iff_AZ_sequences (d : ℕ → ℕ → ℤ)
    (htri : ∀ n k : ℕ, n < k → d n k = 0) :
    ((∃ g f : PowerSeries ℤ, PowerSeries.constantCoeff (R := ℤ) g = 1 ∧
      PowerSeries.constantCoeff (R := ℤ) f = 0 ∧
      PowerSeries.coeff (R := ℤ) 1 f ≠ 0 ∧
      ∀ n k : ℕ, d n k = PowerSeries.coeff (R := ℤ) n (g * f ^ k)) ↔
    (∃ A Z : ℕ → ℚ, A 0 ≠ 0 ∧ d 0 0 = 1 ∧
      (∀ n k : ℕ, (d (n + 1) (k + 1) : ℚ) = ∑ j ∈ Finset.range (n + 1), A j * d n (k + j)) ∧
      (∀ n : ℕ, (d (n + 1) 0 : ℚ) = ∑ j ∈ Finset.range (n + 1), Z j * d n j))) := by
  constructor
  · rintro ⟨g, f, hg0, hf0, hf1, hd⟩
    exact raz_forward_int d g f hg0 hf0 hf1 hd
  · rintro ⟨A, _, hA0, hd00, hA, _⟩
    exact raz_backward_int d htri A hA0 hd00 hA

end MetaMathlibExt
