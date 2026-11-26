/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import MathlibExt.Analysis.SpecialFunctions.AndrewsJacobiTripleProduct
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Fintype.Sets
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cui–Gu `p`-dissection of `f_1`

This module proves the Cui–Gu `p`-dissection of the Euler product `f_1`, expressing it as
a sum of Ramanujan theta values plus a multiple of `f_{p^2}`.

## Main statements

* `MetaMathlibExt.qPochhammer_prime_dissection`

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 5, eq. (8), quoting S. Cui and N. Gu,
*Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51 (2013), 507–523,
Theorem 2.2. The same identity is Nayaka, Dharmendra and Mahesh Kumar, *Divisibility
Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80, Lemma 4,
eq. (43).
-/

namespace MetaMathlibExt

@[expose] public section

private theorem two_dvd_pent (k : ℤ) : 2 ∣ k * (3 * k + 1) := by
  rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r * (3 * k + 1), by rw [hr]; ring⟩
  · exact ⟨k * (3 * r + 2), by rw [hr]; ring⟩

private theorem nonneg_pent (k : ℤ) : 0 ≤ k * (3 * k + 1) := by
  rcases lt_or_ge k 0 with hk | hk
  · have h1 : (3 : ℤ) * k + 1 ≤ 0 := by omega
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hk) h1
  · have h1 : 0 ≤ (3 : ℤ) * k + 1 := by linarith
    exact mul_nonneg hk h1

private theorem prime_mod_six (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h3 : ¬ 3 ∣ p := by
    intro hdvd
    have h := (hp.eq_one_or_self_of_dvd 3 hdvd).resolve_left (by omega)
    omega
  obtain ⟨m, hm⟩ := hodd
  have hmod2 : p % 2 = 1 := by omega
  have hmod3 : p % 3 ≠ 0 := fun h => h3 ((Nat.dvd_iff_mod_eq_zero).mpr h)
  omega

private theorem mem_Icc_s (p : ℕ) (hp5 : 5 ≤ p) (s : ℤ)
    (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) :
    s ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2) := by
  rw [Finset.mem_Icc]
  omega

private theorem six_s_eq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (s : ℤ)
    (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) :
    6 * s + 1 = (p : ℤ) ∨ 6 * s + 1 = -(p : ℤ) := by
  rcases prime_mod_six p hp hp5 with h1 | h5
  · left
    rw [hs]
    simp only [h1, ↓reduceIte]
    omega
  · right
    have hne : p % 6 ≠ 1 := by omega
    rw [hs]
    simp only [hne, ↓reduceIte]
    omega

private theorem nonneg_tri_succ (n : ℤ) : 0 ≤ n * (n + 1) := by
  rcases lt_or_ge n 0 with hn | hn
  · have h1 : n + 1 ≤ 0 := by omega
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hn) h1
  · have h1 : 0 ≤ n + 1 := by linarith
    exact mul_nonneg hn h1

private theorem nonneg_tri_pred (n : ℤ) : 0 ≤ n * (n - 1) := by
  rcases lt_or_ge n 1 with hn | hn
  · have hn0 : n ≤ 0 := by omega
    have h1 : n - 1 ≤ 0 := by omega
    exact mul_nonneg_of_nonpos_of_nonpos hn0 h1
  · have hn0 : 0 ≤ n := by omega
    have h1 : 0 ≤ n - 1 := by omega
    exact mul_nonneg hn0 h1

private theorem odd_prime_cast (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    Odd (p : ℤ) := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  exact (Int.odd_natCast p).mpr hodd

private theorem two_dvd_theta_add (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℤ) :
    2 ∣ 3 * (p : ℤ) ^ 2 + (6 * k + 1) * p := by
  have hpodd : Odd (p : ℤ) := odd_prime_cast p hp hp5
  have h3 : Odd (3 : ℤ) := ⟨1, by ring⟩
  have hpsq : Odd ((p : ℤ) ^ 2) := hpodd.pow
  have h3psq : Odd (3 * (p : ℤ) ^ 2) := h3.mul hpsq
  have h6k : Even ((6 : ℤ) * k) := ⟨3 * k, by ring⟩
  have h1 : Odd (1 : ℤ) := ⟨0, by ring⟩
  have h6k1 : Odd ((6 : ℤ) * k + 1) := h6k.add_odd h1
  have hprod : Odd (((6 : ℤ) * k + 1) * p) := h6k1.mul hpodd
  exact (h3psq.add_odd hprod).two_dvd

private theorem two_dvd_theta_sub (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℤ) :
    2 ∣ 3 * (p : ℤ) ^ 2 - (6 * k + 1) * p := by
  have hpodd : Odd (p : ℤ) := odd_prime_cast p hp hp5
  have h3 : Odd (3 : ℤ) := ⟨1, by ring⟩
  have hpsq : Odd ((p : ℤ) ^ 2) := hpodd.pow
  have h3psq : Odd (3 * (p : ℤ) ^ 2) := h3.mul hpsq
  have h6k : Even ((6 : ℤ) * k) := ⟨3 * k, by ring⟩
  have h1 : Odd (1 : ℤ) := ⟨0, by ring⟩
  have h6k1 : Odd ((6 : ℤ) * k + 1) := h6k.add_odd h1
  have hprod : Odd (((6 : ℤ) * k + 1) * p) := h6k1.mul hpodd
  exact (h3psq.sub_odd hprod).two_dvd

private theorem nonneg_theta_add (p : ℕ) (hp5 : 5 ≤ p) (k : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)) :
    0 ≤ 3 * (p : ℤ) ^ 2 + (6 * k + 1) * p := by
  have hP : 0 ≤ (p : ℤ) := by positivity
  have hfac : 3 * (p : ℤ) ^ 2 + (6 * k + 1) * p
      = (p : ℤ) * (3 * p + (6 * k + 1)) := by ring
  rw [hfac]
  apply mul_nonneg hP
  rw [Finset.mem_Icc] at hk
  omega

private theorem nonneg_theta_sub (p : ℕ) (hp5 : 5 ≤ p) (k : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)) :
    0 ≤ 3 * (p : ℤ) ^ 2 - (6 * k + 1) * p := by
  have hP : 0 ≤ (p : ℤ) := by positivity
  have hfac : 3 * (p : ℤ) ^ 2 - (6 * k + 1) * p
      = (p : ℤ) * (3 * p - (6 * k + 1)) := by ring
  rw [hfac]
  apply mul_nonneg hP
  rw [Finset.mem_Icc] at hk
  omega

private theorem pent_exp_int (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k n : ℤ) :
    ((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2
      = k * (3 * k + 1) / 2
        + (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2 * (n * (n + 1) / 2)
        + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2 * (n * (n - 1) / 2) := by
  have hEN : 2 * (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2)
      = ((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_pent _)
  have hEK : 2 * (k * (3 * k + 1) / 2) = k * (3 * k + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_pent _)
  have hEA : 2 * ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2)
      = 3 * (p : ℤ) ^ 2 + (6 * k + 1) * p := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_theta_add p hp hp5 k)
  have hEB : 2 * ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2)
      = 3 * (p : ℤ) ^ 2 - (6 * k + 1) * p := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_theta_sub p hp hp5 k)
  have hNA : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd
  have hNB : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.even_mul_pred_self n).two_dvd
  have h4 : 4 * (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2)
      = 4 * (k * (3 * k + 1) / 2
        + (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2 * (n * (n + 1) / 2)
        + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2 * (n * (n - 1) / 2)) := by
    calc 4 * (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2)
        = 2 * (2 * (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2)) := by ring
      _ = 2 * (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1)) := by rw [hEN]
      _ = 2 * (2 * (k * (3 * k + 1) / 2))
          + (2 * ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2))
            * (2 * (n * (n + 1) / 2))
          + (2 * ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2))
            * (2 * (n * (n - 1) / 2)) := by
            rw [hEK, hEA, hEB, hNA, hNB]
            ring
      _ = 4 * (k * (3 * k + 1) / 2
          + (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2 * (n * (n + 1) / 2)
          + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2 * (n * (n - 1) / 2)) := by ring
  omega

private theorem pent_exp_nat (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k n : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)) :
    (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2).toNat
      = (k * (3 * k + 1) / 2).toNat
        + ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat * (n * (n + 1) / 2).toNat
        + ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat * (n * (n - 1) / 2).toNat := by
  have hENnn : 0 ≤ ((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2 :=
    Int.ediv_nonneg (nonneg_pent _) (by omega)
  have hEKnn : 0 ≤ k * (3 * k + 1) / 2 :=
    Int.ediv_nonneg (nonneg_pent _) (by omega)
  have hEAnn : 0 ≤ (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_add p hp5 k hk) (by omega)
  have hEBnn : 0 ≤ (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_sub p hp5 k hk) (by omega)
  have hNAnn : 0 ≤ n * (n + 1) / 2 :=
    Int.ediv_nonneg (nonneg_tri_succ n) (by omega)
  have hNBnn : 0 ≤ n * (n - 1) / 2 :=
    Int.ediv_nonneg (nonneg_tri_pred n) (by omega)
  have hint := pent_exp_int p hp hp5 k n
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  rw [Int.toNat_of_nonneg hENnn, Int.toNat_of_nonneg hEKnn, Int.toNat_of_nonneg hEAnn,
    Int.toNat_of_nonneg hEBnn, Int.toNat_of_nonneg hNAnn, Int.toNat_of_nonneg hNBnn]
  exact hint

private theorem tri_sum_int (n : ℤ) :
    n * (n + 1) / 2 + n * (n - 1) / 2 = n * n := by
  have hNA : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd
  have hNB : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.even_mul_pred_self n).two_dvd
  have h2 : 2 * (n * (n + 1) / 2 + n * (n - 1) / 2) = 2 * (n * n) := by
    calc 2 * (n * (n + 1) / 2 + n * (n - 1) / 2)
        = 2 * (n * (n + 1) / 2) + 2 * (n * (n - 1) / 2) := by ring
      _ = n * (n + 1) + n * (n - 1) := by rw [hNA, hNB]
      _ = 2 * (n * n) := by ring
  omega

private theorem tri_sum_nat (n : ℤ) :
    (n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat = (n * n).toNat := by
  have hNAnn : 0 ≤ n * (n + 1) / 2 :=
    Int.ediv_nonneg (nonneg_tri_succ n) (by omega)
  have hNBnn : 0 ≤ n * (n - 1) / 2 :=
    Int.ediv_nonneg (nonneg_tri_pred n) (by omega)
  have hnn : 0 ≤ n * n := mul_self_nonneg n
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Int.toNat_of_nonneg hNAnn, Int.toNat_of_nonneg hNBnn,
    Int.toNat_of_nonneg hnn]
  exact tri_sum_int n

private theorem neg_one_odd_mul (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (n : ℤ) :
    (-1 : ℂ) ^ ((p : ℤ) * n) = (-1 : ℂ) ^ n := by
  have hpodd : Odd (p : ℤ) := odd_prime_cast p hp hp5
  obtain ⟨t, ht⟩ := hpodd
  have hne : (-1 : ℂ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hsplit : (p : ℤ) * n = 2 * t * n + n := by
    calc (p : ℤ) * n = (2 * t + 1) * n := by rw [ht]
      _ = 2 * t * n + n := by ring
  rw [hsplit, zpow_add₀ hne]
  have heven : Even (2 * t * n) := ⟨t * n, by ring⟩
  rw [heven.neg_one_zpow, one_mul]

private theorem neg_one_sq_eq (n : ℤ) : (-1 : ℂ) ^ (n * n) = (-1 : ℂ) ^ n := by
  have hne : (-1 : ℂ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have heven : Even (n * n - n) := by
    have h : n * n - n = n * (n - 1) := by ring
    rw [h]
    exact Int.even_mul_pred_self n
  have hsplit : n * n = n + (n * n - n) := by omega
  rw [hsplit, zpow_add₀ hne, heven.neg_one_zpow, mul_one]

private theorem fiber_term_eq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k n : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)) (q : ℂ) :
    (-1 : ℂ) ^ ((p : ℤ) * n + k)
        * q ^ (((p : ℤ) * n + k) * (3 * ((p : ℤ) * n + k) + 1) / 2).toNat
      = (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat
        * ramanujanThetaTerm (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
          (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) n := by
  have hne : (-1 : ℂ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hexp := pent_exp_nat p hp hp5 k n hk
  have htri := tri_sum_nat n
  have hsign1 := neg_one_odd_mul p hp hp5 n
  have hsign2 := neg_one_sq_eq n
  have hnn : 0 ≤ n * n := mul_self_nonneg n
  have hsignNat : ((-1 : ℂ) ^ ((n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat))
      = (-1 : ℂ) ^ n := by
    rw [htri]
    rw [← zpow_natCast]
    rw [Int.toNat_of_nonneg hnn]
    exact hsign2
  have hsign : (-1 : ℂ) ^ ((p : ℤ) * n + k)
      = (-1 : ℂ) ^ k * (-1 : ℂ) ^ ((n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat) := by
    rw [zpow_add₀ hne, hsign1, ← hsignNat, mul_comm]
  unfold ramanujanThetaTerm
  have hneg1 : (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat : ℂ)
      = (-1) * q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat := by ring
  have hneg2 : (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat : ℂ)
      = (-1) * q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat := by ring
  rw [hneg1, hneg2, mul_pow, mul_pow]
  rw [← pow_mul, ← pow_mul]
  rw [hsign, hexp]
  simp only [pow_add]
  ring

private theorem andrews_pent_exp_eq (n : ℤ) :
    3 * n * (n + 1) / 2 - n = n * (3 * n + 1) / 2 := by
  have h1 : 2 ∣ 3 * n * (n + 1) := by
    have hev : Even (n * (n + 1)) := Int.even_mul_succ_self n
    have h3 : 3 * n * (n + 1) = 3 * (n * (n + 1)) := by ring
    rw [h3]
    exact Even.two_dvd (hev.mul_left 3)
  have h2 : 2 ∣ n * (3 * n + 1) := two_dvd_pent n
  have e1 : 2 * (3 * n * (n + 1) / 2) = 3 * n * (n + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel h1
  have e2 : 2 * (n * (3 * n + 1) / 2) = n * (3 * n + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel h2
  have h2eq : 2 * (3 * n * (n + 1) / 2 - n) = 2 * (n * (3 * n + 1) / 2) := by
    calc 2 * (3 * n * (n + 1) / 2 - n)
        = 2 * (3 * n * (n + 1) / 2) - 2 * n := by ring
      _ = 3 * n * (n + 1) - 2 * n := by rw [e1]
      _ = n * (3 * n + 1) := by ring
      _ = 2 * (n * (3 * n + 1) / 2) := by rw [e2]
  omega

private theorem andrews_pent_term_eq (q : ℂ) (n : ℤ) :
    (-1 : ℂ) ^ n * q ^ ((2 * (1 : ℤ) + 1) * n * (n + 1) / 2 - (1 : ℤ) * n)
      = (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat := by
  congr 1
  have hexp : (2 * (1 : ℤ) + 1) * n * (n + 1) / 2 - (1 : ℤ) * n
      = n * (3 * n + 1) / 2 := by
    have h3 : (2 * (1 : ℤ) + 1) * n * (n + 1) = 3 * n * (n + 1) := by ring
    rw [h3]
    have h1n : (1 : ℤ) * n = n := by ring
    rw [h1n]
    exact andrews_pent_exp_eq n
  have hnn : 0 ≤ n * (3 * n + 1) / 2 :=
    Int.ediv_nonneg (nonneg_pent n) (by omega)
  rw [hexp]
  rw [← zpow_natCast]
  rw [Int.toNat_of_nonneg hnn]

private theorem pent_series_eq (q : ℂ) :
    (∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
      = ∑' n : ℤ, (-1 : ℂ) ^ n
        * q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * n * (n + 1) / 2 - ((1 : ℕ) : ℤ) * n) := by
  apply tsum_congr
  intro n
  simp only [Nat.cast_one]
  exact (andrews_pent_term_eq q n).symm

private def fin3_prod_equiv : (Σ _: Fin 3, ℕ) ≃ ℕ where
  toFun := fun p => 3 * p.2 + p.1.val
  invFun := fun m => ⟨⟨m % 3, by omega⟩, m / 3⟩
  left_inv := by
    rintro ⟨i, n⟩
    simp only
    have hi : i.val < 3 := i.isLt
    have hmod : (3 * n + i.val) % 3 = i.val := by omega
    have hdiv : (3 * n + i.val) / 3 = n := by omega
    simp [hmod, hdiv]
  right_inv := by
    intro m
    simp only
    omega

private theorem fiber_multipliable (q : ℂ) (hq : ‖q‖ < 1) (c : ℕ) :
    Multipliable (fun n : ℕ => (1 : ℂ) - q ^ (3 * n + c)) := by
  have hq3 : ‖q ^ 3‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq three_ne_zero
  have hgeom : Summable (fun n : ℕ => (q ^ 3) ^ n) :=
    summable_geometric_of_norm_lt_one hq3
  have hmul : Summable (fun n : ℕ => (-q ^ c) * (q ^ 3) ^ n) := hgeom.mul_left _
  have hmult : Multipliable (fun n : ℕ => 1 + (-q ^ c) * (q ^ 3) ^ n) :=
    Complex.multipliable_one_add_of_summable hmul
  apply hmult.congr
  intro n
  have hexp : (q : ℂ) ^ (3 * n + c) = q ^ c * (q ^ 3) ^ n := by
    rw [pow_add, pow_mul]
    ring
  rw [hexp]
  ring

private theorem andrews_prod_factor_eq (q : ℂ) (n : ℕ) :
    (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1)))
        * (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * ((n : ℕ) : ℤ) + ((1 : ℕ) : ℤ)))
        * (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1) - ((1 : ℕ) : ℤ)))
      = ((1 : ℂ) - q ^ (3 * n + 3)) * ((1 : ℂ) - q ^ (3 * n + 1))
        * ((1 : ℂ) - q ^ (3 * n + 2)) := by
  have e1 : (2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1) = ((3 * n + 3 : ℕ) : ℤ) := by
    push_cast
    ring
  have e2 : (2 * ((1 : ℕ) : ℤ) + 1) * ((n : ℕ) : ℤ) + ((1 : ℕ) : ℤ)
      = ((3 * n + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  have e3 : (2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1) - ((1 : ℕ) : ℤ)
      = ((3 * n + 2 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [e3, e1, e2, zpow_natCast, zpow_natCast, zpow_natCast]

private theorem qpoch_eq_tprod_succ (q : ℂ) :
    QPochhammer.qPochhammerInfRaw q q = ∏' m : ℕ, ((1 : ℂ) - q ^ (m + 1)) := by
  unfold QPochhammer.qPochhammerInfRaw
  apply tprod_congr
  intro n
  congr 1
  rw [pow_succ']

private theorem pent_theorem (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInfRaw q q
      = ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat := by
  have handrews := andrews_jacobi_triple_product q 1 1 (by omega) (by omega) hq
  have hseries := pent_series_eq q
  have hprod_norm : (∏' n : ℕ, (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1)))
        * (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * ((n : ℕ) : ℤ) + ((1 : ℕ) : ℤ)))
        * (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1) - ((1 : ℕ) : ℤ))))
      = ∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 1)) * ((1 : ℂ) - q ^ (3 * n + 2))
        * ((1 : ℂ) - q ^ (3 * n + 3)) := by
    apply tprod_congr
    intro n
    rw [andrews_prod_factor_eq]
    ring
  have hm0 := fiber_multipliable q hq 1
  have hm1 := fiber_multipliable q hq 2
  have hm2 := fiber_multipliable q hq 3
  have hsplit : (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 1)) * ((1 : ℂ) - q ^ (3 * n + 2))
        * ((1 : ℂ) - q ^ (3 * n + 3)))
      = (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 1)))
        * (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 2)))
        * (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 3))) := by
    have h01 := hm0.mul hm1
    rw [← Multipliable.tprod_mul hm0 hm1, ← Multipliable.tprod_mul h01 hm2]
  have hqhas : HasProd (fun m : ℕ => (1 : ℂ) - q ^ (m + 1))
      (QPochhammer.qPochhammerInfRaw q q) := by
    have h0 := QPochhammer.hasProd_qPochhammerInf q q hq
    apply h0.congr_fun
    intro m
    congr 1
    rw [pow_succ']
  have hHasProd : HasProd ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv)
      (QPochhammer.qPochhammerInfRaw q q) :=
    (fin3_prod_equiv.hasProd_iff).mpr hqhas
  have hfib : ∀ i : Fin 3, HasProd (fun n : ℕ => ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1))
      ∘ fin3_prod_equiv) ⟨i, n⟩)
      (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨i, n⟩) := by
    intro i
    apply Multipliable.hasProd
    have hm : Multipliable (fun n : ℕ => (1 : ℂ) - q ^ (3 * n + i.val + 1)) :=
      fiber_multipliable q hq (i.val + 1)
    apply hm.congr
    intro n
    rfl
  have hsigma := HasProd.sigma hHasProd hfib
  have htprod_eq := hsigma.tprod_eq
  rw [tprod_fintype] at htprod_eq
  rw [Fin.prod_univ_three] at htprod_eq
  have hmatch : (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨0, n⟩)
        * (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨1, n⟩)
        * (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨2, n⟩)
      = (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 1)))
        * (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 2)))
        * (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 3))) := rfl
  calc QPochhammer.qPochhammerInfRaw q q
      = (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨0, n⟩)
        * (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨1, n⟩)
        * (∏' n : ℕ, ((fun m : ℕ => (1 : ℂ) - q ^ (m + 1)) ∘ fin3_prod_equiv) ⟨2, n⟩) :=
        htprod_eq.symm
    _ = (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 1)))
        * (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 2)))
        * (∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 3))) := hmatch
    _ = ∏' n : ℕ, ((1 : ℂ) - q ^ (3 * n + 1)) * ((1 : ℂ) - q ^ (3 * n + 2))
        * ((1 : ℂ) - q ^ (3 * n + 3)) := hsplit.symm
    _ = (∏' n : ℕ, (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1)))
        * (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * ((n : ℕ) : ℤ) + ((1 : ℕ) : ℤ)))
        * (1 - q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * (((n : ℕ) : ℤ) + 1) - ((1 : ℕ) : ℤ)))) :=
        hprod_norm.symm
    _ = ∑' n : ℤ, (-1 : ℂ) ^ n
        * q ^ ((2 * ((1 : ℕ) : ℤ) + 1) * n * (n + 1) / 2 - ((1 : ℕ) : ℤ) * n) :=
        handrews.symm
    _ = ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat := hseries.symm

private def residue_rep (p : ℕ) (n : ℤ) : ℤ :=
  let r := n % (p : ℤ)
  let b := ((p : ℤ) - 1) / 2
  if r ≤ b then r else r - (p : ℤ)

private theorem residue_rep_mem (p : ℕ) (hp5 : 5 ≤ p) (n : ℤ) :
    residue_rep p n ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2) := by
  have hPpos : (0 : ℤ) < (p : ℤ) := by
    have h5 : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
    omega
  have hPne : (p : ℤ) ≠ 0 := ne_of_gt hPpos
  have hr0 : 0 ≤ n % (p : ℤ) := Int.emod_nonneg n hPne
  have hrP : n % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos n hPpos
  unfold residue_rep
  simp only
  split
  · rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_Icc]
    omega

private theorem residue_rep_dvd (p : ℕ) (n : ℤ) :
    (p : ℤ) ∣ (n - residue_rep p n) := by
  have hn : (p : ℤ) * (n / (p : ℤ)) + n % (p : ℤ) = n :=
    Int.mul_ediv_add_emod n (p : ℤ)
  unfold residue_rep
  simp only
  split
  · exact ⟨n / (p : ℤ), by linear_combination -hn⟩
  · exact ⟨n / (p : ℤ) + 1, by linear_combination -hn⟩

private theorem residue_rep_of_mem (p : ℕ) (hp5 : 5 ≤ p) (k m : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)) :
    residue_rep p ((p : ℤ) * m + k) = k := by
  have hPpos : (0 : ℤ) < (p : ℤ) := by
    have h5 : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
    omega
  have hkIcc : (1 - (p : ℤ)) / 2 ≤ k ∧ k ≤ ((p : ℤ) - 1) / 2 := Finset.mem_Icc.mp hk
  have hmod : ((p : ℤ) * m + k) % (p : ℤ) = k % (p : ℤ) := by
    have h1 : (p : ℤ) * m + k = k + (p : ℤ) * m := by ring
    rw [h1]
    exact Int.add_mul_emod_self_left k (p : ℤ) m
  rcases lt_or_ge k 0 with hkneg | hk0
  · have hkPlow : -(p : ℤ) < k := by omega
    have hkp0 : 0 ≤ k + (p : ℤ) := by omega
    have hkpP : k + (p : ℤ) < (p : ℤ) := by omega
    have hkpmod : (k + (p : ℤ)) % (p : ℤ) = k + (p : ℤ) :=
      Int.emod_eq_of_lt hkp0 hkpP
    have hkeq : k % (p : ℤ) = k + (p : ℤ) := by
      have h1 : k + (p : ℤ) = k + (p : ℤ) * 1 := by ring
      have h2 : (k + (p : ℤ) * 1) % (p : ℤ) = k % (p : ℤ) :=
        Int.add_mul_emod_self_left k (p : ℤ) 1
      rw [h1] at hkpmod
      rw [hkpmod] at h2
      calc k % (p : ℤ) = k + (p : ℤ) * 1 := h2.symm
        _ = k + (p : ℤ) := by ring
    have hr : ((p : ℤ) * m + k) % (p : ℤ) = k + (p : ℤ) := by rw [hmod, hkeq]
    have hgt : ((p : ℤ) - 1) / 2 < k + (p : ℤ) := by omega
    unfold residue_rep
    simp only [hr]
    simp only [not_le_of_gt hgt, ↓reduceIte]
    ring
  · have hkP : k < (p : ℤ) := by omega
    have hkemod : k % (p : ℤ) = k := Int.emod_eq_of_lt hk0 hkP
    have hr : ((p : ℤ) * m + k) % (p : ℤ) = k := by rw [hmod, hkemod]
    unfold residue_rep
    simp only [hr, hkIcc.2, ↓reduceIte]

private def symm_equiv (p : ℕ) (hp5 : 5 ≤ p) :
    (Σ _: ↥(Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)), ℤ) ≃ ℤ where
  toFun := fun q => (p : ℤ) * q.2 + (q.1 : ℤ)
  invFun := fun n => ⟨⟨residue_rep p n, residue_rep_mem p hp5 n⟩,
    (n - residue_rep p n) / (p : ℤ)⟩
  left_inv := by
    rintro ⟨⟨k, hk⟩, m⟩
    simp only
    have hrep := residue_rep_of_mem p hp5 k m hk
    have hPne : (p : ℤ) ≠ 0 := by
      have h5 : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
      omega
    have hdiv : ((p : ℤ) * m + k - k) / (p : ℤ) = m := by
      have h1 : (p : ℤ) * m + k - k = m * (p : ℤ) := by ring
      rw [h1]
      exact Int.mul_ediv_cancel m hPne
    simp only [hrep, hdiv]
  right_inv := by
    intro n
    simp only
    have hPne : (p : ℤ) ≠ 0 := by
      have h5 : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
      omega
    obtain ⟨t, ht⟩ := residue_rep_dvd p n
    have hdiv : (n - residue_rep p n) / (p : ℤ) = t := by
      rw [ht]
      have h1 : (p : ℤ) * t = t * (p : ℤ) := by ring
      rw [h1]
      exact Int.mul_ediv_cancel t hPne
    rw [hdiv]
    linear_combination -ht

private theorem pent_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat) := by
  have handr := andrews_jacobi_triple_product_summable q 1 1 (by omega) hq
  apply handr.congr
  intro n
  simp only [Nat.cast_one]
  exact andrews_pent_term_eq q n

private theorem fiber_summable (p : ℕ) (hp5 : 5 ≤ p) (k : ℤ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m : ℤ => (-1 : ℂ) ^ ((p : ℤ) * m + k)
      * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat) := by
  have hPne : (p : ℤ) ≠ 0 := by
    have h5 : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
    omega
  have hsum := pent_summable q hq
  have hinj : Function.Injective (fun m : ℤ => (p : ℤ) * m + k) := by
    intro a b hab
    simp only at hab
    have h : (p : ℤ) * a = (p : ℤ) * b := by linear_combination hab
    have h2 : (p : ℤ) * (a - b) = 0 := by linear_combination h
    have h3 : a - b = 0 := by
      have := mul_eq_zero.mp h2
      rcases this with hP0 | hab0
      · exact absurd hP0 hPne
      · exact hab0
    omega
  exact hsum.comp_injective hinj

private theorem dissection_split (p : ℕ) (hp5 : 5 ≤ p) (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
      = ∑ k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2),
        ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
          * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat := by
  classical
  have hsum := pent_summable q hq
  have hHas : HasSum (fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
      (∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat) := hsum.hasSum
  have hHasSig : HasSum ((fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
      ∘ (symm_equiv p hp5))
      (∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat) :=
    ((symm_equiv p hp5).hasSum_iff).mpr hHas
  have hfib : ∀ k : ↥(Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)),
      HasSum (fun m : ℤ => ((fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
        ∘ (symm_equiv p hp5)) ⟨k, m⟩)
        (∑' m : ℤ, ((fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
          ∘ (symm_equiv p hp5)) ⟨k, m⟩) := by
    intro k
    apply Summable.hasSum
    have hs := fiber_summable p hp5 (k.val) q hq
    exact hs
  have hsigma := HasSum.sigma hHasSig hfib
  have htsum_eq := hsigma.tsum_eq
  rw [tsum_fintype] at htsum_eq
  have huniv : (Finset.univ : Finset ↥(Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)))
      = (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).attach :=
    Finset.univ_eq_attach _
  rw [huniv] at htsum_eq
  have hsum_eq : (∑ b ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).attach,
        ∑' m : ℤ, ((fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
          ∘ (symm_equiv p hp5)) ⟨b, m⟩)
      = ∑ k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2),
        ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
          * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat := by
    have hpoint : ∀ b : ↥(Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)),
        (∑' m : ℤ, ((fun n : ℤ => (-1 : ℂ) ^ n * q ^ (n * (3 * n + 1) / 2).toNat)
          ∘ (symm_equiv p hp5)) ⟨b, m⟩)
        = (fun k : ℤ => ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
          * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat) (b : ℤ) := by
      intro b
      rfl
    simp only [hpoint]
    exact Finset.sum_attach (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2))
      (fun k => ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
        * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat)
  rw [hsum_eq] at htsum_eq
  exact htsum_eq.symm

private theorem theta_exp_sum_int (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℤ) :
    (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2
      + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2 = 3 * (p : ℤ) ^ 2 := by
  have hEA : 2 * ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2)
      = 3 * (p : ℤ) ^ 2 + (6 * k + 1) * p := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_theta_add p hp hp5 k)
  have hEB : 2 * ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2)
      = 3 * (p : ℤ) ^ 2 - (6 * k + 1) * p := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_theta_sub p hp hp5 k)
  have h2 : 2 * ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2
      + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2) = 2 * (3 * (p : ℤ) ^ 2) := by
    calc 2 * ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2
          + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2)
        = 2 * ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2)
          + 2 * ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2) := by ring
      _ = (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p)
          + (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) := by rw [hEA, hEB]
      _ = 2 * (3 * (p : ℤ) ^ 2) := by ring
  omega

private theorem theta_summable (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2))
    (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (ramanujanThetaTerm
      (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
      (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat)) := by
  have hEAnn : 0 ≤ (3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_add p hp5 k hk) (by omega)
  have hEBnn : 0 ≤ (3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_sub p hp5 k hk) (by omega)
  have hsum := theta_exp_sum_int p hp hp5 k
  have hprod : (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
      * (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat)
      = q ^ (3 * p ^ 2) := by
    have hexp : ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat
          + ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat = 3 * p ^ 2 := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add, Int.toNat_of_nonneg hEAnn, Int.toNat_of_nonneg hEBnn]
      rw [hsum]
      push_cast
      ring
    calc (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
            * (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat)
        = q ^ (((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat
          + ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) := by
          have hneg : (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat : ℂ)
              * (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat)
              = q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat
              * q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat := by ring
          rw [hneg, ← pow_add]
      _ = q ^ (3 * p ^ 2) := by rw [hexp]
  have hnorm : ‖(-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
      * (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat)‖ < 1 := by
    rw [hprod, norm_pow]
    have hppos : 0 < p := by omega
    have hsq : 0 < p ^ 2 := pow_pos hppos 2
    have hpos : 0 < 3 * p ^ 2 := mul_pos (by omega) hsq
    have hne : 3 * p ^ 2 ≠ 0 := ne_of_gt hpos
    exact pow_lt_one₀ (norm_nonneg _) hq hne
  have hsumm := ramanujanTheta_summable _ _ hnorm
  exact Summable.of_norm hsumm

private theorem fiber_eq_theta (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℤ)
    (hk : k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2))
    (q : ℂ) (_hq : ‖q‖ < 1) :
    (∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
        * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat)
      = (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat
        * ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
          (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) := by
  have htsum : (∑' m : ℤ, (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat
        * ramanujanThetaTerm (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
          (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) m)
      = (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat
        * ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
          (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) := by
    rw [tsum_mul_left]
    rfl
  rw [← htsum]
  apply tsum_congr
  intro m
  exact fiber_term_eq p hp hp5 k m hk q

private theorem theta_pent_exp_int (n : ℤ) :
    2 * (n * (n + 1) / 2) + n * (n - 1) / 2 = n * (3 * n + 1) / 2 := by
  have hNA : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd
  have hNB : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (Int.even_mul_pred_self n).two_dvd
  have hE : 2 * (n * (3 * n + 1) / 2) = n * (3 * n + 1) := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel (two_dvd_pent n)
  have h2 : 2 * (2 * (n * (n + 1) / 2) + n * (n - 1) / 2)
      = 2 * (n * (3 * n + 1) / 2) := by
    calc 2 * (2 * (n * (n + 1) / 2) + n * (n - 1) / 2)
        = 2 * (2 * (n * (n + 1) / 2)) + 2 * (n * (n - 1) / 2) := by ring
      _ = 2 * (n * (n + 1)) + n * (n - 1) := by rw [hNA, hNB]
      _ = n * (3 * n + 1) := by ring
      _ = 2 * (n * (3 * n + 1) / 2) := by rw [hE]
  omega

private theorem theta_term_pent_eq (Q : ℂ) (n : ℤ) :
    ramanujanThetaTerm (-Q ^ 2) (-Q) n
      = (-1 : ℂ) ^ n * Q ^ (n * (3 * n + 1) / 2).toNat := by
  have hNAnn : 0 ≤ n * (n + 1) / 2 :=
    Int.ediv_nonneg (nonneg_tri_succ n) (by omega)
  have hNBnn : 0 ≤ n * (n - 1) / 2 :=
    Int.ediv_nonneg (nonneg_tri_pred n) (by omega)
  have hEnn : 0 ≤ n * (3 * n + 1) / 2 :=
    Int.ediv_nonneg (nonneg_pent n) (by omega)
  have hexpNat : 2 * (n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat
      = (n * (3 * n + 1) / 2).toNat := by
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    rw [Int.toNat_of_nonneg hNAnn, Int.toNat_of_nonneg hNBnn,
      Int.toNat_of_nonneg hEnn]
    exact theta_pent_exp_int n
  have htri := tri_sum_nat n
  have hsign2 := neg_one_sq_eq n
  have hnn : 0 ≤ n * n := mul_self_nonneg n
  have hsignNat : ((-1 : ℂ) ^ ((n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat))
      = (-1 : ℂ) ^ n := by
    rw [htri, ← zpow_natCast, Int.toNat_of_nonneg hnn]
    exact hsign2
  unfold ramanujanThetaTerm
  have hneg1 : ((-Q ^ 2 : ℂ)) = (-1) * Q ^ 2 := by ring
  have hneg2 : ((-Q : ℂ)) = (-1) * Q := by ring
  rw [hneg1, hneg2, mul_pow, mul_pow]
  have hpow1 : (Q ^ 2) ^ (n * (n + 1) / 2).toNat
      = Q ^ (2 * (n * (n + 1) / 2).toNat) := by
    rw [pow_mul]
  have hpow2 : Q ^ (n * (n - 1) / 2).toNat = Q ^ (n * (n - 1) / 2).toNat := rfl
  rw [hpow1]
  have hcombine : (-1 : ℂ) ^ (n * (n + 1) / 2).toNat * Q ^ (2 * (n * (n + 1) / 2).toNat)
        * ((-1 : ℂ) ^ (n * (n - 1) / 2).toNat * Q ^ (n * (n - 1) / 2).toNat)
      = ((-1 : ℂ) ^ ((n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat))
        * Q ^ (2 * (n * (n + 1) / 2).toNat + (n * (n - 1) / 2).toNat) := by
    rw [pow_add, pow_add]
    ring
  rw [hcombine, hsignNat, hexpNat]

private theorem theta_pent_eq (Q : ℂ) (hQ : ‖Q‖ < 1) :
    ramanujanThetaRaw (-Q ^ 2) (-Q) = QPochhammer.qPochhammerInfRaw Q Q := by
  have htsum : ramanujanThetaRaw (-Q ^ 2) (-Q)
      = ∑' n : ℤ, (-1 : ℂ) ^ n * Q ^ (n * (3 * n + 1) / 2).toNat := by
    unfold ramanujanThetaRaw
    apply tsum_congr
    intro n
    exact theta_term_pent_eq Q n
  rw [htsum]
  exact (pent_theorem Q hQ).symm

private theorem s_exp_pos (p : ℕ) (hp5 : 5 ≤ p) (s : ℤ)
    (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6)
    (h6 : 6 * s + 1 = (p : ℤ)) :
    ((3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2).toNat = 2 * p ^ 2
      ∧ ((3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2).toNat = p ^ 2 := by
  have hEAnn : 0 ≤ (3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_add p hp5 s (mem_Icc_s p hp5 s hs)) (by omega)
  have hEBnn : 0 ≤ (3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_sub p hp5 s (mem_Icc_s p hp5 s hs)) (by omega)
  have hEAint : (3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2 = 2 * (p : ℤ) ^ 2 := by
    have h1 : 3 * (p : ℤ) ^ 2 + (6 * s + 1) * p = 4 * (p : ℤ) ^ 2 := by
      linear_combination h6 * (p : ℤ)
    omega
  have hEBint : (3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2 = (p : ℤ) ^ 2 := by
    have h1 : 3 * (p : ℤ) ^ 2 - (6 * s + 1) * p = 2 * (p : ℤ) ^ 2 := by
      linear_combination -h6 * (p : ℤ)
    omega
  constructor
  · rw [hEAint]
    have hcast : (2 : ℤ) * (p : ℤ) ^ 2 = ((2 * p ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  · rw [hEBint]
    have hcast : (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]

private theorem s_exp_neg (p : ℕ) (hp5 : 5 ≤ p) (s : ℤ)
    (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6)
    (h6 : 6 * s + 1 = -(p : ℤ)) :
    ((3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2).toNat = p ^ 2
      ∧ ((3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2).toNat = 2 * p ^ 2 := by
  have hEAnn : 0 ≤ (3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_add p hp5 s (mem_Icc_s p hp5 s hs)) (by omega)
  have hEBnn : 0 ≤ (3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2 :=
    Int.ediv_nonneg (nonneg_theta_sub p hp5 s (mem_Icc_s p hp5 s hs)) (by omega)
  have hEAint : (3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2 = (p : ℤ) ^ 2 := by
    have h1 : 3 * (p : ℤ) ^ 2 + (6 * s + 1) * p = 2 * (p : ℤ) ^ 2 := by
      linear_combination h6 * (p : ℤ)
    omega
  have hEBint : (3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2 = 2 * (p : ℤ) ^ 2 := by
    have h1 : 3 * (p : ℤ) ^ 2 - (6 * s + 1) * p = 4 * (p : ℤ) ^ 2 := by
      linear_combination -h6 * (p : ℤ)
    omega
  constructor
  · rw [hEAint]
    have hcast : (p : ℤ) ^ 2 = ((p ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  · rw [hEBint]
    have hcast : (2 : ℤ) * (p : ℤ) ^ 2 = ((2 * p ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]

private theorem theta_s_eq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (s : ℤ)
    (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6)
    (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * s + 1) * p) / 2).toNat)
        (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * s + 1) * p) / 2).toNat)
      = QPochhammer.qPochhammerInfRaw (q ^ (p ^ 2)) (q ^ (p ^ 2)) := by
  have hQ : ‖q ^ (p ^ 2)‖ < 1 := by
    rw [norm_pow]
    have hppos0 : 0 < p := by omega
    have hppos : 0 < p ^ 2 := pow_pos hppos0 2
    have hne : p ^ 2 ≠ 0 := ne_of_gt hppos
    exact pow_lt_one₀ (norm_nonneg _) hq hne
  have hpow : (q ^ (p ^ 2)) ^ 2 = q ^ (2 * p ^ 2) := by
    rw [← pow_mul]
    congr 1
    ring
  have hmain := theta_pent_eq (q ^ (p ^ 2)) hQ
  rcases six_s_eq p hp hp5 s hs with h6 | h6
  · obtain ⟨hEA, hEB⟩ := s_exp_pos p hp5 s hs h6
    rw [hEA, hEB]
    have hsymm : ramanujanThetaRaw (-q ^ (2 * p ^ 2)) (-q ^ (p ^ 2))
        = ramanujanThetaRaw (-(q ^ (p ^ 2)) ^ 2) (-(q ^ (p ^ 2))) := by
      rw [hpow]
    rw [hsymm]
    exact hmain
  · obtain ⟨hEA, hEB⟩ := s_exp_neg p hp5 s hs h6
    rw [hEA, hEB]
    rw [ramanujanThetaRaw_symm]
    have hsymm : ramanujanThetaRaw (-q ^ (2 * p ^ 2)) (-q ^ (p ^ 2))
        = ramanujanThetaRaw (-(q ^ (p ^ 2)) ^ 2) (-(q ^ (p ^ 2))) := by
      rw [hpow]
    rw [hsymm]
    exact hmain

private theorem twelve_div (X : ℕ) : (12 * X) / 24 = X / 2 := by
  omega

private theorem s_pent_eq (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (s : ℤ)
    (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6) :
    (s * (3 * s + 1) / 2).toNat = (p ^ 2 - 1) / 24 := by
  rcases prime_mod_six p hp hp5 with h1 | h5
  · have hdiv := Nat.div_add_mod p 6
    have hp_eq : p = 6 * (p / 6) + 1 := by omega
    set t := p / 6 with ht
    have hpZ : (p : ℤ) = 6 * (t : ℤ) + 1 := by
      rw [hp_eq]
      push_cast
      ring
    have hsZ : s = (t : ℤ) := by
      rw [hs]
      simp only [h1, ↓reduceIte]
      omega
    have hLHS : (s * (3 * s + 1) / 2).toNat = t * (3 * t + 1) / 2 := by
      rw [hsZ]
      have hcast : (t : ℤ) * (3 * (t : ℤ) + 1) = ((t * (3 * t + 1) : ℕ) : ℤ) := by
        push_cast
        ring
      have h2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_cast
      calc ((t : ℤ) * (3 * (t : ℤ) + 1) / 2).toNat
          = ((((t * (3 * t + 1) : ℕ) : ℤ)) / 2).toNat := by rw [hcast]
        _ = ((((t * (3 * t + 1) : ℕ) : ℤ)) / ((2 : ℕ) : ℤ)).toNat := by rw [h2]
        _ = ((t * (3 * t + 1) / 2 : ℕ) : ℤ).toNat := by
            rw [← Int.natCast_ediv]
        _ = t * (3 * t + 1) / 2 := Int.toNat_natCast _
    have hRHS : (p ^ 2 - 1) / 24 = t * (3 * t + 1) / 2 := by
      have hsq : p ^ 2 - 1 = 12 * (t * (3 * t + 1)) := by
        have hpsq : p ^ 2 = (6 * t + 1) ^ 2 := by rw [hp_eq]
        have hexpand : (6 * t + 1) ^ 2 = 36 * t ^ 2 + 12 * t + 1 := by ring
        have hsub : 36 * t ^ 2 + 12 * t + 1 - 1 = 36 * t ^ 2 + 12 * t :=
          Nat.add_sub_cancel _ _
        have hfac : 36 * t ^ 2 + 12 * t = 12 * (t * (3 * t + 1)) := by ring
        rw [hpsq, hexpand, hsub, hfac]
      rw [hsq, twelve_div]
    rw [hLHS, hRHS]
  · have hdiv := Nat.div_add_mod p 6
    have hp_eq : p = 6 * (p / 6) + 5 := by omega
    set t := p / 6 with ht
    have hpZ : (p : ℤ) = 6 * (t : ℤ) + 5 := by
      rw [hp_eq]
      push_cast
      ring
    have hne : p % 6 ≠ 1 := by omega
    have hsZ : s = -(t : ℤ) - 1 := by
      rw [hs]
      simp only [hne, ↓reduceIte]
      omega
    have hLHS : (s * (3 * s + 1) / 2).toNat = (t + 1) * (3 * t + 2) / 2 := by
      rw [hsZ]
      have hcast : (-(t : ℤ) - 1) * (3 * (-(t : ℤ) - 1) + 1)
          = (((t + 1) * (3 * t + 2) : ℕ) : ℤ) := by
        push_cast
        ring
      have h2 : (2 : ℤ) = ((2 : ℕ) : ℤ) := by norm_cast
      calc ((-(t : ℤ) - 1) * (3 * (-(t : ℤ) - 1) + 1) / 2).toNat
          = ((((t + 1) * (3 * t + 2) : ℕ) : ℤ) / 2).toNat := by rw [hcast]
        _ = ((((t + 1) * (3 * t + 2) : ℕ) : ℤ) / ((2 : ℕ) : ℤ)).toNat := by rw [h2]
        _ = (((t + 1) * (3 * t + 2) / 2 : ℕ) : ℤ).toNat := by
            rw [← Int.natCast_ediv]
        _ = (t + 1) * (3 * t + 2) / 2 := Int.toNat_natCast _
    have hRHS : (p ^ 2 - 1) / 24 = (t + 1) * (3 * t + 2) / 2 := by
      have hsq : p ^ 2 - 1 = 12 * ((t + 1) * (3 * t + 2)) := by
        have hpsq : p ^ 2 = (6 * t + 5) ^ 2 := by rw [hp_eq]
        have hexpand : (6 * t + 5) ^ 2 = 36 * t ^ 2 + 60 * t + 25 := by ring
        have hsub : 36 * t ^ 2 + 60 * t + 25 - 1 = 36 * t ^ 2 + 60 * t + 24 := by omega
        have hfac : 36 * t ^ 2 + 60 * t + 24 = 12 * ((t + 1) * (3 * t + 2)) := by ring
        rw [hpsq, hexpand, hsub, hfac]
      rw [hsq, twelve_div]
    rw [hLHS, hRHS]

/-- **Cui–Gu $p$-dissection of $f_1$.** Let $p \ge 5$ be a prime, let $s = (p - 1)/6$ if
$p \equiv 1 \pmod 6$ and $s = (-p - 1)/6$ otherwise, and let $q$ be a complex number with
$|q| < 1$. Write $f_k = (q^k; q^k)_\infty = \prod_{m \ge 1} (1 - q^{km})$, let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function, and
let $K$ be the set of integers $k$ with $(1 - p)/2 \le k \le (p - 1)/2$ and $k \ne s$. Then
$$
f_1 = \sum_{k \in K} (-1)^k q^{k(3k+1)/2}
f\bigl(-q^{(3p^2 + (6k+1)p)/2}, -q^{(3p^2 - (6k+1)p)/2}\bigr) +
(-1)^s q^{(p^2-1)/24} f_{p^2}.
$$
All the divisions are exact and all the exponents of $q$ are nonnegative integers.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Lemma 5, eq. (8) (`integers-2024-A86-lem-5`),
quoting S. Cui and N. Gu, *Arithmetic Properties of ℓ-Regular Partitions*, Adv. Appl. Math. 51
(2013), 507–523, Theorem 2.2. The same identity is Nayaka, Dharmendra and Mahesh Kumar,
*Divisibility Properties for Overcubic Partition Triples*, INTEGERS 24 (2024), Article A80,
Lemma 4, eq. (43) (`integers-2024-A80-lem-4`). -/
public theorem qPochhammer_prime_dissection (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (s : ℤ) (hs : s = if p % 6 = 1 then ((p : ℤ) - 1) / 6 else (-(p : ℤ) - 1) / 6)
    (q : ℂ) (hq : ‖q‖ < 1) :
    QPochhammer.qPochhammerInfRaw q q =
      ∑ k ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).erase s,
          (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat *
            ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
              (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) +
        (-1 : ℂ) ^ s * q ^ ((p ^ 2 - 1) / 24) *
          QPochhammer.qPochhammerInfRaw (q ^ (p ^ 2)) (q ^ (p ^ 2)) := by
  classical
  have hpent := pent_theorem q hq
  have hsplit := dissection_split p hp5 q hq
  have hsK := mem_Icc_s p hp5 s hs
  have hfib_eq : ∀ k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2),
      (∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
        * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat)
      = (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat *
        ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
          (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) := by
    intro k hk
    exact fiber_eq_theta p hp hp5 k hk q hq
  have hsum_erase : (∑ k ∈ Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2),
        ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
          * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat)
      = (∑ k ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).erase s,
        ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
          * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat)
        + (∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + s)
          * q ^ (((p : ℤ) * m + s) * (3 * ((p : ℤ) * m + s) + 1) / 2).toNat) :=
    (Finset.sum_erase_add _ _ hsK).symm
  have hcongr : (∑ k ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).erase s,
        ∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + k)
          * q ^ (((p : ℤ) * m + k) * (3 * ((p : ℤ) * m + k) + 1) / 2).toNat)
      = ∑ k ∈ (Finset.Icc ((1 - (p : ℤ)) / 2) (((p : ℤ) - 1) / 2)).erase s,
        (-1 : ℂ) ^ k * q ^ (k * (3 * k + 1) / 2).toNat *
          ramanujanThetaRaw (-q ^ ((3 * (p : ℤ) ^ 2 + (6 * k + 1) * p) / 2).toNat)
            (-q ^ ((3 * (p : ℤ) ^ 2 - (6 * k + 1) * p) / 2).toNat) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkK := Finset.mem_of_mem_erase hk
    exact hfib_eq k hkK
  have hs_fiber : (∑' m : ℤ, (-1 : ℂ) ^ ((p : ℤ) * m + s)
        * q ^ (((p : ℤ) * m + s) * (3 * ((p : ℤ) * m + s) + 1) / 2).toNat)
      = (-1 : ℂ) ^ s * q ^ ((p ^ 2 - 1) / 24) *
        QPochhammer.qPochhammerInfRaw (q ^ (p ^ 2)) (q ^ (p ^ 2)) := by
    have h1 := hfib_eq s hsK
    have h2 := theta_s_eq p hp hp5 s hs q hq
    have h3 := s_pent_eq p hp hp5 s hs
    rw [h1, h2, h3]
  rw [hpent, hsplit, hsum_erase, hcongr, hs_fiber]

end

end MetaMathlibExt
