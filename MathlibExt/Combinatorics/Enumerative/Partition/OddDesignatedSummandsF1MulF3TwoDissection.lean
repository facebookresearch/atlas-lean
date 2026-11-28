/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import MathlibExt.NumberTheory.ModularForms.QParamProduct

/-!
# The 2-dissection of `f₁ * f₃`

Evaluating Ramanujan's theta product identity at the parameters `(-q, -q⁵)` and `(-q³, -q³)`
and writing each theta factor as a quotient of Euler products by the Jacobi triple product
gives the 2-dissection `f1_mul_f3_two_dissection` of the product `f₁ * f₃`, transferred from
the open unit disk to integer power series.

Statements from James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for
2-Regular Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

local notation "𝔣" => qEulerProduct

open QPochhammer

namespace f1_mul_f3_two_dissection

local notation "P" => qPochhammerInfRaw

private lemma norm_pow_lt_one {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hn

private lemma twice_triangle (n : ℤ) :
    2 * (((n * (n + 1) / 2).toNat : ℕ) : ℤ) = n * (n + 1) := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self n)

private lemma theta_term (z r : ℂ) (hz : z ≠ 0) (n : ℤ) :
    ramanujanThetaTerm (z * r) (z⁻¹ * r) n = z ^ n * r ^ (n * n).toNat := by
  let u := (n * (n + 1) / 2).toNat
  let v := (n * (n - 1) / 2).toNat
  have hu : 2 * (u : ℤ) = n * (n + 1) := twice_triangle n
  have hv : 2 * (v : ℤ) = n * (n - 1) := by
    simpa only [show -n * (-n + 1) = n * (n - 1) by ring] using twice_triangle (-n)
  have hd : (u : ℤ) - v = n := by linarith only [hu, hv]
  have hs : u + v = (n * n).toNat := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_add, Int.toNat_of_nonneg (mul_self_nonneg n)]
    linarith only [hu, hv]
  change (z * r) ^ u * (z⁻¹ * r) ^ v = _
  rw [mul_pow, mul_pow, mul_mul_mul_comm, ← pow_add, hs,
    ← zpow_natCast z u, ← zpow_natCast z⁻¹ v, inv_zpow', ← zpow_add₀ hz,
    ← sub_eq_add_neg, hd]

open Analysis.SpecialFunctions.JacobiTripleProduct in
private lemma theta_product (z r : ℂ) (hz : z ≠ 0) (hr : ‖r‖ < 1) :
    ramanujanThetaRaw (z * r) (z⁻¹ * r) =
      P (r ^ 2) (r ^ 2) * P (-(z * r)) (r ^ 2) * P (-(z⁻¹ * r)) (r ^ 2) := by
  have h₂ := norm_pow_lt_one hr two_ne_zero
  obtain ⟨-, -, hj⟩ := jacobi_triple_product z r hz hr
  simp only [ramanujanThetaRaw, theta_term z r hz, hj]
  have hp := ((hasProd_qPochhammerInf (r ^ 2) (r ^ 2) h₂).mul
    (hasProd_qPochhammerInf (-(z * r)) (r ^ 2) h₂)).mul
      (hasProd_qPochhammerInf (-(z⁻¹ * r)) (r ^ 2) h₂)
  apply (hp.congr_fun (fun n => ?_)).tprod_eq
  simp only [pow_add, pow_mul, pow_one]
  ring

-- Group the factors of a q-Pochhammer product by their index modulo `d`.
private lemma split_poch (a q : ℂ) (hq : ‖q‖ < 1) (d : ℕ) [NeZero d] :
    P a q = ∏ i : Fin d, P (a * q ^ (i.val)) (q ^ d) := by
  let e := (Equiv.prodComm (Fin d) ℕ).trans (Nat.divModEquiv d).symm
  have hp := e.hasProd_iff.mpr (hasProd_qPochhammerInf a q hq)
  have hf := hp.prod_fiberwise (g := fun i : Fin d => P (a * q ^ (i.val)) (q ^ d)) (by
    intro i
    apply (hasProd_qPochhammerInf _ _ (norm_pow_lt_one hq (NeZero.ne d))).congr_fun
    intro n
    simp [e, pow_add, pow_mul, mul_comm n d]
    ring)
  exact hf.unique (hasProd_fintype _)

private lemma pair_prod (a q : ℂ) (h : ‖q‖ < 1) :
    P a q * P (-a) q = P (a ^ 2) (q ^ 2) := by
  have hp := (hasProd_qPochhammerInf a q h).mul (hasProd_qPochhammerInf (-a) q h)
  apply hp.unique
  exact (hasProd_qPochhammerInf (a ^ 2) (q ^ 2) (norm_pow_lt_one h two_ne_zero)).congr_fun
    fun n => by ring

private lemma eulerFunction_eq_poch {x : ℂ} (h : ‖x‖ < 1) :
    eulerFunction x = P x x :=
  (hasProd_eulerFunction h).unique
    ((hasProd_qPochhammerInf x x h).congr_fun fun n => by rw [pow_succ'])

private lemma theta_neg_q {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 5) = P (q ^ 6) (q ^ 6) * P q (q ^ 6) * P (q ^ 5) (q ^ 6) := by
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  have hzr : (q ^ 2)⁻¹ * (-q ^ 3) = -q := by field_simp
  have hzr' : ((q ^ 2)⁻¹)⁻¹ * (-q ^ 3) = -q ^ 5 := by rw [inv_inv]; ring
  have hr2 : (-q ^ 3) ^ 2 = q ^ 6 := by ring
  have hr : ‖-q ^ 3‖ < 1 := by
    rw [norm_neg]
    exact norm_pow_lt_one h (by decide)
  have hprod := theta_product ((q ^ 2)⁻¹) (-q ^ 3) (inv_ne_zero hq2) hr
  rw [hzr, hzr', hr2] at hprod
  simpa only [neg_neg] using hprod

private lemma theta_neg_cube {q : ℂ} (h : ‖q‖ < 1) :
    ramanujanThetaRaw (-q ^ 3) (-q ^ 3) =
      P (q ^ 6) (q ^ 6) * P (q ^ 3) (q ^ 6) * P (q ^ 3) (q ^ 6) := by
  have hr2 : (-q ^ 3) ^ 2 = q ^ 6 := by ring
  have hr : ‖-q ^ 3‖ < 1 := by
    rw [norm_neg]
    exact norm_pow_lt_one h (by decide)
  have hprod := theta_product 1 (-q ^ 3) one_ne_zero hr
  simpa only [one_mul, inv_one, hr2, neg_neg] using hprod

private lemma theta_four_eight {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (q ^ 4) (q ^ 8) =
      P (q ^ 12) (q ^ 12) * P (-q ^ 4) (q ^ 12) * P (-q ^ 8) (q ^ 12) := by
  have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
  have hzr : (q ^ 2)⁻¹ * (q ^ 6) = q ^ 4 := by field_simp
  have hzr' : ((q ^ 2)⁻¹)⁻¹ * (q ^ 6) = q ^ 8 := by rw [inv_inv]; ring
  have hr2 : (q ^ 6) ^ 2 = q ^ 12 := by ring
  have hprod := theta_product ((q ^ 2)⁻¹) (q ^ 6) (inv_ne_zero hq2)
    (norm_pow_lt_one h (by decide))
  rw [hzr, hzr', hr2] at hprod
  exact hprod

private lemma theta_two_ten {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (q ^ 2) (q ^ 10) =
      P (q ^ 12) (q ^ 12) * P (-q ^ 2) (q ^ 12) * P (-q ^ 10) (q ^ 12) := by
  have hq4 : q ^ 4 ≠ 0 := pow_ne_zero 4 hq
  have hzr : (q ^ 4)⁻¹ * (q ^ 6) = q ^ 2 := by field_simp
  have hzr' : ((q ^ 4)⁻¹)⁻¹ * (q ^ 6) = q ^ 10 := by rw [inv_inv]; ring
  have hr2 : (q ^ 6) ^ 2 = q ^ 12 := by ring
  have hprod := theta_product ((q ^ 4)⁻¹) (q ^ 6) (inv_ne_zero hq4)
    (norm_pow_lt_one h (by decide))
  rw [hzr, hzr', hr2] at hprod
  exact hprod

private lemma split_q2_3 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 2) (q ^ 2) = P (q ^ 2) (q ^ 6) * P (q ^ 4) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
  have h2 := norm_pow_lt_one h (by decide : (2 : ℕ) ≠ 0)
  have h := split_poch (q ^ 2) (q ^ 2) h2 3
  simp only [Fin.prod_univ_three, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q_6 {q : ℂ} (h : ‖q‖ < 1) :
    P q q = P q (q ^ 6) * P (q ^ 2) (q ^ 6) * P (q ^ 3) (q ^ 6) * P (q ^ 4) (q ^ 6) *
      P (q ^ 5) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
  have h := split_poch q q h 6
  simp only [Fin.prod_univ_six] at h
  rw [show ((0 : Fin 6).val) = 0 from rfl, show ((1 : Fin 6).val) = 1 from rfl,
    show ((2 : Fin 6).val) = 2 from rfl, show ((3 : Fin 6).val) = 3 from rfl,
    show ((4 : Fin 6).val) = 4 from rfl, show ((5 : Fin 6).val) = 5 from rfl] at h
  simp only [pow_zero, pow_one, mul_one] at h
  rw [show q * q = q ^ 2 from by ring, show q * q ^ 2 = q ^ 3 from by ring,
    show q * q ^ 3 = q ^ 4 from by ring, show q * q ^ 4 = q ^ 5 from by ring,
    show q * q ^ 5 = q ^ 6 from by ring] at h
  exact h

private lemma split_q3_2 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 3) (q ^ 3) = P (q ^ 3) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
  have h3 := norm_pow_lt_one (n := 3) h (by decide)
  have h := split_poch (q ^ 3) (q ^ 3) h3 2
  simp only [Fin.prod_univ_two, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q4_3 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 4) (q ^ 4) = P (q ^ 4) (q ^ 12) * P (q ^ 8) (q ^ 12) * P (q ^ 12) (q ^ 12) := by
  have h4 := norm_pow_lt_one (n := 4) h (by decide)
  have h := split_poch (q ^ 4) (q ^ 4) h4 3
  simp only [Fin.prod_univ_three, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q8_3 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 8) (q ^ 8) = P (q ^ 8) (q ^ 24) * P (q ^ 16) (q ^ 24) * P (q ^ 24) (q ^ 24) := by
  have h8 := norm_pow_lt_one (n := 8) h (by decide)
  have h := split_poch (q ^ 8) (q ^ 8) h8 3
  simp only [Fin.prod_univ_three, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q2_6 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 2) (q ^ 2) = P (q ^ 2) (q ^ 12) * P (q ^ 4) (q ^ 12) * P (q ^ 6) (q ^ 12) *
      P (q ^ 8) (q ^ 12) * P (q ^ 10) (q ^ 12) * P (q ^ 12) (q ^ 12) := by
  have h2 := norm_pow_lt_one h (by decide : (2 : ℕ) ≠ 0)
  have h := split_poch (q ^ 2) (q ^ 2) h2 6
  simp only [Fin.prod_univ_six, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q4_12_2 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 4) (q ^ 12) = P (q ^ 4) (q ^ 24) * P (q ^ 16) (q ^ 24) := by
  have h12 := norm_pow_lt_one (n := 12) h (by decide)
  have h := split_poch (q ^ 4) (q ^ 12) h12 2
  simp only [Fin.prod_univ_two, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q6_12_2 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 6) (q ^ 12) = P (q ^ 6) (q ^ 24) * P (q ^ 18) (q ^ 24) := by
  have h12 := norm_pow_lt_one (n := 12) h (by decide)
  have h := split_poch (q ^ 6) (q ^ 12) h12 2
  simp only [Fin.prod_univ_two, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q8_12_2 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 8) (q ^ 12) = P (q ^ 8) (q ^ 24) * P (q ^ 20) (q ^ 24) := by
  have h12 := norm_pow_lt_one (n := 12) h (by decide)
  have h := split_poch (q ^ 8) (q ^ 12) h12 2
  simp only [Fin.prod_univ_two, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q12_2 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 12) (q ^ 12) = P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24) := by
  have h12 := norm_pow_lt_one (n := 12) h (by decide)
  have h := split_poch (q ^ 12) (q ^ 12) h12 2
  simp only [Fin.prod_univ_two, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q4_6 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 4) (q ^ 4) = P (q ^ 4) (q ^ 24) * P (q ^ 8) (q ^ 24) * P (q ^ 12) (q ^ 24) *
      P (q ^ 16) (q ^ 24) * P (q ^ 20) (q ^ 24) * P (q ^ 24) (q ^ 24) := by
  have h4 := norm_pow_lt_one (n := 4) h (by decide)
  have h := split_poch (q ^ 4) (q ^ 4) h4 6
  simp only [Fin.prod_univ_six, ← pow_add, ← pow_mul] at h
  exact h

private lemma split_q6_4 {q : ℂ} (h : ‖q‖ < 1) :
    P (q ^ 6) (q ^ 6) = P (q ^ 6) (q ^ 24) * P (q ^ 12) (q ^ 24) * P (q ^ 18) (q ^ 24) *
      P (q ^ 24) (q ^ 24) := by
  have h6 := norm_pow_lt_one (n := 6) h (by decide)
  have h := split_poch (q ^ 6) (q ^ 6) h6 4
  simp only [Fin.prod_univ_four, ← pow_add, ← pow_mul] at h
  exact h

private lemma prod_left {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 5) * ramanujanThetaRaw (-q ^ 3) (-q ^ 3) *
      eulerFunction (q ^ 2) =
      eulerFunction q * eulerFunction (q ^ 3) * eulerFunction (q ^ 6) := by
  have h2 := norm_pow_lt_one h (by decide : (2 : ℕ) ≠ 0)
  have h3 := norm_pow_lt_one (n := 3) h (by decide)
  have h6 := norm_pow_lt_one (n := 6) h (by decide)
  rw [theta_neg_q hq h, theta_neg_cube h, eulerFunction_eq_poch h,
    eulerFunction_eq_poch h2, eulerFunction_eq_poch h3, eulerFunction_eq_poch h6,
    split_q2_3 h, split_q_6 h, split_q3_2 h]
  ring

private lemma prod_mid {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (q ^ 4) (q ^ 8) * eulerFunction (q ^ 4) * eulerFunction (q ^ 24) =
      eulerFunction (q ^ 8) * eulerFunction (q ^ 12) ^ 2 := by
  have h4 := norm_pow_lt_one (n := 4) h (by decide)
  have h8 := norm_pow_lt_one (n := 8) h (by decide)
  have h12 := norm_pow_lt_one (n := 12) h (by decide)
  have h24 := norm_pow_lt_one (n := 24) h (by decide)
  have r1 : P (q ^ 4) (q ^ 12) * P (-q ^ 4) (q ^ 12) = P (q ^ 8) (q ^ 24) := by
    have hp := pair_prod (q ^ 4) (q ^ 12) h12
    simpa only [← pow_mul] using hp
  have r2 : P (q ^ 8) (q ^ 12) * P (-q ^ 8) (q ^ 12) = P (q ^ 16) (q ^ 24) := by
    have hp := pair_prod (q ^ 8) (q ^ 12) h12
    simpa only [← pow_mul] using hp
  rw [theta_four_eight hq h, eulerFunction_eq_poch h4, eulerFunction_eq_poch h24,
    eulerFunction_eq_poch h8, eulerFunction_eq_poch h12, split_q4_3 h, split_q8_3 h]
  have key : (P (q ^ 4) (q ^ 12) * P (-q ^ 4) (q ^ 12)) *
      ((P (q ^ 8) (q ^ 12) * P (-q ^ 8) (q ^ 12)) *
        (P (q ^ 12) (q ^ 12) ^ 2 * P (q ^ 24) (q ^ 24))) =
      P (q ^ 8) (q ^ 24) * P (q ^ 16) (q ^ 24) *
        (P (q ^ 12) (q ^ 12) ^ 2 * P (q ^ 24) (q ^ 24)) := by
    rw [r1, r2]
    ring
  linear_combination key

private lemma prod_right {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (q ^ 2) (q ^ 10) * eulerFunction (q ^ 2) * eulerFunction (q ^ 8) *
        eulerFunction (q ^ 12) =
      eulerFunction (q ^ 4) ^ 2 * eulerFunction (q ^ 6) * eulerFunction (q ^ 24) := by
  have h2 := norm_pow_lt_one h (by decide : (2 : ℕ) ≠ 0)
  have h4 := norm_pow_lt_one (n := 4) h (by decide)
  have h6 := norm_pow_lt_one (n := 6) h (by decide)
  have h8 := norm_pow_lt_one (n := 8) h (by decide)
  have h12 := norm_pow_lt_one (n := 12) h (by decide)
  have h24 := norm_pow_lt_one (n := 24) h (by decide)
  have r1 : P (q ^ 2) (q ^ 12) * P (-q ^ 2) (q ^ 12) = P (q ^ 4) (q ^ 24) := by
    have hp := pair_prod (q ^ 2) (q ^ 12) h12
    simpa only [← pow_mul] using hp
  have r2 : P (q ^ 10) (q ^ 12) * P (-q ^ 10) (q ^ 12) = P (q ^ 20) (q ^ 24) := by
    have hp := pair_prod (q ^ 10) (q ^ 12) h12
    simpa only [← pow_mul] using hp
  rw [theta_two_ten hq h, eulerFunction_eq_poch h2, eulerFunction_eq_poch h8,
    eulerFunction_eq_poch h12, eulerFunction_eq_poch h4, eulerFunction_eq_poch h6,
    eulerFunction_eq_poch h24, split_q2_6 h, split_q4_12_2 h, split_q6_12_2 h,
    split_q8_12_2 h, split_q12_2 h, split_q8_3 h, split_q4_6 h, split_q6_4 h]
  have key : (P (q ^ 2) (q ^ 12) * P (-q ^ 2) (q ^ 12)) *
      ((P (q ^ 10) (q ^ 12) * P (-q ^ 10) (q ^ 12)) *
        ((P (q ^ 4) (q ^ 24) * P (q ^ 16) (q ^ 24)) *
          ((P (q ^ 6) (q ^ 24) * P (q ^ 18) (q ^ 24)) *
            ((P (q ^ 8) (q ^ 24) * P (q ^ 20) (q ^ 24)) *
              ((P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24)) *
                ((P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24)) *
                  ((P (q ^ 8) (q ^ 24) * P (q ^ 16) (q ^ 24) * P (q ^ 24) (q ^ 24)) *
                    (P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24))))))))) =
      P (q ^ 4) (q ^ 24) * P (q ^ 20) (q ^ 24) *
        ((P (q ^ 4) (q ^ 24) * P (q ^ 16) (q ^ 24)) *
          ((P (q ^ 6) (q ^ 24) * P (q ^ 18) (q ^ 24)) *
            ((P (q ^ 8) (q ^ 24) * P (q ^ 20) (q ^ 24)) *
              ((P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24)) *
                ((P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24)) *
                  ((P (q ^ 8) (q ^ 24) * P (q ^ 16) (q ^ 24) * P (q ^ 24) (q ^ 24)) *
                    (P (q ^ 12) (q ^ 24) * P (q ^ 24) (q ^ 24)))))))) := by
    rw [r1, r2]
    ring
  linear_combination key

private lemma theta_mul {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 5) * ramanujanThetaRaw (-q ^ 3) (-q ^ 3) =
      ramanujanThetaRaw (q ^ 4) (q ^ 8) ^ 2 -
        q * ramanujanThetaRaw (q ^ 2) (q ^ 10) ^ 2 := by
  have ha : -q ≠ 0 := neg_ne_zero.mpr hq
  have hab : ‖-q * -q ^ 5‖ < 1 := by
    have e : -q * -q ^ 5 = q ^ 6 := by ring
    rw [e]
    exact norm_pow_lt_one h (by decide)
  have hcd : -q * -q ^ 5 = -q ^ 3 * -q ^ 3 := by ring
  have hmul := ramanujanTheta_mul_of_mul_eq (a := -q) (b := -q ^ 5) (c := -q ^ 3)
    (d := -q ^ 3) ha hab hcd
  have e1 : (-q) * (-q ^ 3) = q ^ 4 := by ring
  have e2 : (-q ^ 5) * (-q ^ 3) = q ^ 8 := by ring
  have e3 : (-q ^ 3) / (-q) = q ^ 2 := by
    rw [div_eq_iff (neg_ne_zero.mpr hq)]
    ring
  have e4 : (-q) ^ 2 * (-q ^ 5) * (-q ^ 3) = q ^ 10 := by ring
  rw [e1, e2, e3, e4] at hmul
  linear_combination hmul

private lemma analytic_dissection {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    eulerFunction q * eulerFunction (q ^ 3) * eulerFunction (q ^ 2) *
        eulerFunction (q ^ 4) ^ 2 * eulerFunction (q ^ 6) * eulerFunction (q ^ 8) ^ 2 *
        eulerFunction (q ^ 12) ^ 2 * eulerFunction (q ^ 24) ^ 2 =
      eulerFunction (q ^ 2) ^ 2 * eulerFunction (q ^ 8) ^ 4 * eulerFunction (q ^ 12) ^ 6 -
        q * eulerFunction (q ^ 4) ^ 6 * eulerFunction (q ^ 6) ^ 2 *
          eulerFunction (q ^ 24) ^ 4 := by
  have hL := prod_left hq h
  have hM := prod_mid hq h
  have hR := prod_right hq h
  have hT := theta_mul hq h
  have hM2 := congrArg (· ^ 2) hM
  have hR2 := congrArg (· ^ 2) hR
  simp only [mul_pow] at hM2 hR2
  linear_combination (eulerFunction (q ^ 2) ^ 2 * eulerFunction (q ^ 4) ^ 2 *
      eulerFunction (q ^ 8) ^ 2 * eulerFunction (q ^ 12) ^ 2 *
      eulerFunction (q ^ 24) ^ 2) * hT +
    (eulerFunction (q ^ 2) ^ 2 * eulerFunction (q ^ 8) ^ 2 *
      eulerFunction (q ^ 12) ^ 2) * hM2 -
    (eulerFunction (q ^ 2) * eulerFunction (q ^ 4) ^ 2 * eulerFunction (q ^ 8) ^ 2 *
      eulerFunction (q ^ 12) ^ 2 * eulerFunction (q ^ 24) ^ 2) * hL -
    (q * eulerFunction (q ^ 4) ^ 2 * eulerFunction (q ^ 24) ^ 2) * hR2

open UpperHalfPlane Function

local notation "𝕢" => Periodic.qParam 1

/-- A complex function represented by an integer power series on the punctured unit disk. -/
private def Represents (F : ℤ⟦X⟧) (f : ℂ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ ↦ (F.coeff n : ℂ) * 𝕢 τ ^ n) (f (𝕢 τ))

private lemma Represents.mul {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) :
    Represents (F * G) (fun q ↦ f q * g q) := by
  intro τ
  let ι := Int.castRingHom ℂ
  simpa [← map_mul, coeff_map, ι] using
    ModularCurve.hasSum_qParam_mul 1 one_pos (map ι F) (map ι G)
      (fun z ↦ f (𝕢 z)) (fun z ↦ g (𝕢 z))
      (by simpa [coeff_map, ι, Represents] using hf)
      (by simpa [coeff_map, ι, Represents] using hg) τ

private lemma Represents.sub {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g) :
    Represents (F - G) (fun q ↦ f q - g q) := by
  intro τ
  simpa [sub_mul] using (hf τ).sub (hg τ)

private lemma represents_const (c : ℤ) : Represents (C c) (fun _ ↦ (c : ℂ)) := by
  intro τ
  refine (hasSum_ite_eq (0 : ℕ) (c : ℂ)).congr_fun fun n ↦ ?_
  rw [coeff_C]
  split_ifs with h <;> simp_all

private lemma represents_X : Represents X id := by
  intro τ
  simpa +contextual [coeff_X, apply_ite, ite_mul] using hasSum_ite_eq (1 : ℕ) (𝕢 τ)

private lemma Represents.pow {F : ℤ⟦X⟧} {f : ℂ → ℂ} (hf : Represents F f) (n : ℕ) :
    Represents (F ^ n) (fun q ↦ f q ^ n) := by
  induction n with
  | zero => simpa using represents_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private lemma represents_euler (k : ℕ) (hk : k ≠ 0) :
    Represents (qEulerProduct k) (fun q ↦ eulerFunction (q ^ k)) := by
  have cont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have prod := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) cont
  have eqn : qEulerProduct k = expand k hk (pentagonalSeries ℤ) := by
    simpa [qEulerProduct, Function.comp_def, pow_mul] using prod.tprod_eq
  rw [eqn]
  intro τ
  have lt1 : ‖𝕢 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hk1 : ‖𝕢 τ ^ k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) lt1 hk
  have inj : Function.Injective (k * ·) := mul_right_injective₀ hk
  apply (inj.hasSum_iff ?_).mp
  · refine (hasSum_eulerFunction_pentagonalSeries hk1).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, coeff_expand_mul, pow_mul]
    congr 1
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨m, rfl⟩ := hn
      simp [coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  · intro n hn
    have hd : ¬ k ∣ n := by simpa [dvd_def, eq_comm] using hn
    simp [coeff_expand_of_not_dvd _ _ _ hd]

private lemma Represents.eq_of_eval {F G : ℤ⟦X⟧} {f g : ℂ → ℂ}
    (hf : Represents F f) (hg : Represents G g)
    (heq : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → f q = g q) : F = G := by
  have hzero : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
    simp [cuspFunction, Pi.zero_comp, Periodic.cuspFunction_zero]
  have han : AnalyticAt ℂ (cuspFunction 1 (0 : ℍ → ℂ)) 0 := hzero ▸ analyticAt_const
  let c (m : ℕ) : ℂ := (F.coeff m : ℂ) - G.coeff m
  have hh := hasFPowerSeriesOnBall_cuspFunction (c := c) one_pos han (fun τ ↦ by
    have he := heq _ (Periodic.qParam_ne_zero _) (Periodic.norm_qParam_lt_one one_pos τ.im_pos)
    simpa [c, smul_eq_mul, sub_mul, he] using (hf τ).sub (hg τ))
  rw [hzero] at hh
  have hz := hh.hasFPowerSeriesAt.eq_zero_of_eventually (Filter.EventuallyEq.refl _ _)
  apply PowerSeries.ext
  intro n
  have hc := (FormalMultilinearSeries.ofScalars_eq_zero (E := ℂ) (c := c) n).mp
    (congrFun hz n)
  simpa [c, sub_eq_zero] using hc

end f1_mul_f3_two_dissection

/-- **The 2-dissection of $f_1 f_3$.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the Euler
products in the ring of integer power series in $q$. Then
$$f_1 f_2 f_3 f_4^2 f_6 f_8^2 f_{12}^2 f_{24}^2 = f_2^2 f_8^4 f_{12}^6 - q f_4^6 f_6^2 f_{24}^4.$$
Since every $f_k$ with $k \ge 1$ has constant term $1$ and so is invertible, this is Hirschhorn's
identity $f_1 f_3 = \frac{f_2 f_8^2 f_{12}^4}{f_4^2 f_6 f_{24}^2} -
q \frac{f_4^4 f_6 f_{24}^2}{f_2 f_8^2 f_{12}^2}$ (*The Power of q*, eq. (30.12.1)) multiplied
through by $f_2 f_4^2 f_6 f_8^2 f_{12}^2 f_{24}^2$.

Source: James A. Sellers, *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular
Partitions with Designated Summands*, INTEGERS 24 (2024), Article A16, Lemma 3
(`integers-2024-A16-lem-3`). -/
public theorem f1_mul_f3_two_dissection :
    𝔣 1 * 𝔣 3 * 𝔣 2 * 𝔣 4 ^ 2 * 𝔣 6 * 𝔣 8 ^ 2 * 𝔣 12 ^ 2 * 𝔣 24 ^ 2 =
      𝔣 2 ^ 2 * 𝔣 8 ^ 4 * 𝔣 12 ^ 6 - X * 𝔣 4 ^ 6 * 𝔣 6 ^ 2 * 𝔣 24 ^ 4 := by
  have h1 := f1_mul_f3_two_dissection.represents_euler 1 one_ne_zero
  simp only [pow_one] at h1
  have h2 := f1_mul_f3_two_dissection.represents_euler 2 two_ne_zero
  have h3 := f1_mul_f3_two_dissection.represents_euler 3 (by decide)
  have h4 := f1_mul_f3_two_dissection.represents_euler 4 (by decide)
  have h6 := f1_mul_f3_two_dissection.represents_euler 6 (by decide)
  have h8 := f1_mul_f3_two_dissection.represents_euler 8 (by decide)
  have h12 := f1_mul_f3_two_dissection.represents_euler 12 (by decide)
  have h24 := f1_mul_f3_two_dissection.represents_euler 24 (by decide)
  have hlhs := ((((((h1.mul h3).mul h2).mul (h4.pow 2)).mul h6).mul (h8.pow 2)).mul
    (h12.pow 2)).mul (h24.pow 2)
  have hrhs1 := ((h2.pow 2).mul (h8.pow 4)).mul (h12.pow 6)
  have hrhs2 := ((f1_mul_f3_two_dissection.represents_X.mul (h4.pow 6)).mul
    (h6.pow 2)).mul (h24.pow 4)
  exact hlhs.eq_of_eval (hrhs1.sub hrhs2) fun q hq h =>
    f1_mul_f3_two_dissection.analytic_dissection hq h

end MetaMathlibExt
