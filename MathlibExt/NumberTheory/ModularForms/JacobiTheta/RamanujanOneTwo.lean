/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Ramanujan's theta function at $(q, q^2)$

The identity `ramanujanTheta_one_two` follows by applying the Jacobi triple product to
both theta series and grouping the resulting factors by their exponents modulo two and three.
-/

namespace MetaMathlibExt

open QPochhammer

local notation "P" => qPochhammerInfRaw

namespace ramanujanTheta_one_two

private lemma norm_pow_lt_one {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hn

private lemma one_two_product {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 2) = P (q ^ 3) (q ^ 3) * P (-q) (q ^ 3) * P (-q ^ 2) (q ^ 3) := by
  have he : q * q ^ 2 = q ^ 3 := by rw [← pow_succ']
  rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (he ▸ norm_pow_lt_one hq (by decide)), he]

private lemma pair_product (a q : ℂ) (hq : ‖q‖ < 1) :
    P a q * P (-a) q = P (a ^ 2) (q ^ 2) := by
  have hp := (hasProd_qPochhammerInf a q hq).mul (hasProd_qPochhammerInf (-a) q hq)
  apply hp.unique
  exact (hasProd_qPochhammerInf (a ^ 2) (q ^ 2) (norm_pow_lt_one hq two_ne_zero)).congr_fun
    fun n => by rw [← pow_mul, mul_comm 2 n, pow_mul]; ring

private lemma diagonal_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : P q q ≠ 0 := by
  simp only [qPochhammerInfRaw_eq_tprod, sub_eq_add_neg, ← neg_mul]
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    rw [neg_mul, ← sub_eq_add_neg, ← pow_succ']
    exact sub_ne_zero.mpr (fun he => by
      have hn := norm_pow_lt_one (n := n + 1) hq (Nat.succ_ne_zero n)
      simp only [← he, norm_one, lt_self_iff_false] at hn)
  · simpa only [norm_mul, norm_neg, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖q‖

end ramanujanTheta_one_two

open ramanujanTheta_one_two in
/-- **Ramanujan's theta function at $(q, q^2)$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function and
$(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$. For every complex number $q$ with $|q| < 1$,
$f(q,q^2) \, (q;q^2)_\infty = f(-q^3,-q^3)$, that is, $f(q,q^2) = \varphi(-q^3)/\chi(-q)$ with
the denominator cleared, where $\varphi(q) = f(q,q)$ and $\chi(-q) = (q;q^2)_\infty$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 5, Equation (11) (`integers-2024-A103-lem-5`). -/
public theorem ramanujanTheta_one_two {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 2) * qPochhammerInfRaw q (q ^ 2) =
      ramanujanThetaRaw (-q ^ 3) (-q ^ 3) := by
  have h₂ := norm_pow_lt_one hq two_ne_zero
  have h₃ := norm_pow_lt_one (n := 3) hq (by decide)
  have h₆ : (q ^ 3) ^ 2 = q ^ 6 := by rw [← pow_mul]
  have h₄ : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have hdiag : ramanujanThetaRaw (-q ^ 3) (-q ^ 3) =
      P (q ^ 6) (q ^ 6) * P (q ^ 3) (q ^ 6) * P (q ^ 3) (q ^ 6) := by
    have he : (-q ^ 3) * (-q ^ 3) = q ^ 6 := by rw [neg_mul_neg, ← sq, h₆]
    have h₆' : ‖q ^ 6‖ < 1 := norm_pow_lt_one hq (by decide)
    rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (he ▸ h₆'), he, neg_neg]
  have hsplit₂ : P q q = P q (q ^ 2) * P (q ^ 2) (q ^ 2) := by
    simpa [Fin.prod_univ_two, pow_two] using qPochhammerInfRaw_split q q hq 2
  have hsplit₃ : P q q = P q (q ^ 3) * P (q ^ 2) (q ^ 3) * P (q ^ 3) (q ^ 3) := by
    simpa [Fin.prod_univ_three, pow_succ', mul_assoc] using qPochhammerInfRaw_split q q hq 3
  have hsplit₂₃ : P (q ^ 2) (q ^ 2) =
      P (q ^ 2) (q ^ 6) * P (q ^ 4) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
    have h := qPochhammerInfRaw_split (q ^ 2) (q ^ 2) h₂ 3
    simp only [← pow_succ'] at h
    simpa [Fin.prod_univ_three, ← pow_mul, mul_assoc] using h
  have hsplit₃₂ : P (q ^ 3) (q ^ 3) = P (q ^ 3) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
    have h := qPochhammerInfRaw_split (q ^ 3) (q ^ 3) h₃ 2
    simp only [← pow_succ'] at h
    simpa [Fin.prod_univ_two, h₆] using h
  have hpair₁ : P q (q ^ 3) * P (-q) (q ^ 3) = P (q ^ 2) (q ^ 6) := by
    simpa only [h₆] using pair_product q (q ^ 3) h₃
  have hpair₂ : P (q ^ 2) (q ^ 3) * P (-q ^ 2) (q ^ 3) = P (q ^ 4) (q ^ 6) := by
    have h := pair_product (q ^ 2) (q ^ 3) h₃
    rwa [h₆, h₄] at h
  -- Clear the common Euler product so that the remaining factors can be paired.
  rw [one_two_product hq, hdiag]
  apply mul_right_cancel₀ (diagonal_ne_zero hq)
  calc
    _ = P (q ^ 3) (q ^ 3) ^ 2 * P q (q ^ 2) *
        ((P q (q ^ 3) * P (-q) (q ^ 3)) * (P (q ^ 2) (q ^ 3) * P (-q ^ 2) (q ^ 3))) := by
      rw [hsplit₃]
      ring
    _ = (P (q ^ 3) (q ^ 6) ^ 2 * P (q ^ 6) (q ^ 6)) * (P q (q ^ 2) * P (q ^ 2) (q ^ 2)) := by
      rw [hpair₁, hpair₂, hsplit₃₂, hsplit₂₃]
      ring
    _ = _ := by rw [hsplit₂]; ring

end MetaMathlibExt
