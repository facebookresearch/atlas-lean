/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Product forms of Ramanujan's theta functions

We express the specializations ψ and f of the general theta function and the products
χ(q) and χ(-q) as quotients of Euler products on the open unit disk.
-/

namespace MetaMathlibExt

open QPochhammer

namespace ramanujan_psi_f_chi_eq_qPochhammer

local notation "P" => qPochhammerInfRaw

private lemma norm_sq_lt_one {q : ℂ} (h : ‖q‖ < 1) : ‖q ^ 2‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) h two_ne_zero

private lemma split_prod (a q : ℂ) (h : ‖q‖ < 1) :
    P a q = P a (q ^ 2) * P (a * q) (q ^ 2) := by
  have he := hasProd_qPochhammerInf a (q ^ 2) (norm_sq_lt_one h)
  have ho := hasProd_qPochhammerInf (a * q) (q ^ 2) (norm_sq_lt_one h)
  apply (hasProd_qPochhammerInf a q h).unique
  apply HasProd.even_mul_odd
  · exact he.congr_fun fun n => by simp [pow_mul]
  · exact ho.congr_fun fun n => by simp [pow_succ, pow_mul]; ring

private lemma pair_prod (a q : ℂ) (h : ‖q‖ < 1) :
    P a q * P (-a) q = P (a ^ 2) (q ^ 2) := by
  have hp := (hasProd_qPochhammerInf a q h).mul (hasProd_qPochhammerInf (-a) q h)
  apply hp.unique
  exact (hasProd_qPochhammerInf (a ^ 2) (q ^ 2) (norm_sq_lt_one h)).congr_fun
    fun n => by ring

private lemma diagonal_ne_zero {q : ℂ} (h : ‖q‖ < 1) : P q q ≠ 0 := by
  simp only [qPochhammerInfRaw, sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n he
    have heq : q ^ (n + 1) = 1 := by rw [pow_succ']; linear_combination -he
    have := pow_lt_one₀ (norm_nonneg q) h (Nat.succ_ne_zero n)
    rwa [← norm_pow, heq, norm_one, lt_self_iff_false] at this
  · simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) h).mul_left ‖q‖

private def tri (n : ℤ) : ℕ := (n * (n - 1) / 2).toNat

private lemma twice_tri (n : ℤ) : 2 * (tri n : ℤ) = n * (n - 1) := by
  have hn : 0 ≤ n * (n - 1) := by
    rcases le_or_gt n 0 with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
    · exact mul_nonneg h.le (by omega)
  rw [tri, Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_pred_self n)

private lemma term_eq (a b : ℂ) (n : ℤ) :
    ramanujanThetaTerm a b n = a ^ tri (-n) * b ^ tri n := by
  simp only [tri, ramanujanThetaTerm, show -n * (-n - 1) = n * (n + 1) by ring]

/-- Euler's pentagonal series at x is the theta series with parameters -x and -x². -/
private lemma theta_euler (x : ℂ) : ramanujanThetaRaw (-x) (-x ^ 2) = eulerFunction x := by
  rw [ramanujanThetaRaw, eulerFunction_eq_tsum_pentagonal]
  apply tsum_congr
  intro n
  have hA := twice_tri (-n)
  have hB := twice_tri n
  have hsum : ((tri (-n) + tri n : ℕ) : ℤ) = n * n := by push_cast; linarith
  have hexp : tri (-n) + 2 * tri n = pentagonal n := by
    zify
    linarith [two_mul_natCast_pentagonal n]
  have hsign : (-1 : ℂ) ^ (tri (-n) + tri n) = n.negOnePow := by
    rw [← Int.cast_negOnePow_natCast, hsum, Int.negOnePow_mul_self]
  rw [term_eq, neg_eq_neg_one_mul x, neg_eq_neg_one_mul (x ^ 2), mul_pow, mul_pow, ← pow_mul,
    mul_mul_mul_comm, ← pow_add, ← pow_add, hsign, hexp]

open Analysis.SpecialFunctions.JacobiTripleProduct in
private lemma psi_prod {q : ℂ} (h : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) = P (q ^ 4) (q ^ 4) * P (-q) (q ^ 2) := by
  by_cases hq : q = 0
  · subst q
    simpa [qPochhammerInfRaw, eulerFunction_eq_tprod h] using theta_euler 0
  have h₂ := norm_sq_lt_one h
  have h₄ : ‖q ^ 4‖ < 1 := by simpa [← pow_mul] using norm_sq_lt_one h₂
  -- The theta summand is q^(2n² - n), so the Jacobi parameters are q⁻¹ and q².
  obtain ⟨-, -, hj⟩ := jacobi_triple_product q⁻¹ (q ^ 2) (inv_ne_zero hq) h₂
  have hterm (n : ℤ) : ramanujanThetaTerm q (q ^ 3) n =
      q⁻¹ ^ n * (q ^ 2) ^ (n * n).toNat := by
    rw [term_eq, ← pow_mul, ← pow_add, ← pow_mul, ← zpow_natCast q, ← zpow_natCast q,
      inv_zpow', ← zpow_add₀ hq]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg (mul_self_nonneg n)]
    linarith [twice_tri n, twice_tri (-n)]
  simp only [ramanujanThetaRaw, hterm, hj, inv_inv]
  have hp := ((hasProd_qPochhammerInf (q ^ 4) (q ^ 4) h₄).mul
    (hasProd_qPochhammerInf (-q) (q ^ 4) h₄)).mul
      (hasProd_qPochhammerInf (-q * q ^ 2) (q ^ 4) h₄)
  have hs := split_prod (-q) (q ^ 2) h₂
  rw [show (q ^ 2) ^ 2 = q ^ 4 by ring] at hs
  rw [hs, ← mul_assoc]
  apply HasProd.tprod_eq
  apply hp.congr_fun
  intro n
  simp only [pow_add, pow_mul, neg_mul, sub_neg_eq_add]
  field_simp

end ramanujan_psi_f_chi_eq_qPochhammer

open ramanujan_psi_f_chi_eq_qPochhammer

/-- **Product forms of Ramanujan's theta functions $\psi$, $f$ and $\chi$.** Write
$(a; q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and $f_k = (q^k; q^k)_\infty$, and let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function. For every complex number $q$ with $|q| < 1$,
$f(q, q^3) = f_2^2 / f_1$, $f(q, -q^2) = f_2^3 / (f_1 f_4)$, $(-q; q^2)_\infty = f_2^2 / (f_1 f_4)$
and $(q; q^2)_\infty = f_1 / f_2$.

In Ramanujan's notation (Berndt, Part III, Chapter 16), with $\psi(q) = f(q, q^3)$,
$f(q) = f(q, -q^2)$ and $\chi(q) = (-q; q^2)_\infty$, these read $\psi(q) = f_2^2 / f_1$,
$f(q) = f_2^3 / (f_1 f_4)$, $\chi(q) = f_2^2 / (f_1 f_4)$ and $\chi(-q) = f_1 / f_2$.

Source: A. Vanitha, Nasser Abdo Saeed Bulkhali, and M. P. Chaudhary, *On a Ramanujan’s
Continued Fraction of Order Sixteen and New Eisenstein Series Identities*, INTEGERS 25 (2025),
Article A16, Lemma 1 (`integers-2025-A16-lem-1`). -/
public theorem ramanujan_psi_f_chi_eq_qPochhammer (q : ℂ) (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
        qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 / qPochhammerInfRaw q q ∧
      ramanujanThetaRaw q (-q ^ 2) =
        qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 3 /
          (qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4)) ∧
      qPochhammerInfRaw (-q) (q ^ 2) =
        qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 /
          (qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4)) ∧
      qPochhammerInfRaw q (q ^ 2) = qPochhammerInfRaw q q / qPochhammerInfRaw (q ^ 2) (q ^ 2) := by
  have h₂ := norm_sq_lt_one hq
  have h₄ : ‖q ^ 4‖ < 1 := by simpa [← pow_mul] using norm_sq_lt_one h₂
  have hs₁ := split_prod q q hq
  have hs₂ := split_prod (q ^ 2) (q ^ 2) h₂
  have hp := pair_prod q (q ^ 2) h₂
  rw [← sq] at hs₁
  rw [← sq, show (q ^ 2) ^ 2 = q ^ 4 by ring] at hs₂
  rw [show (q ^ 2) ^ 2 = q ^ 4 by ring] at hp
  -- Pair the two odd-power products and put the even factors back into the Euler products.
  have hχ : qPochhammerInfRaw (-q) (q ^ 2) *
      (qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4)) =
      qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 := by
    rw [hs₁]
    linear_combination qPochhammerInfRaw (q ^ 2) (q ^ 2) *
      (qPochhammerInfRaw (q ^ 4) (q ^ 4) * hp - hs₂)
  have hf : ramanujanThetaRaw q (-q ^ 2) =
      qPochhammerInfRaw (-q) (q ^ 2) * qPochhammerInfRaw (q ^ 2) (q ^ 2) := by
    have he := theta_euler (-q)
    rw [neg_neg, neg_sq, eulerFunction_eq_tprod (by simpa using hq)] at he
    have hs := split_prod (-q) (-q) (by simpa using hq)
    rw [neg_sq, neg_mul_neg, ← sq] at hs
    rw [he]
    simpa only [qPochhammerInfRaw, pow_succ' (-q)] using hs
  have h₁ne := diagonal_ne_zero hq
  have h₄ne := diagonal_ne_zero h₄
  refine ⟨?_, ?_, (eq_div_iff (mul_ne_zero h₁ne h₄ne)).2 hχ, ?_⟩
  · rw [psi_prod hq, eq_div_iff h₁ne]
    linear_combination hχ
  · rw [hf, eq_div_iff (mul_ne_zero h₁ne h₄ne)]
    linear_combination qPochhammerInfRaw (q ^ 2) (q ^ 2) * hχ
  · exact (eq_div_iff (diagonal_ne_zero h₂)).2 hs₁.symm

end MetaMathlibExt
