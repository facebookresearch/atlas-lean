/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CarlitzTypeQPolynomials
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Closed forms for extended Carlitz q-Bernoulli polynomials

The extended Carlitz polynomials admit an alternating coefficient formula and a binomial expansion
in their values at zero. These values satisfy a recurrence from degree two onwards.
-/

namespace MetaMathlibExt

open Finset

namespace extendedCarlitzBetaPoly_closed_forms

private theorem smul_add_smul_one_pow_apply
    (A : Module.End ℝ (ℕ → ℝ)) (u v : ℝ) (a : ℕ → ℝ) (n : ℕ) :
    ((u • A + v • 1) ^ n) a 0 =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (A ^ k) a 0 * u ^ k * v ^ (n - k) := by
  have hcomm : Commute (u • A) (v • (1 : Module.End ℝ (ℕ → ℝ))) := by
    change (u • A) * (v • 1) = (v • 1) * (u • A)
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_smul, mul_comm u v]
  rw [hcomm.add_pow, LinearMap.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun k _ => ?_
  simp only [smul_pow, one_pow, smul_mul_assoc, mul_smul_comm, mul_one, mul_apply_eq_comp,
    natCast_apply_eq_smul, ← Nat.cast_smul_eq_nsmul ℝ, map_smul, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

private theorem sum_choose_eval_zero {q : ℝ} (hq0 : 0 < q) {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}
    (hT : IsCarlitzTypeWith q T a) (n : ℕ) (x : ℝ) :
    T n x = ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) * T k 0 * q ^ ((k : ℝ) * x) * qBracket q x ^ (n - k) := by
  let S : Module.End ℝ (ℕ → ℝ) := LinearMap.funLeft ℝ ℝ Nat.succ
  have hS (k i : ℕ) : (S ^ k) a i = a (i + k) := by
    induction k generalizing i with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      change (S ^ k) a (i + 1) = a (i + (k + 1))
      rw [ih, Nat.add_right_comm]
      rfl
  let c : ℝ := (q - 1)⁻¹
  let D (u : ℝ) : Module.End ℝ (ℕ → ℝ) := (c * u) • S + (-c) • 1
  have hrpow (y : ℝ) (k : ℕ) : (q ^ y) ^ k = q ^ ((k : ℝ) * y) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le, mul_comm y]
  -- The normalized weighted forward difference realizes the alternating sum.
  have hD (n : ℕ) (y : ℝ) : (D (q ^ y) ^ n) a 0 = T n y := by
    simp only [D]
    rw [smul_add_smul_one_pow_apply, hT n y, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hc : c ^ k * c ^ (n - k) = ((q - 1) ^ n)⁻¹ := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk)), inv_pow]
    rw [hS, zero_add, mul_pow, hrpow, show -c = (-1 : ℝ) * c by ring, mul_pow, ← hc]
    ring
  have htranslate : D (q ^ x) = q ^ x • D 1 + qBracket q x • 1 := by
    simp only [D, mul_one, smul_add, smul_smul, add_assoc, ← add_smul]
    have hscalar : q ^ x * -c + qBracket q x = -c := by
      rw [qBracket, div_eq_mul_inv]
      change q ^ x * -c + (q ^ x - 1) * c = -c
      ring
    rw [hscalar, mul_comm c]
  have hzero (k : ℕ) : (D 1 ^ k) a 0 = T k 0 := by
    simpa only [Real.rpow_zero] using hD k 0
  rw [← hD n x, htranslate, smul_add_smul_one_pow_apply]
  simp only [hzero, hrpow]

end extendedCarlitzBetaPoly_closed_forms

/-- **Closed forms for the extended Carlitz $q$-Bernoulli polynomials.** Let $q > 0$ with
$q \ne 1$ be real, write $[x] = (q^x - 1)/(q - 1)$, let $r$ be a natural number, and let
$\beta_n^{(r)}(x)$ be the extended Carlitz $q$-Bernoulli polynomials. Put $a_k = (k + r)/[k + r]$
for natural $k$ with $k + r \ne 0$, and $a_0 = 1$ if $r = 0$. Then:
(i) for every natural $n$ and real $x$,
$\beta_n^{(r)}(x) = (q - 1)^{-n} \sum_{k=0}^{n} (-1)^{n-k} \binom{n}{k} a_k q^{kx}$;
(ii) for every natural $n$ and real $x$,
$\beta_n^{(r)}(x) = \sum_{k=0}^{n} \binom{n}{k} \beta_k^{(r)}(0) q^{kx} [x]^{n-k}$;
(iii) for every natural $n \ge 2$,
$q^r \sum_{j=0}^{n} \binom{n}{j} q^j \beta_j^{(r)}(0) = \beta_n^{(r)}(0)$.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.9
(`integers-2026-A85-prop-2-9`). -/
public theorem extendedCarlitzBetaPoly_closed_forms (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r : ℕ) :
    (∀ n x, extendedCarlitzBetaPoly q r n x = ((q - 1) ^ n)⁻¹ *
        ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
          (if k + r = 0 then 1 else ((k + r : ℕ) : ℝ) / qBracket q ((k + r : ℕ) : ℝ)) *
            q ^ ((k : ℝ) * x)) ∧
      (∀ n x, extendedCarlitzBetaPoly q r n x = ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * extendedCarlitzBetaPoly q r k 0 * q ^ ((k : ℝ) * x) *
          qBracket q x ^ (n - k)) ∧
      ∀ n, 2 ≤ n → q ^ r * ∑ j ∈ range (n + 1),
        (n.choose j : ℝ) * q ^ j * extendedCarlitzBetaPoly q r j 0 =
          extendedCarlitzBetaPoly q r n 0 := by
  have hcoeff (r : ℕ) : IsCarlitzTypeWith q (extendedCarlitzBetaPoly q r) fun k =>
      if k + r = 0 then 1 else ((k + r : ℕ) : ℝ) / qBracket q ((k + r : ℕ) : ℝ) := by
    induction r with
    | zero =>
      intro n x
      simp only [extendedCarlitzBetaPoly_zero, carlitzEtaPoly, Nat.add_zero]
    | succ r ih =>
      have hshift := (isCarlitzTypeWith_closure q hq0 hq1 _ _ ih).2.2.1
      intro n x
      rw [extendedCarlitzBetaPoly_succ]
      simpa only [Nat.add_assoc, Nat.add_comm 1 r] using hshift n x
  have hexpand := extendedCarlitzBetaPoly_closed_forms.sum_choose_eval_zero hq0 (hcoeff r)
  refine ⟨hcoeff r, hexpand, fun n hn => ?_⟩
  -- With a single summand at zero, the weighted power sum vanishes in degrees at least two.
  have hdiff := sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta q hq0 hq1 r n 1
  have hn0 : n ≠ 0 := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  simp only [sum_range_one, Nat.cast_zero, qBracket_zero, zero_pow hn0, zero_pow hn1,
    mul_zero, zero_add, mul_one, Nat.cast_one, eq_comm (a := (0 : ℝ)), sub_eq_zero] at hdiff
  rw [hexpand n 1, qBracket_one hq1] at hdiff
  simpa only [one_pow, mul_one, Real.rpow_natCast, mul_right_comm] using hdiff

end MetaMathlibExt
