/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FubiniNumber
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# The Alzer–Richards identity for Fubini numbers

The identity for Fubini numbers and alternating Stirling sums follows by extracting
coefficients of formal power series.
-/

open Finset PowerSeries

namespace MetaMathlibExt

namespace sum_fubiniNumber_mul_sum_alternatingStirling

private noncomputable def egfCoeff (r : ℕ) : ℚ⟦X⟧ →ₗ[ℚ] ℚ :=
  (r.factorial : ℚ) • coeff r

private theorem egfCoeff_C_mul (r : ℕ) (a : ℚ) (f : ℚ⟦X⟧) :
    egfCoeff r (C a * f) = a * egfCoeff r f := by
  simp [egfCoeff, mul_left_comm]

private theorem egfCoeff_natCast_mul (r a : ℕ) (f : ℚ⟦X⟧) :
    egfCoeff r ((a : ℚ⟦X⟧) * f) = (a : ℚ) * egfCoeff r f := by
  simpa using egfCoeff_C_mul r (a : ℚ) f

private theorem egfCoeff_mul_natCast (r a : ℕ) (f : ℚ⟦X⟧) :
    egfCoeff r (f * (a : ℚ⟦X⟧)) = (a : ℚ) * egfCoeff r f := by
  rw [mul_comm, egfCoeff_natCast_mul]

private theorem egfCoeff_mul (r : ℕ) (f g : ℚ⟦X⟧) :
    egfCoeff r (f * g) =
      ∑ k ∈ range (r + 1), (r.choose k : ℚ) * egfCoeff k f * egfCoeff (r - k) g := by
  simp only [egfCoeff, LinearMap.smul_apply, smul_eq_mul, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [Nat.cast_choose ℚ (Nat.le_of_lt_succ (mem_range.mp hk))]
  field_simp

private theorem egfCoeff_exp_pow (r j : ℕ) :
    egfCoeff r (exp ℚ ^ j) = (j : ℚ) ^ r := by
  simp only [egfCoeff, LinearMap.smul_apply, smul_eq_mul, exp_pow_eq_rescale_exp, coeff_rescale,
    coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
  field_simp

private noncomputable def q : ℚ⟦X⟧ := exp ℚ - 1

private theorem egfCoeff_q_pow (r j : ℕ) :
    egfCoeff r (q ^ j) = (Nat.stirlingSecond r j : ℚ) * j.factorial := by
  rw [q, sub_eq_add_neg, add_pow, map_sum]
  have h : (Nat.stirlingSecond r j : ℚ) * j.factorial =
      ∑ i ∈ range (j + 1), (-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) * (i : ℚ) ^ r := by
    exact_mod_cast stirlingSecond_mul_factorial_eq_sum r j
  rw [h]
  refine sum_congr rfl fun i _ => ?_
  rw [show (-1 : ℚ⟦X⟧) = C (-1) by simp, ← map_pow, mul_comm (exp ℚ ^ i), mul_assoc,
    egfCoeff_C_mul, egfCoeff_mul_natCast, egfCoeff_exp_pow]
  ring

private theorem egfCoeff_one_sub_q_pow (A : ℕ → ℕ → ℤ)
    (hA : ∀ r k, A r k = ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j.factorial : ℤ) * (Nat.stirlingSecond r j : ℤ))
    (r k : ℕ) :
    egfCoeff r ((1 - q) ^ k) = (A r k : ℚ) := by
  rw [hA, Int.cast_sum, sub_eq_neg_add, add_pow, map_sum]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, neg_eq_neg_one_mul, mul_pow, show (-1 : ℚ⟦X⟧) = C (-1) by simp, ← map_pow,
    mul_assoc, egfCoeff_C_mul, egfCoeff_mul_natCast, egfCoeff_q_pow]
  ring

private theorem egfCoeff_geom_sum {r n : ℕ} (hr : r ≤ n) :
    egfCoeff r (∑ j ∈ range (n + 1), q ^ j) = (fubiniNumber r : ℚ) := by
  rw [map_sum, fubiniNumber_eq_sum, Nat.cast_sum]
  simp only [egfCoeff_q_pow, Nat.cast_mul]
  symm
  refine sum_subset (range_mono (Nat.succ_le_succ hr)) fun j _ hj => ?_
  rw [Nat.stirlingSecond_eq_zero_of_lt (by simpa using hj), Nat.cast_zero, zero_mul]

-- The term of index zero is 1. The remaining terms each contain a factor of p.
private theorem add_one_pow_eq (p : ℚ⟦X⟧) (n : ℕ) :
    (p + 1) ^ (n + 1) =
      1 + p * ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℚ⟦X⟧) * p ^ k := by
  rw [add_pow, sum_range_succ', mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [pow_succ]
  ac_rfl

private theorem egfCoeff_identity (n : ℕ) :
    egfCoeff n ((∑ j ∈ range (n + 1), q ^ j) * (1 - q + 1) ^ (n + 1)) =
      (fubiniNumber n : ℚ) + egfCoeff n
        (∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℚ⟦X⟧) * (1 - q) ^ k) := by
  let B := ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℚ⟦X⟧) * (1 - q) ^ k
  -- The remainder of the finite geometric sum starts above degree n.
  have hB : egfCoeff n (q ^ (n + 1) * B) = 0 := by
    have hq : (n + 1 : ℕ) ≤ (q ^ (n + 1)).order :=
      le_order_pow_of_constantCoeff_eq_zero _ (by simp [q])
    rw [egfCoeff, LinearMap.smul_apply, smul_eq_mul, mul_comm _ B,
      coeff_mul_of_lt_order ((by exact_mod_cast Nat.lt_succ_self n :
        (n : ℕ∞) < (n + 1 : ℕ)).trans_le hq), mul_zero]
  change _ = (fubiniNumber n : ℚ) + egfCoeff n B
  rw [add_one_pow_eq, ← show B = _ from rfl, mul_add, mul_one, ← mul_assoc,
    geom_sum_mul_neg, sub_mul, one_mul, map_add, map_sub, hB, sub_zero,
    egfCoeff_geom_sum le_rfl]

end sum_fubiniNumber_mul_sum_alternatingStirling

-- Keep the source's lower bound on n. The coefficient proof also works at n = 0.
set_option linter.unusedVariables false in
open sum_fubiniNumber_mul_sum_alternatingStirling in
/-- **Alzer–Richards identity for Fubini numbers.** Let $n \ge 1$ be an integer, let $a(k)$ be
the $k$-th Fubini (ordered Bell) number and $S(r, j)$ the Stirling numbers of the second kind,
and for integers $r, k \ge 0$ let
$A(r, k) = \sum_{j=0}^{k} (-1)^j \binom{k}{j} j! \, S(r, j)$. Then
$$
\sum_{k=0}^{n-1} \binom{n}{k} a(k) \sum_{\nu=0}^{n+1} \binom{n+1}{\nu} A(n-k, \nu) +
(2^{n+1} - 1) a(n) = \sum_{k=0}^{n} \binom{n+1}{k+1} A(n, k).
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 7, Equation (8). -/
public theorem sum_fubiniNumber_mul_sum_alternatingStirling {n : ℕ} (hn : 1 ≤ n)
    (A : ℕ → ℕ → ℤ)
    (hA : ∀ r k, A r k = ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j.factorial : ℤ) * (Nat.stirlingSecond r j : ℤ)) :
    ∑ k ∈ range n, (n.choose k : ℤ) * fubiniNumber k *
        ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℤ) * A (n - k) ν +
      (2 ^ (n + 1) - 1) * fubiniNumber n =
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * A n k := by
  have hpow : ∀ r k, egfCoeff r ((1 - q) ^ k) = (A r k : ℚ) :=
    egfCoeff_one_sub_q_pow A hA
  have hfull : (∑ k ∈ range (n + 1), (n.choose k : ℤ) * fubiniNumber k *
      ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℤ) * A (n - k) ν) =
      (fubiniNumber n : ℤ) + ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * A n k := by
    have hbin (r : ℕ) :
        egfCoeff r ((1 - q + 1) ^ (n + 1)) =
          ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℚ) * A r ν := by
      rw [add_pow, map_sum]
      simp only [one_pow, mul_one, egfCoeff_mul_natCast, hpow]
    have hf (k : ℕ) (hk : k ∈ range (n + 1)) :
        egfCoeff k (∑ j ∈ range (n + 1), q ^ j) = (fubiniNumber k : ℚ) :=
      egfCoeff_geom_sum (Nat.le_of_lt_succ (mem_range.mp hk))
    have h := egfCoeff_identity n
    rw [egfCoeff_mul, sum_congr rfl (fun k hk => by rw [hf k hk, hbin])] at h
    simp only [map_sum, egfCoeff_natCast_mul, hpow] at h
    exact_mod_cast h
  have hA0 (k : ℕ) : A 0 k = 1 := by
    rw [hA, sum_range_succ']
    simp
  rw [sum_range_succ] at hfull
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, hA0, mul_one,
    ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat] at hfull
  calc
    _ = (∑ k ∈ range n, (n.choose k : ℤ) * fubiniNumber k *
          ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℤ) * A (n - k) ν) +
        (fubiniNumber n : ℤ) * 2 ^ (n + 1) - fubiniNumber n := by ring
    _ = _ := by rw [hfull, add_sub_cancel_left]

end MetaMathlibExt
