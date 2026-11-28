/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Ring.Parity
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import all MathlibExt.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
import all MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity
import all MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum

/-!
# Even-index Catalan convolution with Lucas sequences

For every integer `p` and natural number `n`, the rational sum of `C_{2(n-k)} C_{2k} U_k V_{n-k}`
over `0 ≤ k ≤ n`, with `U = U(p, -1)`, `V = V(p, -1)` and `C` the Catalan numbers, is `4^n C_n U_n`.
Reflection removes the Lucas factors from the sum, leaving `U_n` times a Catalan convolution.
The square of the even part of the Catalan generating series `P(X)` satisfies the same equation
as `P(4X²)`, which evaluates that convolution. The Catalan successor relation gives the
published normalization of the right-hand side.

## References

* John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
  Sequences*, The Fibonacci Quarterly 62 (2024), no. 1, 57–64, Proposition 2.4 (the identity)
  and Section 2 (the symmetry argument).
* Vladimir V. Kruchinin and Maria Y. Perminova, *Identities and Hadamard Product of the Generalized
  Fibonacci, Lucas, Catalan, and Harmonic Numbers*, Journal of Integer Sequences 28 (2025),
  Article 25.8.8, 1–17, Proposition 1 (Lucas addition) and Theorem 2 (symmetric weights).
* The formal proof reuses `sum_mul_lucasU_mul_lucasV_of_symm` from
  `MathlibExt.NumberTheory.Recurrences.LucasAlternatingSquaredBinomialSum`,
  `generalizedCatalanSchroeder_catalan_equation` from
  `MathlibExt.Combinatorics.Enumerative.GeneralizedCatalanSchroeder`, and `touchard_catalan_rec`
  from `MathlibExt.Combinatorics.Enumerative.TouchardCatalanIdentity`.
-/

namespace MetaMathlibExt

open Finset PowerSeries

/-- The scalar convolution is the coefficient of `X^(2*n)` in the square of the even part
of the Catalan generating series. -/
private theorem sum_catalan_even_mul (n : ℕ) :
    ∑ k ∈ range (n + 1), (catalan (2 * (n - k)) : ℚ) * catalan (2 * k) =
      (4 : ℚ) ^ n * catalan n := by
  let P : PowerSeries ℚ := mk fun j => (catalan j : ℚ)
  let A : PowerSeries ℚ := mk fun j => (catalan (2 * j) : ℚ)
  let ex := expand (R := ℚ) 2 two_ne_zero
  let E := ex A
  let O := P - E
  let Q := ex (rescale 4 P)
  have hP : P = 1 + X * P ^ 2 := generalizedCatalanSchroeder_catalan_equation ℚ
  have hEven : P + rescale (-1) P = 2 * E := by
    apply PowerSeries.ext
    intro j
    rw [map_add, coeff_rescale, coeff_ofNat_mul]
    by_cases hj : 2 ∣ j
    · obtain ⟨i, rfl⟩ := hj
      dsimp only [E, ex]
      rw [coeff_expand_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      simpa only [A, P, coeff_mk] using (two_mul (catalan (2 * i) : ℚ)).symm
    · have ho : Odd j := Nat.not_even_iff_odd.mp (fun he => hj (even_iff_two_dvd.mp he))
      rw [show coeff j E = 0 from coeff_expand_of_not_dvd 2 two_ne_zero A hj,
        ho.neg_one_pow, neg_one_mul, add_neg_cancel, mul_zero]
  have hplus : E + O = 1 + X * (E + O) ^ 2 := by
    simpa only [show E + O = P by dsimp [O]; ring] using hP
  have hminus : E - O = 1 - X * (E - O) ^ 2 := by
    have hEO : rescale (-1) P = E - O := by
      dsimp [O]
      linear_combination hEven
    simpa only [map_add, map_one, map_mul, map_pow, rescale_neg_one_X, neg_mul, ← sub_eq_add_neg,
      hEO] using congrArg (rescale (-1 : ℚ)) hP
  have htwo : IsUnit (2 : PowerSeries ℚ) := by
    rw [isUnit_iff_constantCoeff, map_ofNat]
    norm_num
  have hE : E = 1 + 2 * X * E * O := by
    apply htwo.mul_left_cancel
    linear_combination hplus + hminus
  have hO : O = X * (E ^ 2 + O ^ 2) := by
    apply htwo.mul_left_cancel
    linear_combination hplus - hminus
  have hsq : (E - 2 * X * E * O) ^ 2 = 1 := by
    rw [show E - 2 * X * E * O = 1 by linear_combination hE, one_pow]
  have hEE : E ^ 2 = 1 + 4 * X ^ 2 * (E ^ 2) ^ 2 := by
    linear_combination hsq + 4 * X * E ^ 2 * hO
  have hQ : Q = 1 + 4 * X ^ 2 * Q ^ 2 := by
    simpa only [Q, ex, map_add, map_one, map_mul, map_pow, rescale_X, expand_C, expand_X,
      map_ofNat] using congrArg (fun f => ex (rescale 4 f)) hP
  -- Subtracting the two equations gives a factor with constant coefficient 1.
  have heq : E ^ 2 = Q := by
    have hu : IsUnit (1 - 4 * X ^ 2 * (E ^ 2 + Q)) := by
      rw [isUnit_iff_constantCoeff]
      simp
    apply sub_eq_zero.mp
    apply hu.mul_right_eq_zero.mp
    linear_combination hEE - hQ
  have hcoeff := congrArg (coeff (2 * n)) heq
  change coeff (2 * n) (ex A ^ 2) = coeff (2 * n) (ex (rescale 4 P)) at hcoeff
  rw [← map_pow] at hcoeff
  dsimp only [ex] at hcoeff
  simp only [coeff_expand_mul, coeff_rescale, P, coeff_mk] at hcoeff
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simpa only [A, coeff_mk, mul_comm] using hcoeff

-- Keep the nonzero proofs in the Lucas parameters inline, as in the wanted statement.
set_option backward.proofsInPublic true in
/-- **Even-index Catalan convolution with Lucas sequences.** Let $p$ be an integer, let $U_n$
and $V_n$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so $U_0 = 0$, $U_1 = 1$, $V_0 = 2$,
$V_1 = p$ and both satisfy $X_{j+2} = p X_{j+1} + X_j$, and let $C_j$ be the $j$-th Catalan
number. Then for every natural number $n$, in the rationals,
$$\sum_{k=0}^{n} C_{2n-2k} C_{2k} U_k V_{n-k} =
\frac{2^{2n}}{2} \cdot \frac{n+2}{2n+1} C_{n+1} U_n.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.4. -/
public theorem lucasU_lucasV_sum_catalan_even (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (catalan (2 * n - 2 * k) * catalan (2 * k) : ℚ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      (2 : ℚ) ^ (2 * n) / 2 * ((n + 2 : ℚ) / (2 * n + 1)) * catalan (n + 1) *
        lucasU ⟨p, -1, by decide⟩ n := by
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  let a (k : ℕ) : ℤ := (catalan (2 * n - 2 * k) : ℤ) * catalan (2 * k)
  have ha (k : ℕ) (hk : k ≤ n) : a (n - k) = a k := by
    simp only [a, ← Nat.mul_sub_left_distrib, Nat.sub_sub_self hk]
    exact mul_comm _ _
  have hweighted : ∑ k ∈ range (n + 1), a k * lucasU P k * lucasV P (n - k) =
      (∑ k ∈ range (n + 1), a k) * lucasU P n := by
    rw [← sum_range_reflect]
    refine (sum_congr rfl fun k hk => ?_).trans
      (lucasU_lucasV_sum_choose_sq_alternating.sum_mul_lucasU_mul_lucasV_of_symm P n a ha)
    have hkn := mem_range_succ_iff.mp hk
    rw [Nat.add_sub_cancel, Nat.sub_sub_self hkn, ha k hkn]
  have hweightedQ := congrArg (Int.castRingHom ℚ) hweighted
  simp only [Int.coe_castRingHom, a, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hweightedQ
  have hrec : ((n : ℚ) + 2) * catalan (n + 1) = 2 * (2 * (n : ℚ) + 1) * catalan n := by
    exact_mod_cast touchard_catalan_rec n
  have hratio : ((n + 2 : ℚ) / (2 * n + 1)) * catalan (n + 1) = 2 * (catalan n : ℚ) := by
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
    linear_combination hrec
  change _ = (2 : ℚ) ^ (2 * n) / 2 * ((n + 2 : ℚ) / (2 * n + 1)) * catalan (n + 1) *
    lucasU P n
  rw [hweightedQ]
  simp_rw [← Nat.mul_sub_left_distrib, sum_catalan_even_mul]
  rw [mul_assoc ((2 : ℚ) ^ (2 * n) / 2), hratio]
  rw [pow_mul, show (2 : ℚ) ^ 2 = 4 by norm_num]
  ring

end MetaMathlibExt
