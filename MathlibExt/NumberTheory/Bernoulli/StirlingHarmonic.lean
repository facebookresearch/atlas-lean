/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.BernoulliPolynomials
import MathlibExt.Combinatorics.Enumerative.StirlingDescPochhammer

/-!
# Bernoulli numbers from Stirling and harmonic numbers

We prove Kargın and Mutluer's identity for the harmonic-weighted convolution of
Stirling numbers of both kinds by taking coefficients of a sum of falling factorials.
-/

namespace MetaMathlibExt

open Finset

namespace sum_stirling_harmonic_eq_bernoulli

open Polynomial

private noncomputable def harmonicStirlingPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C ((Nat.stirlingSecond n k : ℚ) * harmonic k) * descPochhammer ℚ k

private noncomputable def powerSumPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C ((Nat.stirlingSecond n k : ℚ) / ((k : ℚ) + 1)) *
    descPochhammer ℚ (k + 1)

private lemma eval_descPochhammer_add_one (k m : ℕ) :
    (descPochhammer ℚ (k + 1)).eval ((m : ℚ) + 1) =
      (descPochhammer ℚ (k + 1)).eval (m : ℚ) +
      ((k : ℚ) + 1) * (descPochhammer ℚ k).eval (m : ℚ) := by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_eval]
  simp only [eval_mul, eval_X, eval_comp, eval_sub, eval_one, add_sub_cancel_right]
  ring

-- The discrete antiderivative of a falling factorial has zero constant term.
private lemma sum_eval_descPochhammer (k m : ℕ) :
    (∑ i ∈ range m, (descPochhammer ℚ k).eval (i : ℚ)) =
      (descPochhammer ℚ (k + 1)).eval (m : ℚ) / ((k : ℚ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, Nat.cast_succ, eval_descPochhammer_add_one, add_div]
    congr 1
    apply (eq_div_iff (by positivity)).mpr
    ring

private lemma powerSumPoly_eq (n : ℕ) :
    powerSumPoly n =
      C (((n : ℚ) + 1)⁻¹) * (Polynomial.bernoulli (n + 1) - C (_root_.bernoulli (n + 1))) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf := Set.infinite_range_of_injective (Nat.cast_injective (R := ℚ))
  refine hinf.mono ?_
  rintro _ ⟨m, rfl⟩
  simp only [Set.mem_ofPred_eq, powerSumPoly, eval_finsetSum, eval_mul, eval_C, eval_sub]
  rw [← Polynomial.sum_range_pow_eq_bernoulli_sub, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]
  calc
    _ = ∑ k ∈ range (n + 1), ∑ i ∈ range m,
        (Nat.stirlingSecond n k : ℚ) * (descPochhammer ℚ k).eval (i : ℚ) := by
      refine sum_congr rfl fun k _ => ?_
      rw [← mul_sum, sum_eval_descPochhammer]
      ring
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      simp only [descPochhammer_eval_eq_descFactorial]
      exact_mod_cast (Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i n).symm

private lemma harmonicStirlingPoly_succ (n : ℕ) :
    harmonicStirlingPoly (n + 1) = X * harmonicStirlingPoly n + powerSumPoly n := by
  let g (k : ℕ) :=
    C ((k : ℚ) * Nat.stirlingSecond n k * harmonic k) * descPochhammer ℚ k
  have hshift : ∑ k ∈ range (n + 1), g (k + 1) = ∑ k ∈ range (n + 1), g k := by
    have h := (sum_range_succ' g (n + 1)).symm.trans (sum_range_succ g (n + 1))
    simpa [g, Nat.stirlingSecond_eq_zero_of_lt n.lt_succ_self] using h
  have hstep (k : ℕ) : (Nat.stirlingSecond (n + 1) (k + 1) : ℚ) =
      ((k + 1 : ℕ) : ℚ) * Nat.stirlingSecond n (k + 1) + Nat.stirlingSecond n k := by
    rw [Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul]
  unfold harmonicStirlingPoly powerSumPoly
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, map_zero, add_zero,
    hstep, add_mul, map_add, sum_add_distrib]
  change (∑ k ∈ range (n + 1), g (k + 1)) + _ = _
  rw [hshift, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  dsimp [g]
  rw [harmonic_succ, mul_add, map_add, add_mul, div_eq_mul_inv]
  simp only [descPochhammer_succ_right, ← C_eq_natCast, Nat.cast_succ, map_mul]
  ring

private lemma powerSumPoly_coeff (n j : ℕ) (hj : 0 < j) (hjn : j ≤ n) :
    (powerSumPoly n).coeff j =
      (n.choose j : ℚ) * _root_.bernoulli (n + 1 - j) / ((n : ℚ) + 1 - j) := by
  have hj' : j ≠ 0 := hj.ne'
  have hjn' : j ≤ n + 1 := by omega
  have hchoose : (n.choose j : ℚ) * ((n : ℚ) + 1) =
      ((n + 1).choose j : ℚ) * ((n : ℚ) + 1 - j) := by
    simpa only [Nat.cast_mul, Nat.cast_sub hjn', Nat.cast_succ] using
      congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq n j)
  have hden : (n : ℚ) + 1 - j ≠ 0 := by
    rw [← Nat.cast_succ, ← Nat.cast_sub hjn']
    exact_mod_cast (show n + 1 - j ≠ 0 by omega)
  rw [powerSumPoly_eq, coeff_C_mul, coeff_sub, coeff_C, ite_eq_right hj', sub_zero,
    Polynomial.coeff_bernoulli, ite_eq_left hjn']
  field_simp
  linear_combination -_root_.bernoulli (n + 1 - j) * hchoose

private lemma harmonicStirlingPoly_coeff_zero (n : ℕ) :
    (harmonicStirlingPoly n).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp only [harmonicStirlingPoly, eval_finsetSum, eval_mul, eval_C, descPochhammer_eval_zero]
  exact sum_eq_zero fun k _ => by split <;> simp_all

private lemma harmonicStirlingPoly_coeff (n j : ℕ) (hjn : j < n) :
    (harmonicStirlingPoly n).coeff j =
      ((n.choose j : ℚ) - 1) * _root_.bernoulli (n - j) / ((n : ℚ) - j) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [harmonicStirlingPoly_coeff_zero]
    | succ j =>
      rw [harmonicStirlingPoly_succ, coeff_add, coeff_X_mul,
        ih j (by omega), powerSumPoly_coeff n (j + 1) (by omega) (by omega)]
      rw [Nat.choose_succ_succ, Nat.cast_add (n.choose j) _, Nat.add_sub_add_right]
      simp only [Nat.cast_succ]
      rw [show (n : ℚ) + 1 - ((j : ℚ) + 1) = n - j by ring]
      ring

private lemma coeff_descPochhammer (k j : ℕ) :
    (descPochhammer ℚ k).coeff j =
      (-1 : ℚ) ^ (k - j) * (Nat.stirlingFirst k j : ℚ) := by
  have hcoeff : (descPochhammer ℤ k).coeff j = signedStirlingFirst k j := by
    by_cases hj : j ≤ k
    · rw [descPochhammer_eq_sum_signedStirlingFirst, finsetSum_coeff]
      simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
      simp [hj]
    · rw [coeff_eq_zero_of_natDegree_lt (by simpa using Nat.lt_of_not_ge hj),
        signedStirlingFirst_eq_zero_of_lt (Nat.lt_of_not_ge hj)]
  rw [← descPochhammer_map (Int.castRingHom ℚ), coeff_map, hcoeff]
  simp [signedStirlingFirst_apply]

private lemma harmonicStirlingPoly_coeff_eq_sum (n j : ℕ) :
    (harmonicStirlingPoly n).coeff j =
      ∑ k ∈ Icc j n, (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond n k : ℚ) *
        (Nat.stirlingFirst k j : ℚ) * harmonic k := by
  simp only [harmonicStirlingPoly, finsetSum_coeff, coeff_C_mul, coeff_descPochhammer]
  symm
  refine (sum_congr rfl (fun k _ => ?_)).trans (sum_subset ?_ ?_)
  · ring
  · intro k hk
    exact mem_range_succ_iff.mpr (mem_Icc.mp hk).2
  · intro k hk hki
    have hkj : k < j := by
      have hkn := mem_range_succ_iff.mp hk
      simp only [mem_Icc, hkn, and_true] at hki
      omega
    simp [Nat.stirlingFirst_eq_zero_of_lt hkj]

end sum_stirling_harmonic_eq_bernoulli

/--
**Bernoulli numbers from Stirling and harmonic numbers.** Let $j < n$ be natural numbers. Write
${n \brace k}$ for the Stirling numbers of the second kind, ${k \brack j}$ for the unsigned
Stirling numbers of the first kind (the number of permutations of $k$ elements with exactly $j$
cycles), $H_k = \sum_{i=1}^{k} 1/i$ for the harmonic numbers (so $H_0 = 0$), and $B_m$ for the
Bernoulli numbers, normalized so that $B_1 = -1/2$. Then, in the rational numbers,

$$
\sum_{k=j}^{n} (-1)^{k-j} {n \brace k} {k \brack j} H_k
= \left(\binom{n}{j} - 1\right) \frac{B_{n-j}}{n-j}.
$$

The paper also covers the diagonal case $n = j$, reading the right-hand side as a limit (both
sides are then $H_j$); that case is not included here.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Theorem 1,
equation (5).
-/
public theorem sum_stirling_harmonic_eq_bernoulli (n j : ℕ) (hjn : j < n) :
    (∑ k ∈ Finset.Icc j n,
      (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond n k : ℚ) *
        (Nat.stirlingFirst k j : ℚ) * harmonic k) =
      ((n.choose j : ℚ) - 1) * bernoulli (n - j) / (n - j : ℚ) := by
  rw [← sum_stirling_harmonic_eq_bernoulli.harmonicStirlingPoly_coeff_eq_sum,
    sum_stirling_harmonic_eq_bernoulli.harmonicStirlingPoly_coeff n j hjn]

end MetaMathlibExt
