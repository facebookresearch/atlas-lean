/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliPoly
import MathlibExt.NumberTheory.Bernoulli.BernoulliStirlingSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sums of Bernoulli numbers via poly-Bernoulli polynomials

We use the Stirling recurrence and Pascal's identity to compute the change in the
poly-Bernoulli polynomial between zero and one, without analytic generating functions.
-/

namespace MetaMathlibExt

open Finset

namespace sum_bernoulli_eq_polyBernoulli

private def binomialTransform (n : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range (n + 1), (n.choose i : ℚ) * f i

private lemma binomialTransform_succ (n : ℕ) (f : ℕ → ℚ) :
    binomialTransform (n + 1) f = binomialTransform n f +
      binomialTransform n (fun i => f (i + 1)) := by
  have hshift : (∑ i ∈ range (n + 1), (n.choose (i + 1) : ℚ) * f (i + 1)) + f 0 =
      binomialTransform n f := by
    have h := (sum_range_succ' (fun i => (n.choose i : ℚ) * f i) (n + 1)).symm.trans
      (sum_range_succ (fun i => (n.choose i : ℚ) * f i) (n + 1))
    simpa [binomialTransform, Nat.choose_eq_zero_of_lt n.lt_succ_self] using h
  unfold binomialTransform
  rw [sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.choose_succ_succ,
    Nat.cast_add, add_mul, sum_add_distrib]
  rw [add_assoc, hshift, add_comm]
  rfl

private lemma binomialTransform_sub (n : ℕ) (f g : ℕ → ℚ) :
    binomialTransform n (fun i => f i - g i) = binomialTransform n f - binomialTransform n g := by
  simp only [binomialTransform, mul_sub, sum_sub_distrib]

private lemma binomialTransform_mul (n : ℕ) (f : ℕ → ℚ) (c : ℚ) :
    binomialTransform n (fun i => c * f i) = c * binomialTransform n f := by
  simp only [binomialTransform, mul_left_comm _ c, mul_sum]

-- These are the exponential-series coefficients of `(1 - exp(-t))^k`,
-- with the factorials cleared.
private def signedStirling (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * ((-1 : ℚ) ^ k * (k.factorial : ℚ) * (Nat.stirlingSecond n k : ℚ))

private lemma signedStirling_eq_zero {n k : ℕ} (h : n < k) : signedStirling n k = 0 := by
  simp [signedStirling, Nat.stirlingSecond_eq_zero_of_lt h]

private lemma signedStirling_zero_left (k : ℕ) : signedStirling 0 (k + 1) = 0 :=
  signedStirling_eq_zero (Nat.zero_lt_succ k)

private lemma signedStirling_zero_zero : signedStirling 0 0 = 1 := by simp [signedStirling]

private lemma signedStirling_succ_zero (n : ℕ) : signedStirling (n + 1) 0 = 0 := by
  simp [signedStirling]

private lemma signedStirling_succ_succ (n k : ℕ) :
    signedStirling (n + 1) (k + 1) = ((k : ℚ) + 1) *
      (signedStirling n k - signedStirling n (k + 1)) := by
  unfold signedStirling
  rw [Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
  push_cast
  rw [pow_succ (-1 : ℚ) n, pow_succ (-1 : ℚ) k]
  ring

private lemma binomialTransform_stirling_zero (n : ℕ) :
    binomialTransform n (fun i => signedStirling i 0) = 1 := by
  unfold binomialTransform
  rw [sum_eq_single 0]
  · simp [signedStirling_zero_zero]
  · rintro (_ | i) _ hi
    · contradiction
    · simp [signedStirling_succ_zero]
  · simp

-- This is the coefficient version of `(exp(t) - 1) * (1 - exp(-t))^k
-- = exp(t) * (1 - exp(-t))^(k+1)`.
private lemma binomialTransform_stirling_succ (n k : ℕ) :
    binomialTransform n (fun i => signedStirling i (k + 1)) =
      binomialTransform n (fun i => signedStirling i k) - signedStirling n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [binomialTransform, signedStirling_zero_zero, signedStirling_zero_left]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [binomialTransform_stirling_zero, signedStirling_succ_zero, sub_zero]
      rw [binomialTransform_succ]
      simp only [signedStirling_succ_succ, Nat.cast_zero, zero_add, one_mul,
        binomialTransform_sub, binomialTransform_stirling_zero, add_sub_cancel]
    | succ k =>
      simp only [binomialTransform_succ, signedStirling_succ_succ, binomialTransform_mul,
        binomialTransform_sub]
      rw [ih (k + 1), ih k]
      push_cast
      ring

private lemma sum_signedStirling_extend {n N : ℕ} (hn : n ≤ N) (s : ℕ) (w : ℕ → ℚ) :
    (∑ k ∈ range (n + 1), signedStirling n (k + s) / w k) =
      ∑ k ∈ range (N + 1), signedStirling n (k + s) / w k := by
  apply sum_subset (range_mono (Nat.succ_le_succ hn))
  intro k _ hk
  rw [mem_range, not_lt] at hk
  rw [signedStirling_eq_zero (show n < k + s by omega), zero_div]

private lemma binomialTransform_stirlingSum (n s : ℕ) (w : ℕ → ℚ) :
    binomialTransform n (fun i => ∑ k ∈ range (i + 1), signedStirling i (k + s) / w k) =
      ∑ k ∈ range (n + 1), binomialTransform n (fun i => signedStirling i (k + s)) / w k := by
  unfold binomialTransform
  calc
    _ = ∑ i ∈ range (n + 1), (n.choose i : ℚ) *
        ∑ k ∈ range (n + 1), signedStirling i (k + s) / w k := by
      refine sum_congr rfl fun i hi => ?_
      exact congrArg ((n.choose i : ℚ) * ·)
        (sum_signedStirling_extend (Nat.lt_succ_iff.mp (mem_range.mp hi)) s w)
    _ = _ := by simpa only [mul_sum, mul_div_assoc, sum_div] using
      (sum_comm (s := range (n + 1)) (t := range (n + 1))
        (f := fun i k => (n.choose i : ℚ) * (signedStirling i (k + s) / w k)))

private lemma polyBernoulli_two_eq (n : ℕ) :
    polyBernoulli n 2 = ∑ k ∈ range (n + 1), signedStirling n k / ((k : ℚ) + 1) ^ 2 := by
  rw [polyBernoulli, mul_sum]
  simp only [signedStirling, Nat.cast_add, Nat.cast_one, zpow_ofNat, mul_div_assoc]

-- Coefficients of the formal dilogarithm at `1 - exp(-t)`.
private def dilogCoeff (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), signedStirling n (k + 1) / ((k : ℚ) + 1) ^ 2

private lemma polyBernoulliPoly_one_sub (n : ℕ) :
    polyBernoulliPoly n 2 1 - polyBernoulli n 2 = binomialTransform n dilogCoeff := by
  have hone : polyBernoulliPoly n 2 1 = binomialTransform n (fun i => polyBernoulli i 2) := by
    simp only [polyBernoulliPoly, binomialTransform, one_pow, mul_one]
  rw [hone, polyBernoulli_two_eq n]
  simp only [polyBernoulli_two_eq]
  unfold dilogCoeff
  change (binomialTransform n (fun i =>
      ∑ k ∈ range (i + 1), signedStirling i (k + 0) / ((k : ℚ) + 1) ^ 2)) - _ = _
  rw [binomialTransform_stirlingSum n 0, binomialTransform_stirlingSum n 1, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.add_zero, binomialTransform_stirling_succ, sub_div]

private def logCoeff (n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), signedStirling n (k + 1) / ((k : ℚ) + 1)

private lemma logCoeff_eq (n : ℕ) : logCoeff n = if n = 1 then 1 else 0 := by
  cases n with
  | zero => simp [logCoeff, signedStirling_zero_left]
  | succ n =>
    calc
      logCoeff (n + 1) = ∑ k ∈ range (n + 1),
          (signedStirling n k - signedStirling n (k + 1)) := by
        unfold logCoeff
        rw [sum_range_succ, signedStirling_eq_zero (n + 1).lt_succ_self, zero_div, add_zero]
        refine sum_congr rfl fun k _ => ?_
        rw [signedStirling_succ_succ, mul_div_cancel_left₀ _ (by positivity)]
      _ = signedStirling n 0 := by
        rw [sum_sub_distrib]
        have h := (sum_range_succ' (signedStirling n) (n + 1)).symm.trans
          (sum_range_succ (signedStirling n) (n + 1))
        rw [signedStirling_eq_zero n.lt_succ_self, add_zero] at h
        rw [← h]
        ring
      _ = _ := by cases n <;> simp [signedStirling_zero_zero, signedStirling_succ_zero]

private lemma dilogCoeff_succ (n : ℕ) : dilogCoeff (n + 1) = bernoulli n := by
  have hBernoulli : (∑ k ∈ range (n + 1), signedStirling n k / ((k : ℚ) + 1)) =
      bernoulli' n := by
    rw [bernoulli'_eq_bernoulli,
      MathlibExt.NumberTheory.BernoulliSecondKindWanted.bernoulli_eq_sum_stirlingSecond, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    unfold signedStirling
    ring
  calc
    dilogCoeff (n + 1) = ∑ k ∈ range (n + 1), (signedStirling n k / ((k : ℚ) + 1) -
        signedStirling n (k + 1) / ((k : ℚ) + 1)) := by
      unfold dilogCoeff
      rw [sum_range_succ, signedStirling_eq_zero (n + 1).lt_succ_self, zero_div, add_zero]
      refine sum_congr rfl fun k _ => ?_
      rw [signedStirling_succ_succ, ← sub_div]
      field_simp
    _ = bernoulli' n - (if n = 1 then 1 else 0) := by
      rw [sum_sub_distrib, hBernoulli, ← logCoeff, logCoeff_eq]
    _ = bernoulli n := by
      by_cases hn : n = 1
      · subst n
        norm_num [bernoulli'_one]
      · simp [hn, bernoulli_eq_bernoulli'_of_ne_one hn]

private lemma binomialTransform_bernoulli (n : ℕ) :
    binomialTransform n bernoulli = bernoulli n + (if n = 1 then 1 else 0) := by
  rw [binomialTransform, sum_range_succ, sum_bernoulli]
  simp [add_comm]

private lemma binomialTransform_dilogCoeff (n : ℕ) :
    binomialTransform n dilogCoeff = (∑ j ∈ range n, bernoulli j) +
      (if 1 < n then 1 else 0) := by
  induction n with
  | zero => simp [binomialTransform, dilogCoeff, signedStirling_zero_left]
  | succ n ih =>
    rw [binomialTransform_succ, ih, sum_range_succ]
    simp only [dilogCoeff_succ, binomialTransform_bernoulli]
    obtain _ | _ | n := n <;> simp <;> ring

end sum_bernoulli_eq_polyBernoulli

/--
**Sums of Bernoulli numbers via poly-Bernoulli polynomials.** Let $B_j$ denote the Bernoulli
numbers with $B_1 = -\tfrac12$, let $B_n^{(2)}$ denote the poly-Bernoulli numbers of order $2$,
and let $B_n^{(2)}(x)$ denote the poly-Bernoulli polynomials of order $2$. For every natural
number $n \ge 2$,
$$\sum_{j=0}^{n} B_j = B_n^{(2)}(1) + B_n - B_n^{(2)} - 1.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 3.
-/
public theorem sum_bernoulli_eq_polyBernoulli (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n + 1), bernoulli j) =
      polyBernoulliPoly n 2 1 + bernoulli n - polyBernoulli n 2 - 1 := by
  open sum_bernoulli_eq_polyBernoulli in
  have h := polyBernoulliPoly_one_sub n
  rw [binomialTransform_dilogCoeff, ite_eq_left (Nat.lt_of_succ_le hn)] at h
  rw [sum_range_succ]
  linear_combination -h

end MetaMathlibExt
