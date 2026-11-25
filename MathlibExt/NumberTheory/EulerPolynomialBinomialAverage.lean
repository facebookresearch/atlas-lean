/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.ZetaValues

/-!
# Euler polynomials as alternating sums of shifted powers

`eulerPoly_eq_binomial_average` expresses each Euler polynomial as a finite alternating sum
of binomial averages. The proof uses the average of translation by the two half-steps.
-/

@[expose] public section

open Polynomial Finset

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/-- **Euler polynomials.** Let $B_m(x)$ denote the $m$-th Bernoulli polynomial. For $n \ge 0$,
the Euler polynomial $E_n(x)$ is the polynomial with rational coefficients
$E_n(x) = \frac{2}{n + 1} \left(B_{n+1}(x) - 2^{n+1} B_{n+1}(x/2)\right)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Section 1 (Euler polynomials). -/
noncomputable def eulerPoly (n : ℕ) : ℚ[X] :=
  (2 / (n + 1 : ℚ)) • (Polynomial.bernoulli (n + 1) -
    (2 : ℚ) ^ (n + 1) •
      (Polynomial.bernoulli (n + 1)).comp (C (1 / 2) * X))

/-- The average of the Euler polynomial at adjacent arguments recovers the monomial. -/
private theorem eulerPoly_shift (n : ℕ) :
    taylor 1 (eulerPoly n) + eulerPoly n = (2 : ℚ) • X ^ n := by
  apply Polynomial.funext
  intro x
  have dup := bernoulliFun_mul (n + 1) (m := 2) (by decide) ((x : ℝ) / 2)
  have cast_eval (y : ℚ) : bernoulliFun (n + 1) (y : ℝ) =
      ((Polynomial.bernoulli (n + 1)).eval y : ℚ) := by
    exact Polynomial.eval_map_apply (algebraMap ℚ ℝ) y
  norm_num [sum_range_succ] at dup
  rw [show 2 * ((x : ℝ) / 2) = x by ring,
    show (x : ℝ) / 2 + 1 / 2 = ((x + 1 : ℚ) / 2 : ℚ) by push_cast; ring,
    show (x : ℝ) / 2 = ((x / 2 : ℚ) : ℝ) by push_cast; rfl,
    cast_eval, cast_eval, cast_eval] at dup
  have hd : (Polynomial.bernoulli (n + 1)).eval x =
      2 ^ n * ((Polynomial.bernoulli (n + 1)).eval (x / 2) +
        (Polynomial.bernoulli (n + 1)).eval ((x + 1) / 2)) := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    rw [pow_succ] at dup
    linarith
  have step := Polynomial.bernoulli_eval_one_add (n + 1) x
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at step
  rw [add_comm 1 x] at step
  simp only [eval_add, taylor_eval, eulerPoly, eval_smul, eval_sub, eval_comp, eval_mul,
    eval_C, eval_X, eval_pow, smul_eq_mul]
  simp only [one_div_mul_eq_div]
  field_simp
  rw [pow_succ]
  linear_combination step + 2 * hd

private noncomputable def average : Module.End ℚ ℚ[X] :=
  (1 / 2 : ℚ) • (taylor (1 / 2) + taylor (-1 / 2))

private theorem average_eulerPoly (n : ℕ) :
    average (eulerPoly n) = taylor (-1 / 2) (X ^ n) := by
  have h := congrArg (taylor (-1 / 2 : ℚ)) (eulerPoly_shift n)
  simp only [map_add, map_smul, taylor_taylor] at h
  simp only [average, LinearMap.smul_apply, LinearMap.add_apply]
  norm_num only at h ⊢
  rw [h, smul_smul]
  norm_num

private theorem degree_eulerPoly_le (n : ℕ) : (eulerPoly n).degree ≤ ↑n := by
  by_cases hz : eulerPoly n = 0
  · simp [hz]
  have hd := degree_add_eq_of_leadingCoeff_add_ne_zero
    (p := taylor 1 (eulerPoly n)) (q := eulerPoly n) (by simpa using hz)
  rw [degree_taylor, max_self, eulerPoly_shift] at hd
  rw [← hd]
  exact (degree_smul_le _ _).trans (degree_X_pow_le _)

-- A first difference cancels the leading term, including for constant polynomials.
private theorem degree_difference (h : ℚ) (p : ℚ[X]) (d : ℕ)
    (hp : p.degree < ↑(d + 1)) : (p - taylor h p).degree < ↑d := by
  by_cases hz : p = 0
  · simp [hz]
  have hd := (natDegree_lt_iff_degree_lt hz).mpr hp
  exact (degree_sub_lt_left (degree_taylor _ _).symm hz (leadingCoeff_taylor _ _).symm).trans_le
    (degree_le_of_natDegree_le (Nat.le_of_lt_succ hd))

-- Subtracting the centered average amounts to taking two opposite first differences.
private theorem average_remainder (k : ℕ) (p : ℚ[X]) (hp : p.degree < ↑(2 * k)) :
    ((1 - average) ^ k) p = 0 := by
  induction k generalizing p with
  | zero =>
    by_contra! h
    have hz : p ≠ 0 := by simpa using h
    exact (Nat.not_lt_zero _) ((natDegree_lt_iff_degree_lt hz).mpr hp)
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp]
    apply ih
    let q := p - taylor (-1 / 2) p
    have hq : q.degree < ↑(2 * k + 1) :=
      degree_difference _ _ _ (by simpa [Nat.mul_succ, Nat.add_assoc] using hp)
    have fac : (1 - average) p = (1 / 2 : ℚ) • (q - taylor (1 / 2) q) := by
      simp only [average, q, LinearMap.sub_apply, one_apply_eq_self, LinearMap.smul_apply,
        LinearMap.add_apply, map_sub, taylor_taylor]
      norm_num [taylor_zero]
      module
    rw [fac]
    exact (degree_smul_le _ _).trans_lt (degree_difference _ _ _ hq)

private theorem taylor_pow_apply (h : ℚ) (k : ℕ) (p : ℚ[X]) :
    ((taylor h : Module.End ℚ ℚ[X]) ^ k) p = taylor (k * h) p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_eq_comp, ih, taylor_taylor]
    push_cast
    ring_nf

-- Evaluate the binomial theorem for commuting endomorphisms at a polynomial.
private theorem binomial_apply (a b : Module.End ℚ ℚ[X]) (hab : Commute a b)
    (k : ℕ) (p : ℚ[X]) :
    ((a + b) ^ k) p = ∑ j ∈ range (k + 1),
      (k.choose j : ℚ) • (a ^ j) ((b ^ (k - j)) p) := by
  rw [hab.add_pow]
  simp only [LinearMap.sum_apply, mul_apply_eq_comp, natCast_apply_eq_smul, map_nsmul,
    Nat.cast_smul_eq_nsmul]

private theorem average_pow (k n : ℕ) :
    (average ^ k) (taylor (-1 / 2) (X ^ n)) =
      (1 / 2 : ℚ) ^ k • ∑ j ∈ range (k + 1),
        (k.choose j : ℚ) • (X + C ((j : ℚ) - (k + 1 : ℚ) / 2)) ^ n := by
  have comm : Commute (taylor (1 / 2 : ℚ)) (taylor (-1 / 2 : ℚ)) := by
    apply LinearMap.ext
    intro p
    change taylor _ (taylor _ p) = taylor _ (taylor _ p)
    rw [taylor_taylor, taylor_taylor, add_comm]
  rw [average, smul_pow, LinearMap.smul_apply, binomial_apply _ _ comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [taylor_pow_apply, taylor_pow_apply, taylor_taylor, taylor_taylor, taylor_X_pow,
    Nat.cast_sub (mem_range_succ_iff.mp hj)]
  ring_nf

set_option linter.unusedVariables false in
/-- **Euler polynomials as alternating sums of shifted powers.** Let $E_n(x)$ denote the Euler
polynomial. For all natural numbers $m \ge 2$ and $n \le 2m + 1$,
$E_n(x) = \sum_{k=0}^{m} \frac{(-1)^k}{2^k} \binom{m+1}{k+1}
\sum_{j=0}^{k} \binom{k}{j} \left(x + j - \frac{k+1}{2}\right)^n$
as polynomials in $x$ with rational coefficients.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.1. -/
theorem eulerPoly_eq_binomial_average (m n : ℕ)
    (hm : 2 ≤ m) (hn : n ≤ 2 * m + 1) :
    eulerPoly n =
      ∑ k ∈ Finset.range (m + 1),
        ((-1) ^ k * (Nat.choose (m + 1) (k + 1) : ℚ) /
            (2 : ℚ) ^ k) •
          ∑ j ∈ Finset.range (k + 1),
            (Nat.choose k j : ℚ) •
              (X + C ((j : ℚ) - (k + 1 : ℚ) / 2)) ^ n := by
  have hz := average_remainder (m + 1) (eulerPoly n)
    ((degree_eulerPoly_le n).trans_lt (WithBot.coe_lt_coe.mpr (show n < 2 * (m + 1) by omega)))
  rw [show (1 - average) = -average + 1 by abel,
    binomial_apply _ _ (Commute.one_right _) _, sum_range_succ'] at hz
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_smul, one_pow,
    one_apply_eq_self] at hz
  apply eq_of_sub_eq_zero
  convert hz using 1
  rw [sub_eq_neg_add, ← sum_neg_distrib, add_left_inj]
  apply sum_congr rfl
  intro k _
  rw [← neg_one_smul ℚ average, smul_pow, LinearMap.smul_apply,
    pow_succ average, mul_apply_eq_comp, average_eulerPoly, average_pow]
  rw [← neg_smul, smul_smul, smul_smul]
  congr 1
  rw [pow_succ, div_pow]
  ring

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
