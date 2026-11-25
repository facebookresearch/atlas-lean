/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel

/-!
# Rising-factorial weighted sums via iterated antiderivatives

Integrating a polynomial repeatedly divides its coefficients by rising factorials.
For arbitrary antiderivatives, their values at zero determine the correction polynomial.
-/

namespace MetaMathlibExt

private theorem hasDerivAt_divided_monomial (c d x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ ↦ c * y ^ (n + 1) / (↑(n + 1) * d))
      (c * x ^ n / d) x := by
  have hn : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
  simpa only [Nat.add_one_sub_one, mul_left_comm c (↑(n + 1) : ℝ), mul_div_mul_left _ _ hn]
    using ((hasDerivAt_pow (n + 1) x).const_mul c).div_const (↑(n + 1) * d)

/-- **Rising-factorial weighted sums via iterated antiderivatives.** Let $N$ and $s$ be natural
numbers, $a_0, \dots, a_N$ real numbers and $f(y) = \sum_{k=0}^{N} a_k y^k$. Let
$I_0, I_1, I_2, \dots$ be functions $\mathbb{R} \to \mathbb{R}$ with $I_0 = f$ such that for every
$j \ge 0$ the function $I_{j+1}$ is differentiable on $\mathbb{R}$ with derivative $I_j$ (the
constants of integration are arbitrary). Write $m^{(i)} = m(m+1)\cdots(m+i-1)$ for the rising
factorial. Then for every real number $x$,

$$\sum_{k=0}^{N} \frac{a_k\, x^{k+s}}{(k+1)^{(s)}} =
I_s(x) - \sum_{j=1}^{s} \frac{I_j(0)\, x^{s-j}}{(s-j)!}.$$

The source assumes $s > 0$; for $s = 0$ the identity reads $f(x) = I_0(x)$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.2). -/
public theorem sum_coeff_mul_pow_div_ascFactorial_eq_antideriv (a : ℕ → ℝ) (N s : ℕ)
    (I : ℕ → ℝ → ℝ) (hI0 : ∀ y, I 0 y = ∑ k ∈ Finset.range (N + 1), a k * y ^ k)
    (hI : ∀ j y, HasDerivAt (I (j + 1)) (I j y) y) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), a k * x ^ (k + s) / (k + 1).ascFactorial s =
      I s x - ∑ j ∈ Finset.Icc 1 s, I j 0 * x ^ (s - j) / (s - j).factorial := by
  let weighted (r : ℕ) (y : ℝ) :=
    ∑ k ∈ Finset.range (N + 1), a k * y ^ (k + r) / (k + 1).ascFactorial r
  let correction (r : ℕ) (y : ℝ) :=
    ∑ j ∈ Finset.Icc 1 r, I j 0 * y ^ (r - j) / (r - j).factorial
  suffices h : (fun y ↦ weighted s y + correction s y) = I s from
    eq_sub_iff_add_eq.mpr (congrFun h x)
  induction s with
  | zero =>
    funext y
    simp [weighted, correction, hI0]
  | succ s ih =>
    -- Split off the new integration constant. All remaining powers are positive.
    have step (y : ℝ) : correction (s + 1) y =
        (∑ j ∈ Finset.Icc 1 s, I j 0 * y ^ (s - j + 1) / (s - j + 1).factorial) +
          I (s + 1) 0 := by
      dsimp only [correction]
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le s))]
      simp only [Nat.sub_self, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.succ_sub (Finset.mem_Icc.mp hj).2]
    have hderiv (y : ℝ) :
        HasDerivAt (fun z ↦ weighted (s + 1) z + correction (s + 1) z) (I s y) y := by
      rw [← ih]
      apply HasDerivAt.add
      · apply HasDerivAt.fun_sum
        intro k _
        simpa only [Nat.ascFactorial_succ, Nat.cast_mul, Nat.add_right_comm k 1 s, Nat.add_assoc]
          using hasDerivAt_divided_monomial (a k) ((k + 1).ascFactorial s) y (k + s)
      · rw [funext step]
        apply HasDerivAt.add_const
        apply HasDerivAt.fun_sum
        intro j _
        simpa only [Nat.factorial_succ, Nat.cast_mul] using
          hasDerivAt_divided_monomial (I j 0) (s - j).factorial y (s - j)
    apply eq_of_fderiv_eq (fun y ↦ (hderiv y).differentiableAt)
      (fun y ↦ (hI s y).differentiableAt)
      (fun y ↦ (hderiv y).hasFDerivAt.fderiv.trans (hI s y).hasFDerivAt.fderiv.symm) 0
    simp [weighted, step]

/-- **Binomial sums with rising-factorial denominators.** Write $m^{(i)} = m(m+1)\cdots(m+i-1)$
for the rising factorial. For all natural numbers $N$ and $s \ge 1$ and every real number $x$,

$$\sum_{k=0}^{N} \binom{N}{k} \frac{x^{k+s}}{(k+1)^{(s)}} =
\frac{(1+x)^{N+s} - 1}{(N+1)^{(s)}} - \sum_{j=1}^{s-1} \frac{x^j}{j!\,(N+1)^{(s-j)}}.$$

The source writes $\binom{n}{k}$ for $\binom{N}{k}$.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.1). -/
public theorem sum_choose_mul_pow_div_ascFactorial (N s : ℕ) (hs : 0 < s) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * x ^ (k + s) / (k + 1).ascFactorial s =
      ((1 + x) ^ (N + s) - 1) / (N + 1).ascFactorial s -
        ∑ j ∈ Finset.Icc 1 (s - 1), x ^ j / (j.factorial * (N + 1).ascFactorial (s - j)) := by
  let D : ℝ := (N + 1).ascFactorial s
  have hD : D ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos N s).ne'
  let f (j : ℕ) : ℝ := x ^ j * (N + s).choose j
  -- Clearing the common denominator turns the left side into the binomial tail.
  have htail : D * (∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℝ) * x ^ (k + s) / (k + 1).ascFactorial s) =
      ∑ k ∈ Finset.range (N + 1), f (k + s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hchoose := Nat.choose_mul (n := N + s) (Nat.le_add_left s k)
    simp only [Nat.add_sub_cancel] at hchoose
    have h : N.choose k * (N + 1).ascFactorial s =
        (N + s).choose (k + s) * (k + 1).ascFactorial s := by
      simp only [Nat.ascFactorial_eq_factorial_mul_choose]
      calc
        _ = s.factorial * ((N + s).choose s * N.choose k) := by ac_rfl
        _ = s.factorial * ((N + s).choose (k + s) * (k + s).choose s) := by rw [hchoose]
        _ = _ := by ac_rfl
    have hcast : (N.choose k : ℝ) * D = (↑((N + s).choose (k + s)) : ℝ) *
        ↑((k + 1).ascFactorial s) := by
      dsimp only [D]
      exact_mod_cast h
    have hk : (↑((k + 1).ascFactorial s) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos k s).ne'
    rw [← mul_div_assoc, div_eq_iff hk]
    dsimp only [f]
    calc
      _ = ((N.choose k : ℝ) * D) * x ^ (k + s) := by ac_rfl
      _ = _ := by rw [hcast]; ac_rfl
  -- The same scaling turns the correction terms into the positive low-degree terms.
  have hlow : D * (∑ j ∈ Finset.Icc 1 (s - 1),
      x ^ j / (j.factorial * (N + 1).ascFactorial (s - j))) =
      ∑ j ∈ Finset.Icc 1 (s - 1), f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjs : j ≤ s := (Finset.mem_Icc.mp hj).2.trans (Nat.sub_le _ _)
    have h := Nat.ascFactorial_mul_ascFactorial (N + 1) (s - j) j
    rw [Nat.sub_add_cancel hjs, show N + 1 + (s - j) = N + (s - j) + 1 by ac_rfl,
      Nat.ascFactorial_eq_factorial_mul_choose (N + (s - j)),
      show N + (s - j) + j = N + s by rw [Nat.add_assoc, Nat.sub_add_cancel hjs]] at h
    have hcast : D = (↑((N + 1).ascFactorial (s - j)) : ℝ) *
        (↑j.factorial * ↑((N + s).choose j)) := by
      dsimp only [D]
      exact_mod_cast h.symm
    have hjd : (↑j.factorial * ↑((N + 1).ascFactorial (s - j)) : ℝ) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne')
        (Nat.cast_ne_zero.mpr (Nat.ascFactorial_pos N (s - j)).ne')
    rw [← mul_div_assoc, div_eq_iff hjd, hcast]
    dsimp only [f]
    ac_rfl
  have hzero : 0 ∈ Finset.range s := Finset.mem_range.mpr hs
  have herase : (Finset.range s).erase 0 = Finset.Icc 1 (s - 1) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hprefix : (∑ j ∈ Finset.range s, f j) = (∑ j ∈ Finset.Icc 1 (s - 1), f j) + 1 := by
    simpa [herase, f] using (Finset.sum_erase_add (Finset.range s) f hzero).symm
  have hexpand : (1 + x) ^ (N + s) = ((∑ j ∈ Finset.Icc 1 (s - 1), f j) + 1) +
      ∑ k ∈ Finset.range (N + 1), f (k + s) := by
    rw [add_comm 1 x, add_pow]
    simp only [one_pow, mul_one]
    change (∑ j ∈ Finset.range (N + s + 1), f j) = _
    rw [show N + s + 1 = s + (N + 1) by ac_rfl, Finset.sum_range_add, hprefix]
    simp only [add_comm s]
  change _ = ((1 + x) ^ (N + s) - 1) / D - _
  apply mul_left_cancel₀ hD
  rw [mul_sub, htail, hlow, ← mul_div_assoc, mul_div_cancel_left₀ _ hD, hexpand]
  abel

end MetaMathlibExt
