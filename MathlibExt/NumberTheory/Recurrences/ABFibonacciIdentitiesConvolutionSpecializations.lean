/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesConvolutionLucasABFibAB
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fibonacci, Jacobsthal and Pell convolution identities

For every natural number `n`, the two Fibonacci–Jacobsthal sums, the two Pell sums, and the
two even-index Fibonacci–Lucas sums with Mersenne sequences come from the same
(a, b)-Lucas/(a, d)-Fibonacci convolution over `ℂ`. At `n = 0` the sums are empty and the
right-hand sides are zero by the initial values.

## References

* Emil Daniel Schwab, *Fibonacci Numbers via Dirichlet Convolution and Lucas Numbers via
  Unitary Convolution*, Journal of Integer Sequences 28 (2025), Article 25.1.7,
  Corollary 14(b), pp. 14–15. The proof specializes Corollary 14(a), formalized as
  `convolution_lucasAB_fibAB` in `ABFibonacciIdentitiesConvolutionLucasABFibAB`.
* M. Griffiths and A. Bramham, *The Jacobsthal numbers: two results and two questions*,
  Fibonacci Quarterly 53 (2015), 147–151, Section 2; cited by Schwab for part (i).
* A. Bramham and M. Griffiths, *Combinatorial interpretation of some convolution identities*,
  Fibonacci Quarterly 54 (2016), 335–339, Theorem 1.1; cited by Schwab for part (i).
* T. Koshy and M. Griffiths, *Some Gibonacci convolutions with dividends*,
  Fibonacci Quarterly 56 (2018), 237–245, (2.6) and (2.7); cited by Schwab for part (i).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted

private lemma fibAB_two_neg_one (n : ℕ) : fibAB 2 (-1) n = (n : ℂ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
    simp only [fibAB_add_two, ih₀, ih₁, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

private lemma lucasAB_two_neg_one (n : ℕ) : lucasAB 2 (-1) n = 2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ => rw [lucasAB_add_two, ih₀, ih₁]; norm_num

-- Three successive applications of the (1, 1) recurrence give the even-index recurrence.
private lemma even_recurrence (u : ℕ → ℂ)
    (hu : ∀ m : ℕ, u (m + 2) = 1 * u (m + 1) + 1 * u m) (n : ℕ) :
    u (2 * (n + 2)) = 3 * u (2 * (n + 1)) + (-1) * u (2 * n) := by
  rw [show 2 * (n + 2) = 2 * n + 4 by omega, show 2 * (n + 1) = 2 * n + 2 by omega]
  linear_combination hu (2 * n + 2) + hu (2 * n + 1) - hu (2 * n)

private lemma fibAB_three_neg_one (n : ℕ) : fibAB 3 (-1) n = fibAB 1 1 (2 * n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    change fibAB 3 (-1) 1 = fibAB 1 1 (0 + 2)
    rw [fibAB_add_two, fibAB_zero, fibAB_one, fibAB_one]
    norm_num
  | more n ih₀ ih₁ => rw [fibAB_add_two, ih₀, ih₁, even_recurrence _ (fibAB_add_two 1 1)]

private lemma lucasAB_three_neg_one (n : ℕ) : lucasAB 3 (-1) n = lucasAB 1 1 (2 * n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    change lucasAB 3 (-1) 1 = lucasAB 1 1 (0 + 2)
    rw [lucasAB_add_two, lucasAB_zero, lucasAB_one, lucasAB_one]
    norm_num
  | more n ih₀ ih₁ => rw [lucasAB_add_two, ih₀, ih₁, even_recurrence _ (lucasAB_add_two 1 1)]

private lemma mersenne_recurrences (n : ℕ) :
    fibAB 3 (-2) n = 2 ^ n - 1 ∧ lucasAB 3 (-2) n = 2 ^ n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [fibAB_zero, lucasAB_zero]
  | one => norm_num [fibAB_one, lucasAB_one]
  | more n ih₀ ih₁ =>
    constructor
    · rw [fibAB_add_two, ih₀.1, ih₁.1, pow_succ (2 : ℂ) (n + 1), pow_succ (2 : ℂ) n]
      ring
    · rw [lucasAB_add_two, ih₀.2, ih₁.2, pow_succ (2 : ℂ) (n + 1), pow_succ (2 : ℂ) n]
      ring

/-- **Fibonacci, Jacobsthal and Pell convolution identities.** Write $F_n$ and $L_n$ for the
Fibonacci and Lucas numbers (the $(1,1)$-Fibonacci and $(1,1)$-Lucas numbers), $J_n$ and $j_n$
for the Jacobsthal and Jacobsthal–Lucas numbers (the $(1,2)$-Fibonacci and $(1,2)$-Lucas
numbers), and $P_n$ and $Q_n$ for the Pell and Pell–Lucas numbers (the $(2,1)$-Fibonacci and
$(2,1)$-Lucas numbers), all as complex numbers. Then for every natural number $n$:
(i) $\sum_{i=1}^{n} L_{n-i} J_i = j_{n+1} - L_{n+1}$ and
$\sum_{i=1}^{n} j_{n-i} F_i = j_{n+1} - L_{n+1}$;
(ii) $2 \sum_{i=1}^{n} P_i = (Q_{n+1} - 2)/2$ and $\sum_{i=1}^{n} i \, Q_{n-i} = (Q_{n+1} - 2)/2$;
(iii) $\sum_{i=1}^{n} L_{2(n-i)} (2^i - 1) = L_{2n+2} - 2^{n+1} - 1$ and
$\sum_{i=1}^{n} (2^{n-i} + 1) F_{2i} = L_{2n+2} - 2^{n+1} - 1$.

Source: Emil Daniel Schwab, "Fibonacci Numbers
via Dirichlet Convolution and Lucas Numbers via
Unitary Convolution", Corollary 14(b). -/
theorem convolution_specializations (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, lucasAB 1 1 (n - i) * fibAB 1 2 i =
        lucasAB 1 2 (n + 1) - lucasAB 1 1 (n + 1) ∧
      ∑ i ∈ Finset.Icc 1 n, lucasAB 1 2 (n - i) * fibAB 1 1 i =
        lucasAB 1 2 (n + 1) - lucasAB 1 1 (n + 1)) ∧
    (2 * ∑ i ∈ Finset.Icc 1 n, fibAB 2 1 i =
        (lucasAB 2 1 (n + 1) - 2) / 2 ∧
      ∑ i ∈ Finset.Icc 1 n, (i : ℂ) * lucasAB 2 1 (n - i) =
        (lucasAB 2 1 (n + 1) - 2) / 2) ∧
    (∑ i ∈ Finset.Icc 1 n,
        lucasAB 1 1 (2 * (n - i)) * (2 ^ i - 1) =
        lucasAB 1 1 (2 * n + 2) - 2 ^ (n + 1) - 1 ∧
      ∑ i ∈ Finset.Icc 1 n, (2 ^ (n - i) + 1) * fibAB 1 1 (2 * i) =
        lucasAB 1 1 (2 * n + 2) - 2 ^ (n + 1) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h, hsymm⟩ := convolution_lucasAB_fibAB 1 2 1 (by norm_num) n
    rw [show (2 : ℂ) - 1 = 1 by norm_num, one_mul] at h
    exact ⟨hsymm.symm.trans h, h⟩
  · obtain ⟨h, hsymm⟩ := convolution_lucasAB_fibAB 2 1 (-1) (by norm_num) n
    simp only [fibAB_two_neg_one, lucasAB_two_neg_one, mul_comm (lucasAB 2 1 _)] at h hsymm
    rw [show (1 : ℂ) - (-1) = 2 by norm_num, mul_comm (2 : ℂ)] at h
    rw [← Finset.mul_sum] at hsymm
    have hsum := (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2 h
    exact ⟨hsymm.symm.trans hsum, hsum⟩
  · obtain ⟨h, hsymm⟩ := convolution_lucasAB_fibAB 3 (-1) (-2) (by norm_num) n
    simp only [lucasAB_three_neg_one, fibAB_three_neg_one, (mersenne_recurrences _).1,
      (mersenne_recurrences _).2, Nat.mul_add, Nat.mul_one] at h hsymm
    rw [show (-1 : ℂ) - (-2) = 1 by norm_num, one_mul, sub_add_eq_sub_sub] at h
    exact ⟨h, hsymm.symm.trans h⟩

end MathlibExt.NumberTheory.Recurrences.ABFibonacciIdentitiesWanted
