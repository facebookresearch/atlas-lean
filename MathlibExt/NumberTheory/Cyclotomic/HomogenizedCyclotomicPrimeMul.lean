/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.HomogenizedCyclotomic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Homogenized cyclotomic values at prime multiples

The value at index `p * n` satisfies the cyclotomic expansion identities in both
divisibility cases for the prime `p`.
-/

namespace MetaMathlibExt

open Polynomial

private theorem homogenizedCyclotomic_eq_eval_scaleRoots (n : ℕ) (a b : ℤ) :
    homogenizedCyclotomic n a b = ((cyclotomic n ℤ).scaleRoots b).eval a := by
  rw [homogenizedCyclotomic, eval_eq_sum_range, natDegree_scaleRoots, natDegree_cyclotomic]
  simp only [coeff_scaleRoots, natDegree_cyclotomic, mul_right_comm]

private theorem scaleRoots_expand {p : ℕ} (hp : 0 < p) (f : ℤ[X]) (b : ℤ) :
    (expand ℤ p f).scaleRoots b = expand ℤ p (f.scaleRoots (b ^ p)) := by
  ext i
  by_cases hi : p ∣ i
  · obtain ⟨j, rfl⟩ := hi
    simp only [coeff_scaleRoots, coeff_expand_mul' hp, natDegree_expand, ← pow_mul,
      mul_comm f.natDegree p, Nat.mul_sub]
  · simp [coeff_scaleRoots, coeff_expand hp, hi]

set_option linter.unusedVariables false in
/-- **Homogenized cyclotomic values at $pn$.** Let $p$ be a prime, $n$ a positive integer and
$a, b$ integers, and write $\Phi_m(a, b)$ for the homogenized cyclotomic value. If $p \mid n$,
then $\Phi_{pn}(a, b) = \Phi_n(a^p, b^p)$. If $p \nmid n$, then
$\Phi_{pn}(a, b) \cdot \Phi_n(a, b) = \Phi_n(a^p, b^p)$.

The paper states the case $p \nmid n$ as a quotient; here it is cleared of its denominator.

Source: Ömer Avcı, *Large Zsigmondy Primes*, INTEGERS 24 (2024), Article A62, Lemma 3 (iii)
(quoted from reference [6]). -/
public theorem homogenizedCyclotomic_prime_mul {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (a b : ℤ) :
    (p ∣ n → homogenizedCyclotomic (p * n) a b = homogenizedCyclotomic n (a ^ p) (b ^ p)) ∧
      (¬ p ∣ n → homogenizedCyclotomic (p * n) a b * homogenizedCyclotomic n a b =
        homogenizedCyclotomic n (a ^ p) (b ^ p)) := by
  simp only [homogenizedCyclotomic_eq_eval_scaleRoots, mul_comm p n]
  rw [← expand_eval, ← scaleRoots_expand hp.pos]
  constructor
  · intro h
    rw [cyclotomic_expand_eq_cyclotomic hp h]
  · intro h
    rw [cyclotomic_expand_eq_cyclotomic_mul hp h, mul_scaleRoots_of_noZeroDivisors, eval_mul]

end MetaMathlibExt
