/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliDuality
public import WantedExt.NumberTheory.EulerPolynomialFormulasWanted
public import WantedExt.NumberTheory.GobelSequenceWanted
public import Mathlib.NumberTheory.Harmonic.Defs

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/--
`polyBernoulliPoly n p x` is the poly-Bernoulli polynomial obtained by
multiplying the exponential generating function for `polyBernoulli` by
`exp (x t)`: its `i`th summand is `choose n i * polyBernoulli i p * x^(n-i)`.
Thus it is the coefficient form of
`Li_p(1-exp(-t))/(1-exp(-t)) * exp(x t)`; this finite-sum definition replaces
the paper's generating-function presentation, but has the same normalization
at `x = 0`.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public def polyBernoulliPoly (n : ℕ) (p : ℤ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℚ) * polyBernoulli i p * x ^ (n - i)

/--
At `x = 0`, the poly-Bernoulli polynomial of degree `n` is the poly-Bernoulli
number of index `n` and the same integer order `p`; this proves the
normalization stated with the generating function, with no deviation.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public theorem polyBernoulliPoly_zero (n : ℕ) (p : ℤ) :
    polyBernoulliPoly n p 0 = polyBernoulli n p := by
  rw [polyBernoulliPoly, Finset.sum_range_succ]
  have hzero :
      (∑ i ∈ Finset.range n,
        (n.choose i : ℚ) * polyBernoulli i p * (0 : ℚ) ^ (n - i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hsub : n - i ≠ 0 := by omega
    simp [hsub]
  rw [hzero]
  simp

/--
The degree-zero poly-Bernoulli polynomial equals `1` for every integer order
`p` and every rational argument `x`; this is the constant term of the stated
generating function, with no deviation.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, definition of
poly-Bernoulli polynomials before Corollary 3.
-/
public theorem polyBernoulliPoly_zero_index (p : ℤ) (x : ℚ) :
    polyBernoulliPoly 0 p x = 1 := by
  simp [polyBernoulliPoly, polyBernoulli]

/--
For natural indices `j < n`, the alternating sum from `k = j` through `n` of
the second-kind Stirling number `{n brace k}`, the unsigned first-kind
Stirling number `[k brack j]`, and `H_k` equals
`(choose n j - 1) * B_(n-j)/(n-j)`. Here `B` is Mathlib's `bernoulli`, so
`B_1 = -1/2`. The hypothesis `j < n` is the stated deviation: the diagonal `n = j`, where the
paper reads the right-hand side in the limiting sense (both sides are then `H_j`), is
not stated.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Theorem 1,
equation (5).
-/
public theorem_wanted sum_stirling_harmonic_eq_bernoulli (n j : ℕ) (hjn : j < n) :
    (∑ k ∈ Finset.Icc j n,
      (-1 : ℚ) ^ (k - j) * (Nat.stirlingSecond n k : ℚ) *
        (Nat.stirlingFirst k j : ℚ) * harmonic k) =
      ((n.choose j : ℚ) - 1) * bernoulli (n - j) / (n - j : ℚ)

/--
For positive natural numbers `n` and `m`, the sum from `j = 1` through `n` of
`(choose n j - 1) * (B_j/j) * m^(n-j)` equals
`m^n * (H_m-H_n)` minus the sum from `j = 1` through `m` of `(m-j)^n/j`.
All powers, divisions, Bernoulli numbers, and harmonic numbers are in `ℚ`;
this is a direct formalization with no mathematical deviation.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 1,
equation (11).
-/
public theorem_wanted sum_bernoulli_harmonic_power_identity (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) - 1) * (bernoulli j / (j : ℚ)) * (m : ℚ) ^ (n - j)) =
      (m : ℚ) ^ n * (harmonic m - harmonic n) -
        ∑ j ∈ Finset.Icc 1 m, ((m - j : ℕ) : ℚ) ^ n / (j : ℚ)

/--
For positive natural `n`, the sum from `j = 1` through `n` of
`(choose n j + 1) * (B_j/j) * (1-2^j)` equals `1`. Bernoulli numbers use
Mathlib's convention `B_1 = -1/2`, and all arithmetic is in `ℚ`; there is no
mathematical deviation from equation (14).
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 2,
equation (14).
-/
public theorem_wanted sum_bernoulli_one_sub_two_pow (n : ℕ) (hn : 0 < n) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) + 1) * (bernoulli j / (j : ℚ)) *
        (1 - (2 : ℚ) ^ j)) = 1

/--
For natural `n >= 2`, the sum `B_0 + ... + B_n` equals the order-two
poly-Bernoulli polynomial at `1`, plus `B_n`, minus the order-two
poly-Bernoulli number, minus `1`. The polynomial is represented by its finite
coefficient sum rather than by a generating function; this is the only
representational deviation.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 3.
-/
public theorem_wanted sum_bernoulli_eq_polyBernoulli (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n + 1), bernoulli j) =
      polyBernoulliPoly n 2 1 + bernoulli n - polyBernoulli n 2 - 1

/--
For an odd prime `p`, the rational sum `sum_{j=0}^p p * B_j` has denominator
not divisible by `p`, and its image under `ratResidue p` equals that of `-1`.
The explicit denominator clause and residue equality replace the paper's
rational congruence notation; `hp2` states oddness as `p != 2`.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (23).
-/
public theorem_wanted sum_prime_mul_bernoulli_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (p : ℚ) * bernoulli j).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (p : ℚ) * bernoulli j) =
        ratResidue p (-1)

/--
For a prime `p >= 5`, the rational sum `B_0 + ... + B_(p-3)` has denominator not divisible
by `p`, and its residue equals that of `-1`. The denominator clause and
`ratResidue` equality are the formal replacement for rational congruence.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (24).
-/
public theorem_wanted sum_bernoulli_to_prime_sub_three_mod_prime (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬p ∣ (∑ j ∈ Finset.range (p - 2), bernoulli j).den ∧
      ratResidue p (∑ j ∈ Finset.range (p - 2), bernoulli j) =
        ratResidue p (-1)

/--
For an odd prime `p`, the rational sum `E_0(0) + ... + E_p(0)` has denominator
not divisible by `p`, and its residue equals that of `3/2`. The source's Euler number
`E_n = E_n(0)` is the value at `0` of the existing Euler polynomial `eulerPoly n`
(generating function `2 e^{xt}/(e^t + 1)`, values `1, -1/2, 0, 1/4`); the explicit
denominator clause and residue equality replace the paper's congruence notation.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (25).
-/
public theorem_wanted sum_euler_eval_zero_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0) =
        ratResidue p (3 / 2)

/--
For an odd prime `p`, the rational number
`p * sum_{j=0}^p B_j/(p-j+1)` has denominator not divisible by `p`, and its
residue equals that of `-1`. Natural subtraction occurs only for `j <= p` in
the range; the denominator clause and residue equality replace rational
congruence notation.
Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (26).
-/
public theorem_wanted prime_mul_sum_bernoulli_div_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ ((p : ℚ) * ∑ j ∈ Finset.range (p + 1),
      bernoulli j / ((p - j + 1 : ℕ) : ℚ)).den ∧
      ratResidue p ((p : ℚ) * ∑ j ∈ Finset.range (p + 1),
        bernoulli j / ((p - j + 1 : ℕ) : ℚ)) = ratResidue p (-1)

end

end MetaMathlibExt
