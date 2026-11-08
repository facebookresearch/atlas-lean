/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PrimeFin

namespace MetaMathlibExt

@[expose] public section

/-! # Goormaghtigh primes

Statements from Grantham's paper on Goormaghtigh primes. Equation (1) of the paper is
`N = (x^m - 1)/(x - 1) = (y^n - 1)/(y - 1)`; the length-`k` repunit in base `x` is written
here as the geometric sum `∑ i ∈ Finset.range k, x ^ i`, which avoids natural-number
division. A Goormaghtigh number has two repunit representations of length at least three
in distinct bases; a Goormaghtigh prime is a prime Goormaghtigh number.
-/

/-- The only solutions of the Goormaghtigh equation
`(x^m - 1)/(x - 1) = (y^n - 1)/(y - 1)` with `y > x ≥ 2`, `n > 2`,
`gcd(m - 1, n - 1) > 1` and `m ≤ 50` have `N = 31` or `N = 8191`.

The paper prints the side conditions of Equation (1) as `y > x ≥ 2`, `n > m > 2`; with
`y > x` equal repunits force `m > n` (the paper's own solution `31 = f₅(2) = f₃(5)` has
`m = 5 > n = 3`, and its algorithm takes `m > n`), so the printed `n > m` is read as
`m > n`. That inequality follows from the other hypotheses and is not assumed. The paper
quotes this as part of Theorem 4 of Bennett, Garbuz and Marten (2020); the algorithm and
proof narrative in the extracted record are not part of the statement.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Theorem 1 (`integers-2024-A98-thm-1`). -/
public theorem_wanted goormaghtigh_eq_of_gcd_sub_one_gt_one_of_le_fifty
    (x y m n : ℕ) (hx : 2 ≤ x) (hxy : x < y) (hn : 2 < n)
    (hgcd : 1 < Nat.gcd (m - 1) (n - 1)) (hm : m ≤ 50)
    (heq : ∑ i ∈ Finset.range m, x ^ i = ∑ i ∈ Finset.range n, y ^ i) :
    ∑ i ∈ Finset.range m, x ^ i = 31 ∨ ∑ i ∈ Finset.range m, x ^ i = 8191

/-- There are no Goormaghtigh primes below `10^700` other than `31` and `8191`: a prime
`p < 10^700` that is a repunit of length at least three in two distinct bases is `31`
or `8191`.

This is the headline result whose computation the extracted Theorem 1 record describes;
the record's further remark (no new Goormaghtigh numbers below `10^700` with both
exponents prime) is not formalized here.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Section 2, discussion following Theorem 1 (`integers-2024-A98-thm-1`). -/
public theorem_wanted goormaghtigh_prime_lt_ten_pow_seven_hundred
    (p x y m n : ℕ) (hp : p.Prime) (hplt : p < 10 ^ 700) (hx : 2 ≤ x) (hxy : x < y)
    (hn : 3 ≤ n) (hpx : p = ∑ i ∈ Finset.range m, x ^ i)
    (hpy : p = ∑ i ∈ Finset.range n, y ^ i) :
    p = 31 ∨ p = 8191

/-- Assuming the abc conjecture, there are only finitely many Goormaghtigh numbers where
neither representation has length three or four, i.e. finitely many `N` that are repunits
of length at least five in two distinct bases.

The abc conjecture is the hypothesis `habc`: for every `ε > 0`, only finitely many
coprime positive triples `a + b = c` satisfy `rad(abc)^(1 + ε) ≤ c`. The paper states it
for relatively prime integers; the positive-triple form used here is the standard
equivalent one.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Theorem 2 (`integers-2024-A98-thm-2`). -/
public theorem_wanted goormaghtigh_numbers_length_ge_five_finite_of_abc
    (habc : ∀ ε : ℝ, 0 < ε →
      {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
        ((∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ))}.Finite) :
    {N : ℕ | ∃ x y m n : ℕ, 2 ≤ x ∧ x < y ∧ 5 ≤ n ∧
      N = ∑ i ∈ Finset.range m, x ^ i ∧ N = ∑ i ∈ Finset.range n, y ^ i}.Finite

/-- Assuming the abc conjecture, there are only finitely many Goormaghtigh primes, i.e.
finitely many primes that are repunits of length at least three in two distinct bases.

The abc conjecture is the hypothesis `habc`, in the positive-triple form described for
`goormaghtigh_numbers_length_ge_five_finite_of_abc`.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Corollary 1 (`integers-2024-A98-cor-1`). -/
public theorem_wanted goormaghtigh_primes_finite_of_abc
    (habc : ∀ ε : ℝ, 0 < ε →
      {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
        ((∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ))}.Finite) :
    {p : ℕ | p.Prime ∧ ∃ x y m n : ℕ, 2 ≤ x ∧ x < y ∧ 3 ≤ n ∧
      p = ∑ i ∈ Finset.range m, x ^ i ∧ p = ∑ i ∈ Finset.range n, y ^ i}.Finite

end

end MetaMathlibExt
