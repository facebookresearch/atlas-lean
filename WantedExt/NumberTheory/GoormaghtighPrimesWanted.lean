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

/-- **Goormaghtigh solutions with $\gcd(m - 1, n - 1) > 1$ and $m \le 50$.** Let $x, y, m, n$ be
natural numbers with $2 \le x < y$, $n > 2$, $m \le 50$ and $\gcd(m - 1, n - 1) > 1$, and suppose

$$N = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i,$$

that is, $N = (x^m - 1)/(x - 1) = (y^n - 1)/(y - 1)$. Then $N = 31$ or $N = 8191$.

The paper prints the side conditions of its Equation (1) as $y > x \ge 2$ and $n > m > 2$. Since
$y > x$, equal repunits force $m > n$ (the paper's own solution
$31 = 1 + 2 + 4 + 8 + 16 = 1 + 5 + 25$ has $m = 5 > n = 3$), so the printed $n > m$ is read as
$m > n$; that inequality follows from the other hypotheses and is not assumed. The paper quotes
this result as part of Theorem 4 of Bennett, Garbuz and Marten (2020).

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Theorem 1 (`integers-2024-A98-thm-1`). -/
public theorem_wanted goormaghtigh_eq_of_gcd_sub_one_gt_one_of_le_fifty
    (x y m n : ℕ) (hx : 2 ≤ x) (hxy : x < y) (hn : 2 < n)
    (hgcd : 1 < Nat.gcd (m - 1) (n - 1)) (hm : m ≤ 50)
    (heq : ∑ i ∈ Finset.range m, x ^ i = ∑ i ∈ Finset.range n, y ^ i) :
    ∑ i ∈ Finset.range m, x ^ i = 31 ∨ ∑ i ∈ Finset.range m, x ^ i = 8191

/-- **No Goormaghtigh primes below $10^{700}$ besides $31$ and $8191$.** Let $p$ be a prime with
$p < 10^{700}$, and let $x, y, m, n$ be natural numbers with $2 \le x < y$ and $n \ge 3$ such that

$$p = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i,$$

that is, $p$ is a repunit of length $m$ in base $x$ and of length $n$ in base $y$. Then $p = 31$
or $p = 8191$.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Section 2, discussion following Theorem 1 (`integers-2024-A98-thm-1`). -/
public theorem_wanted goormaghtigh_prime_lt_ten_pow_seven_hundred
    (p x y m n : ℕ) (hp : p.Prime) (hplt : p < 10 ^ 700) (hx : 2 ≤ x) (hxy : x < y)
    (hn : 3 ≤ n) (hpx : p = ∑ i ∈ Finset.range m, x ^ i)
    (hpy : p = ∑ i ∈ Finset.range n, y ^ i) :
    p = 31 ∨ p = 8191

/-- **Under abc, finitely many Goormaghtigh numbers have both lengths at least five.** Assume the
abc conjecture in the following form: for every real $\varepsilon > 0$, there are only finitely
many triples $(a, b, c)$ of positive integers with $a + b = c$, $\gcd(a, b) = 1$ and
$\operatorname{rad}(abc)^{1 + \varepsilon} \le c$, where $\operatorname{rad}(k)$ is the product of
the distinct primes dividing $k$. Then there are only finitely many natural numbers $N$ for which
there exist natural numbers $x, y, m, n$ with $2 \le x < y$ and $n \ge 5$ such that

$$N = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i.$$

Such an $N$ is a repunit of length $m$ in base $x$ and of length $n \ge 5$ in base $y$; since
$x < y$, equality forces $m > n$, so both lengths are at least five. The paper states the abc
conjecture for relatively prime integers; the positive-triple form used here is the standard
equivalent one.

Source: Jon Grantham, *No New Goormaghtigh Primes up to 10^700*, INTEGERS 24 (2024),
Article A98, Theorem 2 (`integers-2024-A98-thm-2`). -/
public theorem_wanted goormaghtigh_numbers_length_ge_five_finite_of_abc
    (habc : ∀ ε : ℝ, 0 < ε →
      {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
        ((∏ q ∈ (t.1 * t.2.1 * t.2.2).primeFactors, (q : ℝ)) ^ (1 + ε) ≤ (t.2.2 : ℝ))}.Finite) :
    {N : ℕ | ∃ x y m n : ℕ, 2 ≤ x ∧ x < y ∧ 5 ≤ n ∧
      N = ∑ i ∈ Finset.range m, x ^ i ∧ N = ∑ i ∈ Finset.range n, y ^ i}.Finite

/-- **Under abc, there are only finitely many Goormaghtigh primes.** Assume the abc conjecture in
the following form: for every real $\varepsilon > 0$, there are only finitely many triples
$(a, b, c)$ of positive integers with $a + b = c$, $\gcd(a, b) = 1$ and
$\operatorname{rad}(abc)^{1 + \varepsilon} \le c$, where $\operatorname{rad}(k)$ is the product of
the distinct primes dividing $k$. Then there are only finitely many primes $p$ for which there
exist natural numbers $x, y, m, n$ with $2 \le x < y$ and $n \ge 3$ such that

$$p = \sum_{i=0}^{m-1} x^i = \sum_{i=0}^{n-1} y^i.$$

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
