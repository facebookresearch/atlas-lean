/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Radical.Basic
public import MathlibExt.NumberTheory.ReducedResidueLongestAP
public import MathlibExt.NumberTheory.ReducedResiduePrimeBound

/-!
# Longest arithmetic progressions in the reduced residue systems `R_m(n)`

For integers `m` and `n > 1`, Phothila, Thoket and Kanasri study the reduced residue system
`R_m(n) = {a ∈ ℤ | m + 1 ≤ a ≤ m + n, gcd(a, n) = 1}` modulo `n`, the length `f_m(n)` of the
longest arithmetic progressions contained in it, the length `f_m(d, n)` of the longest ones
with common difference `d`, and `g(n) = f_{-⌈n/2⌉}(n)` for the system of absolute least
reduced residues. Throughout, `gpf(n)` is written `n.primeFactors.sup id` (the largest prime
factor of `n` for `n > 1`) and `rad(n)` is `UniqueFactorizationMonoid.radical n`.

The definitions, the squarefree fixed-difference bound, the formula for twice an odd prime and
the minimum for primes congruent to three modulo four are in
`MathlibExt.NumberTheory.ReducedResidueLongestAP`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

@[expose] public section

open UniqueFactorizationMonoid

/-- **Longest progressions of absolute least residues: primes congruent to 1 mod 4.** For a
prime $p \equiv 1 \pmod 4$, the length $g(p)$ of the longest arithmetic progression in the
absolute least reduced residue system modulo $p$ is $(p - 1)/2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) : absLeastAPLength p = (p - 1) / 2

/-- **Longest progressions of absolute least residues: primes congruent to 3 mod 4.** For a
prime $p \equiv 3 \pmod 4$, the length $g(p)$ of the longest arithmetic progression in the
absolute least reduced residue system modulo $p$ is $(p + 1)/2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_of_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 3) : absLeastAPLength p = (p + 1) / 2

/-- **Longest progressions of absolute least residues: prime powers.** Let $p$ be a prime and
$r \ge 1$, with $r \ge 2$ when $p$ is odd. Then the length $g(p^r)$ of the longest arithmetic
progression in the absolute least reduced residue system modulo $p^r$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (h : p = 2 ∨ 2 ≤ r) : absLeastAPLength (p ^ r) = p ^ (r - 1)

/-- **Longest progressions of absolute least residues: odd squarefree composite moduli.** Let
$n > 1$ be an odd squarefree natural number that is not prime, let $P$ be its largest prime
factor and $d = n / P$, and let $g(n)$ be the length of the longest arithmetic progression in the
absolute least reduced residue system modulo $n$. Then
$g(n) = \lfloor P - (P + 1)/(2d) \rfloor$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_odd_squarefree {n : ℕ} (hn : 1 < n) (hodd : Odd n)
    (hsq : Squarefree n) (hnp : ¬ n.Prime) :
    (absLeastAPLength n : ℤ) =
      ⌊((n.primeFactors.sup id : ℕ) : ℚ) -
        ((n.primeFactors.sup id : ℕ) + 1) / (2 * ((n / n.primeFactors.sup id : ℕ) : ℚ))⌋

/-- **Longest progressions of absolute least residues: neither squarefree nor prime power.** Let
$n > 1$ be a natural number that is neither squarefree nor a prime power, let
$\operatorname{rad}(n)$ be the product of the distinct primes dividing $n$ and $P$ the largest
prime factor of $n$, and let $g(n)$ be the length of the longest arithmetic progression in the
absolute least reduced residue system modulo $n$. Then
$g(n) = \max(n / \operatorname{rad}(n), P - 1)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_of_not_squarefree_of_not_isPrimePow {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    absLeastAPLength n = max (n / radical n) (n.primeFactors.sup id - 1)

/-- **Longest progressions of absolute least residues: even squarefree, three or more primes.**
Let $n$ be an even squarefree natural number with at least three prime factors, let $P$ be its
largest prime factor and $d = n / P$, and let $g(n)$ be the length of the longest arithmetic
progression in the absolute least reduced residue system modulo $n$. Then
$\lfloor P - 2P/d \rfloor \le g(n) \le P - 1$, and if $d \ge 2P$ then $g(n) = P - 1$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 1 (`integers-2026-A6-thm-1`). -/
public theorem_wanted absLeastAPLength_even_squarefree_bounds {n : ℕ} (heven : Even n)
    (hsq : Squarefree n) (h3 : 3 ≤ n.primeFactors.card) :
    (⌊((n.primeFactors.sup id : ℕ) : ℚ) -
        2 * (n.primeFactors.sup id : ℕ) / ((n / n.primeFactors.sup id : ℕ) : ℚ)⌋ ≤
        (absLeastAPLength n : ℤ) ∧
      absLeastAPLength n ≤ n.primeFactors.sup id - 1) ∧
    (2 * n.primeFactors.sup id ≤ n / n.primeFactors.sup id →
      absLeastAPLength n = n.primeFactors.sup id - 1)

/-- **Maximum longest progression length over all reduced residue windows.** Let $n > 1$ be a
natural number, $\operatorname{rad}(n)$ the product of its distinct prime factors and
$\operatorname{gpf}(n)$ its largest prime factor. For an integer $m$ let $f_m(n)$ be the length of
the longest arithmetic progression with positive common difference contained in the set $R_m(n)$
of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then the largest value of
$f_m(n)$ over all integers $m$ is $\max(n / \operatorname{rad}(n), \operatorname{gpf}(n) - 1)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 2 (`integers-2026-A6-thm-2`). -/
public theorem_wanted isGreatest_longestAPLength {n : ℕ} (hn : 1 < n) :
    IsGreatest (Set.range fun m : ℤ => longestAPLength m n)
      (max (n / radical n) (n.primeFactors.sup id - 1))

/-- **Minimum longest progression length modulo a prime $p \equiv 1 \pmod 4$.** Let $p$ be a prime
with $p \equiv 1 \pmod 4$. For an integer $m$ let $f_m(p)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p)$ of integers $a$ with
$m + 1 \le a \le m + p$ and $\gcd(a, p) = 1$. Then the least value of $f_m(p)$ over all integers
$m$ is $(p - 1) / 2$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_of_mod_four_eq_one {p : ℕ} (hp : p.Prime)
    (h4 : p % 4 = 1) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m p) ((p - 1) / 2)

/-- **Minimum longest progression length modulo a prime power.** Let $p$ be a prime and $r > 1$ a
natural number. For an integer $m$ let $f_m(p^r)$ be the length of the longest arithmetic
progression with positive common difference contained in the set $R_m(p^r)$ of integers $a$ with
$m + 1 \le a \le m + p^r$ and $\gcd(a, p^r) = 1$. Then the least value of $f_m(p^r)$ over all
integers $m$ is $p^{r-1}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted isLeast_longestAPLength_prime_pow {p r : ℕ} (hp : p.Prime) (hr : 1 < r) :
    IsLeast (Set.range fun m : ℤ => longestAPLength m (p ^ r)) (p ^ (r - 1))

/-- **Minimum longest progression length when $n$ is neither squarefree nor a prime power.** Let
$n > 1$ be a natural number that is neither squarefree nor a prime power, $\operatorname{rad}(n)$
the product of its distinct prime factors and $\operatorname{gpf}(n)$ its largest prime factor.
For an integer $m$ let $f_m(n)$ be the length of the longest arithmetic progression with positive
common difference contained in the set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and
$\gcd(a, n) = 1$. Then $f_m(n) \ge n / \operatorname{rad}(n)$ for every integer $m$, and
$f_m(n) \le \max(n / \operatorname{rad}(n), \operatorname{gpf}(n) - 1)$ for some integer $m$.
If moreover $\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$, then the least value of
$f_m(n)$ over all integers $m$ is $n / \operatorname{rad}(n)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 3 (`integers-2026-A6-thm-3`). -/
public theorem_wanted longestAPLength_min_of_not_squarefree_of_not_isPrimePow {n : ℕ}
    (hn : 1 < n) (hsq : ¬ Squarefree n) (hpp : ¬ IsPrimePow n) :
    ((∀ m : ℤ, n / radical n ≤ longestAPLength m n) ∧
      ∃ m : ℤ, longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1)) ∧
    (n.primeFactors.sup id - 1 ≤ n / radical n →
      IsLeast (Set.range fun m : ℤ => longestAPLength m n) (n / radical n))

/-- **Average longest progression length for non-squarefree moduli.** Let $n > 1$ be a natural
number that is not squarefree, $\operatorname{rad}(n)$ the product of its distinct prime factors
and $\operatorname{gpf}(n)$ its largest prime factor, and suppose that
$\operatorname{gpf}(n) - 1 \le n / \operatorname{rad}(n)$. For an integer $m$ let $f_m(n)$ be the
length of the longest arithmetic progression with positive common difference contained in the
set $R_m(n)$ of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then
$\frac{1}{n} \sum_{m=0}^{n-1} f_m(n) = \frac{n}{\operatorname{rad}(n)}$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Corollary 1 (`integers-2026-A6-cor-1`). -/
public theorem_wanted average_longestAPLength_of_not_squarefree {n : ℕ} (hn : 1 < n)
    (hsq : ¬ Squarefree n) (h : n.primeFactors.sup id - 1 ≤ n / radical n) :
    (1 / (n : ℚ)) * ∑ m ∈ Finset.range n, (longestAPLength m n : ℚ) = (n : ℚ) / radical n

end

end MetaMathlibExt
