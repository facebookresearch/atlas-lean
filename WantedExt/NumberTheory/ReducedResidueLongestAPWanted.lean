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
public import MathlibExt.NumberTheory.ReducedResidueAverage
public import MathlibExt.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimeOfModFourEqOne
public import MathlibExt.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimeOfModFourEqOne
public import MathlibExt.NumberTheory.ReducedResidueLongestAPLongestAPLengthMinOfNotSquarefreeOfNotIsPrimePow
public import MathlibExt.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimePow
public import MathlibExt.NumberTheory.ReducedResidueLongestAPIsLeastLongestAPLengthPrimePow
public import MathlibExt.NumberTheory.ReducedResidueLongestAPIsGreatestLongestAPLength

/-!
# Longest arithmetic progressions in the reduced residue systems `R_m(n)`

For integers `m` and `n > 1`, Phothila, Thoket and Kanasri study the reduced residue system
`R_m(n) = {a ∈ ℤ | m + 1 ≤ a ≤ m + n, gcd(a, n) = 1}` modulo `n`, the length `f_m(n)` of the
longest arithmetic progressions contained in it, the length `f_m(d, n)` of the longest ones
with common difference `d`, and `g(n) = f_{-⌈n/2⌉}(n)` for the system of absolute least
reduced residues. Throughout, `gpf(n)` is written `n.primeFactors.sup id` (the largest prime
factor of `n` for `n > 1`) and `rad(n)` is `UniqueFactorizationMonoid.radical n`.

The definitions, the squarefree fixed-difference bound, the formula for twice an odd prime, and
the absolute least residue formula and minimum for primes congruent to three modulo four are in
`MathlibExt.NumberTheory.ReducedResidueLongestAP`. The formula for `g(p)` for primes congruent
to one modulo four is in
`MathlibExt.NumberTheory.ReducedResidueLongestAPAbsLeastAPLengthPrimeOfModFourEqOne`.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

@[expose] public section

open UniqueFactorizationMonoid

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

end

end MetaMathlibExt
