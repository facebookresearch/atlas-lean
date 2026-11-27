/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PolygonalSumParity
public import MathlibExt.NumberTheory.PracticalNumber
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.PracticalPolygonalSums
public import MathlibExt.NumberTheory.OddSquareTriangular
public import MathlibExt.NumberTheory.PracticalPolygonalSumsPracticalAddPolygonalExceptions
public import MathlibExt.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow
public import MathlibExt.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne

/-!
# Sums of practical numbers and polygonal numbers

Statements from Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and
Polygonal Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1
(arXiv:2403.13533). The statement `MetaMathlibExt.exists_sq_add_sq_modEq_prime_pow` is in
`MathlibExt.NumberTheory.PracticalPolygonalSumsExistsSqAddSqModEqPrimePow`. In the paper
"natural number" means positive integer; practical numbers
are `MetaMathlibExt.IsPracticalNumber`. The paper's `s`-gonal number `P_s(n)` is the canonical
`Nat.polygonalNumber s n`; triangular numbers are `Nat.polygonalNumber 3 k = k (k + 1) / 2`
with `k ≥ 0` (the paper's Lemma 5, arXiv Lemma 3.3, counts `0`).
-/

namespace MetaMathlibExt

@[expose] public section

open ArithmeticFunction
open scoped Nat

/-- **Every positive integer is a practical number plus a triangular number.** For every natural
number $n > 0$ there are a practical number $q$ and a natural number $k$ with
$n = q + k(k+1)/2$; the case $k = 0$, where the triangular number is $0$, is allowed.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 1
(`jis-2024-24.5.1-thm-1`). -/
public theorem_wanted exists_practical_add_triangular (n : ℕ) (hn : 0 < n) :
    ∃ q k : ℕ, IsPracticalNumber q ∧ n = q + Nat.polygonalNumber 3 k

/-- **Large integers as a practical number plus two polygonal numbers.** Let $s > 3$ be a natural
number and, for a natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th
$s$-gonal number, so that $P_s(0) = 0$. There is a natural number $N$ such that every natural
number $n > N$ can be written as $n = q + P_s(x) + P_s(y)$ with $q$ a practical number and
$x, y$ natural numbers.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 2
(`jis-2024-24.5.1-thm-2`). -/
public theorem_wanted eventually_practical_add_two_polygonal (s : ℕ) (hs : 3 < s) :
    ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
      IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s x + Nat.polygonalNumber s y

/-- **Sums of two polygonal numbers modulo prime powers.** For a natural number $s > 3$ and a
natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th $s$-gonal number. There
is a prime $p$ with $p \equiv 1 \pmod{4}$ and $p \nmid s - 2$ such that for all natural numbers
$k > 0$ and $n > 0$ there are natural numbers $x, y > 0$ with
$P_s(x) + P_s(y) \equiv n \pmod{p^k}$.

The paper's statement asks only for an odd prime; the condition $p \equiv 1 \pmod{4}$ is the
choice made in its proof via Lemma 8 (arXiv Lemma 4.3).

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 9
(arXiv Lemma 4.4; `jis-2024-24.5.1-lem-9`). -/
public theorem_wanted exists_prime_polygonal_add_polygonal_modEq_prime_pow (s : ℕ)
    (hs : 3 < s) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ ¬ p ∣ s - 2 ∧ ∀ k n : ℕ, 0 < k → 0 < n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p ^ k]

end

end MetaMathlibExt
