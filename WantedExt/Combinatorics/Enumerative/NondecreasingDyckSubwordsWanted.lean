/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.NondecreasingDyckSubwords

/-!
# Subwords in non-decreasing Dyck paths

Statements from Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in
Non-Decreasing Dyck Paths*, Journal of Integer Sequences 28 (2025), Article
25.1.6. Dyck paths are Mathlib's `DyckWord`s. A Dyck path is non-decreasing when
the heights of its valley vertices (the low points of the factors `DU`), read
from left to right, form a non-decreasing sequence; this is the `0`-Dyck case
of Flórez and Ramírez, *Restricted Dyck paths on valleys sequence*,
arXiv:2108.08299, Section 1. A subword is a contiguous factor, and
`nondecreasingDyckSubwordTotal w n` is the total number of occurrences of `w`
(overlapping occurrences counted separately) summed over the non-decreasing
Dyck paths of semilength `n`. The bivariate generating function
`F_w(x, y) = ∑_{n ≥ 1} ∑_{P} x^n y^{#w(P)}` is a power series in `x` with
coefficients in `ℤ[y]`, and the univariate `D_w(x) = ∑ d_w(n) x^n`. Generating
function identities are stated with the denominator cleared, and the closed
forms with the rational factor cleared, over `ℤ`.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- The variable `x` of the bivariate generating functions. -/
local notation "𝒙" => (PowerSeries.X : PowerSeries (Polynomial ℤ))
/-- The variable `y` of the bivariate generating functions, a constant in `ℤ[y]`. -/
local notation "𝒚" => PowerSeries.C (Polynomial.X : Polynomial ℤ)
/-- The variable `x` of the univariate generating functions. -/
local notation "𝒛" => (PowerSeries.X : PowerSeries ℤ)

/-- **Generating functions and closed form for the subwords $UU$ and $DD$ in non-decreasing Dyck
paths.** Let $w$ be $UU$ or $DD$. For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing
Dyck paths of semilength $n$, let $\#_w(P)$ be the number of occurrences of the subword $w$ in a
path $P$, and let $d_w(n) = \sum_{P \in \mathcal{D}_n} \#_w(P)$. Let
$F_w(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_w(P)} x^n$, a power series in $x$
with coefficients in $\mathbb{Z}[y]$, and $D_w(x) = \sum_{n \ge 0} d_w(n) x^n$ in
$\mathbb{Z}[[x]]$. Then $(1 - x - 2xy + x^2 y^2) F_w(x, y) = x (1 - xy)$ and
$(1 - 3x + x^2)^2 D_w(x) = x^2 (1 - x + x^2)$, and for every $n \ge 1$,
$$10\, d_w(n) = (7 - 10n) F_{2n} + (6n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 3
(`jis-2025-25.1.6-thm-3`). -/
public theorem_wanted nondecreasingDyck_subword_UU_DD (w : List DyckStep)
    (hw : w = [U, U] ∨ w = [D, D]) :
    (1 - 𝒙 - 2 * 𝒙 * 𝒚 + 𝒙 ^ 2 * 𝒚 ^ 2) * nondecreasingDyckSubwordBivariateGF w =
      𝒙 * (1 - 𝒙 * 𝒚) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF w = 𝒛 ^ 2 * (1 - 𝒛 + 𝒛 ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      10 * (nondecreasingDyckSubwordTotal w n : ℤ) =
        (7 - 10 * (n : ℤ)) * (Nat.fib (2 * n) : ℤ) + (6 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- **Generating functions and closed form for the subword $UDD$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UDD}(P)$ be the number of occurrences of the subword $UDD$ in a path $P$, and let
$d_{UDD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UDD}(P)$. Let
$F_{UDD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UDD}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UDD}(x) = \sum_{n \ge 0} d_{UDD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then
$$(1 - 3x + x^2 (2 - y)) (1 - 2x + x^2 (1 - y)) F_{UDD}(x, y) = (1 - x)(1 - 2x)(1 - x(1 - y)) x$$
and
$$(1 - 2x)(1 - 3x + x^2)^2 D_{UDD}(x) = (1 - x)(1 - 3x + 2x^2 - x^3) x^2,$$
and for every $n \ge 2$,
$$5\, d_{UDD}(n) = (5n - 9) F_{2n} + (5 - 2n) L_{2n} - 5 \cdot 2^{n-2},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 6
(`jis-2025-25.1.6-thm-6`). -/
public theorem_wanted nondecreasingDyck_subword_UDD :
    ((1 - 3 * 𝒙 + 𝒙 ^ 2 * (2 - 𝒚)) * (1 - 2 * 𝒙 + 𝒙 ^ 2 * (1 - 𝒚)))
        * nondecreasingDyckSubwordBivariateGF [U, D, D]
        = (1 - 𝒙) * (1 - 2 * 𝒙) * (1 - 𝒙 * (1 - 𝒚)) * 𝒙 ∧
    ((1 - 2 * 𝒛) * (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, D, D]
        = (1 - 𝒛) * (1 - 3 * 𝒛 + 2 * 𝒛 ^ 2 - 𝒛 ^ 3) * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 2 ≤ n →
      5 * (nondecreasingDyckSubwordTotal [U, D, D] n : ℤ) =
        (5 * (n : ℤ) - 9) * (Nat.fib (2 * n) : ℤ) + (-2 * (n : ℤ) + 5) * (lucasNumber (2 * n) : ℤ)
            - 5 * 2 ^ (n - 2)

/-- **The subword $DUU$ in non-decreasing Dyck paths.** Let $F_{DUU}(x, y)$ and $D_{DUU}(x)$ be
the bivariate and univariate generating functions of the subword $DUU$ in non-decreasing Dyck
paths, let $d_{DUU}(n)$ be the total number of occurrences of $DUU$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - 3x + x^2(3 - 2y) - x^3(1 - y)) F_{DUU}(x, y) = x - x^2 + x^3(1 - y)$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DUU}(x) = x^3$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$10 d_{DUU}(n) = -(5n + 4) F_{2n} + 3n L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 7
(`jis-2025-25.1.6-thm-7`). -/
public theorem_wanted nondecreasingDyck_subword_DUU :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (3 - 2 * 𝒚) - 𝒙 ^ 3 * (1 - 𝒚))
        * nondecreasingDyckSubwordBivariateGF [D, U, U] = 𝒙 - 𝒙 ^ 2 + 𝒙 ^ 3 * (1 - 𝒚) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U, U] = 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, U, U] n : ℤ) =
        -(5 * (n : ℤ) + 4) * (Nat.fib (2 * n) : ℤ) + 3 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DUD$ in non-decreasing Dyck paths.** Let $F_{DUD}(x, y)$ and $D_{DUD}(x)$ be
the bivariate and univariate generating functions of the subword $DUD$ in non-decreasing Dyck
paths, let $d_{DUD}(n)$ be the total number of occurrences of $DUD$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - x^2(1 - 2y) + x^3(1 - y) - x(2 + y)) F_{DUD}(x, y) = x (1 - x - x^2(1 - y))$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DUD}(x) = x^2 - 2x^3$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$5 d_{DUD}(n) = (5n + 1) F_{2n} - 2n L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 8
(`jis-2025-25.1.6-thm-8`). -/
public theorem_wanted nondecreasingDyck_subword_DUD :
    (1 - 𝒙 ^ 2 * (1 - 2 * 𝒚) + 𝒙 ^ 3 * (1 - 𝒚) - 𝒙 * (2 + 𝒚))
        * nondecreasingDyckSubwordBivariateGF [D, U, D] = 𝒙 * (1 - 𝒙 - 𝒙 ^ 2 * (1 - 𝒚)) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, U, D] = 𝒛 ^ 2 - 2 * 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      5 * (nondecreasingDyckSubwordTotal [D, U, D] n : ℤ) =
        (5 * (n : ℤ) + 1) * (Nat.fib (2 * n) : ℤ) - 2 * (n : ℤ) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DDU$ in non-decreasing Dyck paths.** Let $F_{DDU}(x, y)$ and $D_{DDU}(x)$ be
the bivariate and univariate generating functions of the subword $DDU$ in non-decreasing Dyck
paths, let $d_{DDU}(n)$ be the total number of occurrences of $DDU$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - 3x + x^2(2 - y)) F_{DDU}(x, y) = (1 - x) x$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 3x + x^2)^2 D_{DDU}(x) = (1 - x) x^3$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$10 d_{DDU}(n) = (10n - 13) F_{2n} + (-4n + 5) L_{2n}.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 9
(`jis-2025-25.1.6-thm-9`). -/
public theorem_wanted nondecreasingDyck_subword_DDU :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (2 - 𝒚)) * nondecreasingDyckSubwordBivariateGF [D, D, U] = (1 - 𝒙) * 𝒙 ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, D, U] = (1 - 𝒛) * 𝒛 ^ 3 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [D, D, U] n : ℤ) =
        (10 * (n : ℤ) - 13) * (Nat.fib (2 * n) : ℤ) + (-4 * (n : ℤ) + 5) * (lucasNumber (2 * n) : ℤ)

/-- **The subword $DDD$ in non-decreasing Dyck paths.** Let $F_{DDD}(x, y)$ and $D_{DDD}(x)$ be
the bivariate and univariate generating functions of the subword $DDD$ in non-decreasing Dyck
paths, let $d_{DDD}(n)$ be the total number of occurrences of $DDD$ over all non-decreasing Dyck
paths of semilength $n$, and let $F_n$ and $L_n$ denote the Fibonacci and Lucas numbers. Then
$$(1 - x(1 + y) - x^2(1 - y)) (1 - x(1 + 2y) - x^2(1 - y - y^2)) F_{DDD}(x, y) =
x (1 - xy) (1 - 2xy - x^2(1 - y^2))$$
in $\mathbb{Z}[y][[x]]$,
$$(1 - 2x) (1 - 3x + x^2)^2 D_{DDD}(x) = x^3 (1 - 2x + x^2 - x^3)$$
in $\mathbb{Z}[[x]]$, and for every $n \ge 3$,
$$4 d_{DDD}(n) = (-8n + 10) F_{2n} + (4n - 6) L_{2n} + 2^n.$$

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 10
(`jis-2025-25.1.6-thm-10`). -/
public theorem_wanted nondecreasingDyck_subword_DDD :
    ((1 - 𝒙 * (1 + 𝒚) - 𝒙 ^ 2 * (1 - 𝒚)) * (1 - 𝒙 * (1 + 2 * 𝒚) - 𝒙 ^ 2 * (1 - 𝒚 - 𝒚 ^ 2)))
        * nondecreasingDyckSubwordBivariateGF [D, D, D]
        = 𝒙 * (1 - 𝒙 * 𝒚) * (1 - 2 * 𝒙 * 𝒚 - 𝒙 ^ 2 * (1 - 𝒚 ^ 2)) ∧
    ((1 - 2 * 𝒛) * (1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [D, D, D]
        = 𝒛 ^ 3 * (1 - 2 * 𝒛 + 𝒛 ^ 2 - 𝒛 ^ 3) ∧
    ∀ n : ℕ, 3 ≤ n →
      4 * (nondecreasingDyckSubwordTotal [D, D, D] n : ℤ) =
        (-8 * (n : ℤ) + 10) * (Nat.fib (2 * n) : ℤ) + (4 * (n : ℤ) - 6) * (lucasNumber (2 * n) : ℤ)
            + 2 ^ n

/-- **Generating functions and closed form for the subword $UUD$ in non-decreasing Dyck paths.**
For $n \ge 0$ let $\mathcal{D}_n$ be the set of non-decreasing Dyck paths of semilength $n$, let
$\#_{UUD}(P)$ be the number of occurrences of the subword $UUD$ in a path $P$, and let
$d_{UUD}(n) = \sum_{P \in \mathcal{D}_n} \#_{UUD}(P)$. Let
$F_{UUD}(x, y) = \sum_{n \ge 1} \sum_{P \in \mathcal{D}_n} y^{\#_{UUD}(P)} x^n$, a power series
in $x$ with coefficients in $\mathbb{Z}[y]$, and $D_{UUD}(x) = \sum_{n \ge 0} d_{UUD}(n) x^n$ in
$\mathbb{Z}[[x]]$. Then
$$(1 - 3x + x^2 (3 - 2y) - x^3 (1 - y)) F_{UUD}(x, y) = (1 - x) x (1 - x(1 - y))$$
and $(1 - 3x + x^2)^2 D_{UUD}(x) = (1 - x)^2 x^2$, and for every $n \ge 3$,
$$10\, d_{UUD}(n) = (11 - 5n) F_{2n} + (3n - 5) L_{2n},$$
where $F_k$ and $L_k$ are the Fibonacci and Lucas numbers ($F_0 = 0$, $F_1 = 1$, $L_0 = 2$,
$L_1 = 1$).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 11
(`jis-2025-25.1.6-thm-11`). -/
public theorem_wanted nondecreasingDyck_subword_UUD :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 * (3 - 2 * 𝒚) - 𝒙 ^ 3 * (1 - 𝒚))
        * nondecreasingDyckSubwordBivariateGF [U, U, D] = (1 - 𝒙) * 𝒙 * (1 - 𝒙 * (1 - 𝒚)) ∧
    ((1 - 3 * 𝒛 + 𝒛 ^ 2) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, D] = (1 - 𝒛) ^ 2 * 𝒛 ^ 2 ∧
    ∀ n : ℕ, 3 ≤ n →
      10 * (nondecreasingDyckSubwordTotal [U, U, D] n : ℤ) =
        (-5 * (n : ℤ) + 11) * (Nat.fib (2 * n) : ℤ) + (3 * (n : ℤ) - 5) * (lucasNumber (2 * n) : ℤ)

/-- **Subword $UUUD$ in non-decreasing Dyck paths.** Let $F_{UUUD}(x, y) \in \mathbb{Z}[y][[x]]$ be
the bivariate generating function with constant term $0$ in which, for $n \ge 1$, the coefficient
of $x^n$ is the sum of $y^{k(P)}$ over the non-decreasing Dyck paths $P$ of semilength $n$, where
$k(P)$ is the number of occurrences of the subword $UUUD$ in $P$. Let $d_{UUUD}(n)$ be the total
number of occurrences of $UUUD$ over all non-decreasing Dyck paths of semilength $n$, let
$D_{UUUD}(x) = \sum_{n \ge 0} d_{UUUD}(n) x^n \in \mathbb{Z}[[x]]$, and let $F_n$ and $L_n$ denote
the Fibonacci and Lucas numbers. Then
$(1 - 3x + x^2 + (3 - 3y) x^3 - 2(1 - y) x^4) F_{UUUD}(x, y) = (1 - x)(x + x^3 (y - 1))$,
$(1 + x(x - 3))^2 D_{UUUD}(x) = (x - 1)^2 x^3 (x + 1)$, and for every $n \ge 3$,
$d_{UUUD}(n) = n F_{2n-5} - L_{2n-6}$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 12
(`jis-2025-25.1.6-thm-12`). -/
public theorem_wanted nondecreasingDyck_subword_UUUD :
    (1 - 3 * 𝒙 + 𝒙 ^ 2 + (3 - 3 * 𝒚) * 𝒙 ^ 3 - 2 * (1 - 𝒚) * 𝒙 ^ 4)
        * nondecreasingDyckSubwordBivariateGF [U, U, U, D] = (1 - 𝒙) * (𝒙 + 𝒙 ^ 3 * (𝒚 - 1)) ∧
    ((1 + 𝒛 * (𝒛 - 3)) ^ 2) * nondecreasingDyckSubwordTotalGF [U, U, U, D]
        = (𝒛 - 1) ^ 2 * 𝒛 ^ 3 * (𝒛 + 1) ∧
    ∀ n : ℕ, 3 ≤ n →
      (nondecreasingDyckSubwordTotal [U, U, U, D] n : ℤ) =
        (n : ℤ) * (Nat.fib (2 * n - 5) : ℤ) - (lucasNumber (2 * n - 6) : ℤ)

/-- **Recurrence for the subword $U^m$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n > m$,
$$d_{U^m}(n) = 3\,d_{U^m}(n-1) - d_{U^m}(n-2) + F_{2(n-m)} + F_{2(n-2)} -
\sum_{k=1}^{m-2} k\,F_{2(n-k-2)}$$
(the sum is empty when $m \le 2$); moreover $d_{U^m}(n) = 0$ for every $n < m$, and
$d_{U^m}(m) = 1$.

The source writes $n \le m$ for the vanishing case, which contradicts $d_{U^m}(m) = 1$; the
vanishing case is stated for $n < m$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 13
(`jis-2025-25.1.6-thm-13`). -/
public theorem_wanted nondecreasingDyck_subword_U_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n →
      (nondecreasingDyckSubwordTotal (List.replicate m U) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m)) : ℤ) + (Nat.fib (2 * (n - 2)) : ℤ)
          - ∑ k ∈ Finset.Icc 1 (m - 2), (k : ℤ) * (Nat.fib (2 * (n - k - 2)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U) m = 1

/-- **Recurrence for the subword $U^mD$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$). Then for every
$n \ge m + 2$,
$$d_{U^mD}(n) = 3\,d_{U^mD}(n-1) - d_{U^mD}(n-2) + F_{2(n-m)-3} + m\,F_{2(n-m-1)};$$
moreover $d_{U^mD}(n) = 0$ for every $n < m$, $d_{U^mD}(m) = 1$, and $d_{U^mD}(m+1) = m + 2$.

The source states the recurrence for $n \ge m$, where $n = m$ and $n = m + 1$ give negative
Fibonacci indices; those two values are the separately stated initial values, and the recurrence
is stated for $n \ge m + 2$.

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 15
(`jis-2025-25.1.6-thm-15`). -/
public theorem_wanted nondecreasingDyck_subword_U_pow_D (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m + 2 ≤ n →
      (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m) - 3) : ℤ) + (m : ℤ) * (Nat.fib (2 * (n - m - 1)) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) n = 0) ∧
    nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) m = 1 ∧
    nondecreasingDyckSubwordTotal (List.replicate m U ++ [D]) (m + 1) = m + 2

/-- **Recurrence for the subword $UD^m$ in non-decreasing Dyck paths.** Let $m \ge 1$. Let
$d_w(n)$ be the total number of occurrences of the subword $w$ over all non-decreasing Dyck paths
of semilength $n$, let $l_{n,k}$ be the number of non-decreasing Dyck paths of semilength $n$
whose last peak has height $k$, and let $F_k$ be the Fibonacci numbers ($F_0 = 0$, $F_1 = 1$).
Then for every $n$ with $n > m$ and $n \ge 3$,
$$d_{UD^m}(n) = 3\,d_{UD^m}(n-1) - d_{UD^m}(n-2) + F_{2(n-m)-1} + l_{n-1,m-1} - l_{n-2,m-1};$$
moreover $d_{UD^m}(n) = 0$ for every $n < m$, and $d_{UD^m}(m) = 1$.

The source states the recurrence for $n \ge m$; $n = m$ is the separately stated initial value,
and the added condition $n \ge 3$ excludes only $(m, n) = (1, 2)$, where $d_{UD}(2) = 3$ but the
right side is $3 \cdot 1 - 0 + F_1 + l_{1,0} - l_{0,0} = 4$ (the empty path has no peak).

Source: Flórez, Junes, Montoya, and Ramírez, *Counting Subwords in Non-Decreasing
Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.1.6, Theorem 16
(`jis-2025-25.1.6-thm-16`). -/
public theorem_wanted nondecreasingDyck_subword_U_D_pow (m : ℕ) (hm : 1 ≤ m) :
    (∀ n : ℕ, m < n → 3 ≤ n →
      (nondecreasingDyckSubwordTotal (U :: List.replicate m D) n : ℤ) =
        3 * (nondecreasingDyckSubwordTotal (U :: List.replicate m D) (n - 1) : ℤ)
          - (nondecreasingDyckSubwordTotal (U :: List.replicate m D) (n - 2) : ℤ)
          + (Nat.fib (2 * (n - m) - 1) : ℤ)
          + (nondecreasingDyckLastPeakCount (n - 1) (m - 1) : ℤ)
          - (nondecreasingDyckLastPeakCount (n - 2) (m - 1) : ℤ)) ∧
    (∀ n : ℕ, n < m → nondecreasingDyckSubwordTotal (U :: List.replicate m D) n = 0) ∧
    nondecreasingDyckSubwordTotal (U :: List.replicate m D) m = 1

end

end MetaMathlibExt
