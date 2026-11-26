/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.WeaklyDecreasingWordPairs
public import MathlibExt.Combinatorics.Enumerative.WeaklyDecreasingWordPairsBivariate
public import MathlibExt.Combinatorics.Enumerative.WordPairIntersections
public import MathlibExt.Combinatorics.Enumerative.WordPairOverlap

/-!
# Intersections in pairs of words

Statements from Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*,
INTEGERS 24 (2024), Article A107.

A word of length `n` over the alphabet `[k]` is a map `Fin n → Fin k`; a pair `(u, v)` is
non-intersecting when no letter occurs in both, and the overlap statistic (tracked by `q`) is the
number of positions of `v` whose letter occurs in `u`. Weakly decreasing words are `Antitone`
maps. The paper's generating functions run over pairs of non-empty words (`x^n y^r`, `n, r ≥ 1`).
A two-variable generating function that factors as `A(x) B(y)` is stated coefficientwise:
`[x^n y^r] A(x)B(y) = [x^n]A · [y^r]B`, with `A`, `B` in `ℚ⟦X⟧`; `q` is a rational parameter
(an identity of polynomials in `q` holds iff it holds for every `q : ℚ`); Corollary 4 is stated in
`MvPowerSeries (Fin 2) ℚ` with `x = X 0`, `y = X 1`. `S_{n,j}` is `Nat.stirlingSecond n j`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Generating function of non-intersecting pairs of words of equal length.** Let $k$ be a
natural number, let $S(n, j)$ denote the Stirling numbers of the second kind, and for $n \ge 1$ let
$h(n)$ be the number of pairs $(u, v)$ of words of length $n$ over an alphabet of $k$ letters such
that no letter occurs in both. Then, as formal power series over $\mathbb{Q}$,
$\sum_{n \ge 1} h(n) x^n = \sum_{n \ge 0} \sum_{j=1}^{k-1} \binom{k}{j} \, j! \, S(n, j) \,
(k-j)^n x^n$.

The constant term on the right is $0$ because $S(0, j) = 0$ for $j \ge 1$: the empty pair is not
counted.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Corollary 1 (`integers-2024-A107-cor-1`). -/
public theorem_wanted nonIntersectingWordPairs_sameLength_generatingFunction (k : ℕ) :
    (PowerSeries.mk fun n => if n = 0 then (0 : ℚ) else
        (((Finset.univ : Finset ((Fin n → Fin k) × (Fin n → Fin k))).filter fun p => Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ)) =
      PowerSeries.mk fun n => ∑ j ∈ Finset.Icc 1 (k - 1),
        (k.choose j : ℚ) * j.factorial * Nat.stirlingSecond n j * ((k - j : ℕ) : ℚ) ^ n

/-- **Non-intersecting pairs of weakly decreasing words.** Fix natural numbers $k$, $n \ge 1$ and
$r \ge 1$, and order an alphabet of $k$ letters. Write $[x^m] F$ for the coefficient of $x^m$ in a
formal power series $F$ over $\mathbb{Q}$. The number of pairs $(u, v)$ of weakly decreasing words
over this alphabet, $u$ of length $n$ and $v$ of length $r$, such that no letter occurs in both is
$\sum_{j=1}^{k-1} \binom{k}{j} \, [x^n]\bigl(x^j (1-x)^{-j}\bigr) \,
[x^r]\bigl((1-x)^{-(k-j)} - 1\bigr)$.

Source: Aubrey Blecher and Arnold Knopfmacher, *Intersections in Pairs of Words*, INTEGERS 24 (2024),
Article A107, Theorem 3 (`integers-2024-A107-thm-3`). -/
public theorem_wanted weaklyDecreasingNonIntersectingPairs_card_eq_coeff (k n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) :
    (((Finset.univ : Finset ((Fin n → Fin k) × (Fin r → Fin k))).filter fun p => Antitone p.1 ∧
        Antitone p.2 ∧ Disjoint (Finset.univ.image p.1) (Finset.univ.image p.2)).card : ℚ) =
      ∑ j ∈ Finset.Icc 1 (k - 1), (k.choose j : ℚ) * coeff n (X ^ j * ((1 - X) ^ j)⁻¹ : ℚ⟦X⟧) *
        coeff r ((((1 - X) ^ (k - j))⁻¹ - 1 : ℚ⟦X⟧))

end

end MetaMathlibExt
