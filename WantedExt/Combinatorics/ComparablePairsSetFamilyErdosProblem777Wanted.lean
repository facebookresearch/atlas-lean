/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Comparable pairs in set families (Erdős Problem 777)

Erdős Problem 777 (Daykin and Erdős): for a family `F` of `m` subsets of `{1, …, n}` let `G_F` be
the graph on `F` in which `A ∼ B` if `A ⊆ B` or `B ⊆ A`. (1) If `ε > 0` and `n` is large, does `m ≤
(2 - ε) 2^{n/2}` force fewer than `2^n` edges? (2) If `G_F` has at least `c m²` edges, is `m ≪_c
2^{n/2}`? (3) For every `ε > 0` is there `δ > 0` such that more than `m^{2 - δ}` edges force `m < (2
+ ε)^{n/2}`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777

@[expose] public section

namespace MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #777, https://www.erdosproblems.com/777 (status
SOLVED). UnsolvedMath record UM-30007028 (`EP-777`), dataset ulamai/UnsolvedMath v1.8.0.

The edges of `G_F` are the pairs `(A, B)` of members with `A ⊊ B`. Each question is stated as posed:
(1) for all large `n`; (2) for every `c > 0` some constant `C` bounds `m ≤ C 2^{n/2}` for all `n`;
(3) for all `n`. formal-conjectures has no statement of this problem.
-/

/--
**Affirmative answer to Erdős Problem 777, first question.** For every real $\varepsilon > 0$
there is $N$ such that for every $n \ge N$, every family $F$ of subsets of $\{0, \dots, n - 1\}$
with $|F| \le (2 - \varepsilon) 2^{n/2}$ has fewer than $2^n$ comparable pairs, that is, ordered
pairs $(A, B)$ of members of $F$ with $A \subsetneq B$.

The bound is sharp: for even $n$, a family of $m = 2^{n/2 + 1}$ subsets formed by two stacked
subcubes has at least $2^n$ comparable pairs. According to erdosproblems.com/777 the affirmative
answer follows from Theorem 1.4 and Corollary 1.5 of Alon, Das, Glebov and Sudakov.

Source: T. F. Bloom, Erdős Problems, Problem #777, https://www.erdosproblems.com/777 (status
SOLVED); resolution: N. Alon and P. Frankl, The maximum number of disjoint pairs in a family of
subsets, Graphs Combin. 1 (1985), 13-21; N. Alon, S. Das, R. Glebov and B. Sudakov, Comparable
pairs in families of sets, J. Combin. Theory Ser. B (2015), 164-185, arXiv:1411.4196, Alon-Frankl
Theorem 1.4: for every k ≥ 1 there is β(k) > 0 such that for m = 2^{(1/(k+1) + δ)n}, c(n, m) <
(1 - 1/k) C(m, 2) + O(m^{2 - β δ^{k+1}}), the case k = 1 conjectured by Daykin and Erdős;
Alon-Frankl Section 6, Example 6.1: the sets meeting the second half of [n] in at most d elements
or missing at most d elements of the first half form a family of Θ(n^d 2^{n/2}) sets with a
constant fraction of comparable pairs, disproving a conjecture of Erdős; erdosproblems.com/777:
Alon and Frankl answer the third question in the affirmative and the second in the negative, and
an affirmative answer to the first follows from Theorem 1.4 and Corollary 1.5 of Alon, Das,
Glebov and Sudakov, https://www.erdosproblems.com/777.
-/
public theorem_wanted fewComparablePairsBelowTwoHalfPower_holds :
    fewComparablePairsBelowTwoHalfPower

end MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted
