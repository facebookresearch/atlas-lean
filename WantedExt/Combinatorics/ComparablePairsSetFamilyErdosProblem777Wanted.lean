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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #777, https://www.erdosproblems.com/777 (status
SOLVED). UnsolvedMath record UM-30007028 (`EP-777`), dataset ulamai/UnsolvedMath v1.8.0.

The edges of `G_F` are the pairs `(A, B)` of members with `A ⊊ B`. Each question is stated as posed:
(1) for all large `n`; (2) for every `c > 0` some constant `C` bounds `m ≤ C 2^{n/2}` for all `n`;
(3) for all `n`. formal-conjectures has no statement of this problem.
-/

open Classical in
/-- **Number of comparable pairs.** For $n \in \mathbb{N}$ and a family $F$ of subsets of
$\{0, \dots, n - 1\}$, the number of comparable pairs of $F$ is the number of ordered pairs
$(A, B)$ of members of $F$ with $A \subsetneq B$. It is the number of edges of the comparability
graph $G_F$ on $F$, in which two distinct members are adjacent when one contains the other. -/
noncomputable def comparablePairs {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ :=
  ((F ×ˢ F).filter fun p => p.1 ⊂ p.2).card

/-- **Erdős Problem 777, first question.** For every real $\varepsilon > 0$ there is $N$ such that
for every $n \ge N$, every family $F$ of subsets of $\{0, \dots, n - 1\}$ with
$|F| \le (2 - \varepsilon) 2^{n/2}$ has fewer than $2^n$ comparable pairs, that is, ordered pairs
$(A, B)$ of members of $F$ with $A \subsetneq B$. -/
def fewComparablePairsBelowTwoHalfPower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset (Fin n)),
    (F.card : ℝ) ≤ (2 - ε) * 2 ^ ((n : ℝ) / 2) → comparablePairs F < 2 ^ n

/-- **Erdős Problem 777, second question.** For every real $c > 0$ there is a real constant $C$
such that for every $n$ and every family $F$ of subsets of $\{0, \dots, n - 1\}$ with at least
$c |F|^2$ comparable pairs (ordered pairs $(A, B)$ of members of $F$ with $A \subsetneq B$), we
have $|F| \le C \cdot 2^{n/2}$. -/
def denseComparabilityFamilySmall : Prop :=
  ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    c * (F.card : ℝ) ^ 2 ≤ comparablePairs F → (F.card : ℝ) ≤ C * 2 ^ ((n : ℝ) / 2)

/-- **Erdős Problem 777, third question.** For every real $\varepsilon > 0$ there is a real
$\delta > 0$ such that for every $n$, every family $F$ of subsets of $\{0, \dots, n - 1\}$ with
more than $|F|^{2 - \delta}$ comparable pairs (ordered pairs $(A, B)$ of members of $F$ with
$A \subsetneq B$) satisfies $|F| < (2 + \varepsilon)^{n/2}$. -/
def nearlyCompleteComparabilityFamilySmall : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    (F.card : ℝ) ^ (2 - δ) < comparablePairs F → (F.card : ℝ) < (2 + ε) ^ ((n : ℝ) / 2)

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

/--
**Negative answer to Erdős Problem 777, second question.** It is not the case that for every
real $c > 0$ there is a real constant $C$ such that for every $n$ and every family $F$ of subsets
of $\{0, \dots, n - 1\}$ with at least $c |F|^2$ comparable pairs (ordered pairs $(A, B)$ of
members of $F$ with $A \subsetneq B$), we have $|F| \le C \cdot 2^{n/2}$. Equivalently, there is
a real $c > 0$ such that for every real $C$ some $n$ and some family $F$ of subsets of
$\{0, \dots, n - 1\}$ with at least $c |F|^2$ comparable pairs have $|F| > C \cdot 2^{n/2}$.

Alon and Frankl's Example 6.1 with $d = 1$ gives such families: $m \gg n 2^{n/2}$ subsets of an
$n$-element set with at least $2^{-5} \binom{m}{2}$ comparable pairs (erdosproblems.com/777).

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
public theorem_wanted denseComparabilityFamilySmall_refuted : ¬ denseComparabilityFamilySmall

/--
**Affirmative answer to Erdős Problem 777, third question.** For every real $\varepsilon > 0$
there is a real $\delta > 0$ such that for every $n$, every family $F$ of subsets of
$\{0, \dots, n - 1\}$ with more than $|F|^{2 - \delta}$ comparable pairs (ordered pairs $(A, B)$
of members of $F$ with $A \subsetneq B$) satisfies $|F| < (2 + \varepsilon)^{n/2}$.

According to erdosproblems.com/777 this follows from the case $k = 1$ of Theorem 1.4 of Alon and
Frankl, conjectured by Daykin and Erdős: there is $\beta > 0$ such that for every $\eta > 0$, a
family of $m = 2^{(1/2 + \eta) n}$ subsets of an $n$-element set has $O(m^{2 - \beta \eta^2})$
comparable pairs.

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
public theorem_wanted nearlyCompleteComparabilityFamilySmall_holds :
    nearlyCompleteComparabilityFamilySmall

end MathlibExt.Combinatorics.ComparablePairsSetFamilyErdosProblem777Wanted
