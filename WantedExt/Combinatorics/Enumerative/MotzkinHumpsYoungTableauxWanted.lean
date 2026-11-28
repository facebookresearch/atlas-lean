/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.AdjustedSytHookCount
public import MathlibExt.Combinatorics.Enumerative.MotzkinFirstDownLastUp
public import MathlibExt.Combinatorics.Enumerative.MotzkinHumpGeneratingFunction
public import MathlibExt.Combinatorics.Enumerative.MotzkinNumber
public import MathlibExt.Combinatorics.Enumerative.SytHookCountGeneratingFunction

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Closed formula for hook tableau counts.** For natural numbers $n$ and $k$ with
$k + 2 \le n$, let $\mathrm{SYT}_k(2,1;n)$ be the number of standard Young tableaux of order $n$
in the $(2,1)$-hook whose first row is longer than its second row by exactly $k$. Then, as an
identity of rational numbers,
$$
\mathrm{SYT}_k(2,1;n) = (-1)^{n+k} + \sum_{i=0}^{\lfloor (n-k-1)/2 \rfloor}
\sum_{\substack{0 \le j \le n-k-1-2i \\ j \equiv n+k-1 \pmod 2}}
\frac{2k+2}{n+k+1-2i-j} \binom{n-2i-2}{j} \binom{n-2i-j-1}{\frac{n+k-j-1}{2} - i}.
$$

When $k = 0$ and $2i = n - 1$, the upper argument $n - 2i - 2$ would be $-1$; it is read as $0$,
so the only term of that inner sum, $j = 0$, has binomial factor $\binom{0}{0} = 1$.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Theorem 2 (`jis-2025-25.8.1-thm-2`).
-/
public theorem_wanted sytHookCount_closedForm (n k : ℕ) (hk : k + 2 ≤ n) :
    (sytHookCount n k : ℚ) =
      (-1 : ℚ) ^ (n + k) +
        ∑ i ∈ Finset.range ((n - k - 1) / 2 + 1),
          ∑ j ∈ Finset.range (n - k - 1 - 2 * i + 1),
            (if j % 2 = (n + k - 1) % 2 then (1 : ℚ) else 0) *
              ((2 * k + 2 : ℕ) : ℚ) / ((n + k + 1 - 2 * i - j : ℕ) : ℚ) *
              (Nat.choose (n - 2 * i - 2) j : ℚ) *
              (Nat.choose (n - 2 * i - j - 1) ((n + k - j - 1) / 2 - i) : ℚ)

/-- **Humps correspond to last-up prefixes of twice the height.** Use the steps $U = (1,1)$,
$F = (1,0)$ and $D = (1,-1)$. A Motzkin prefix of length $n$ ending at height $h$ is a word of
$n$ steps that never goes below height $0$ and ends at height $h$; a Motzkin path is a Motzkin
prefix ending at height $0$. A hump of height $k$ in a path is a pair of an up step and a later
down step with only flat steps between them, where the up step ends at height $k$; the hump is
a peak when the down step immediately follows the up step. For every natural number $n$ there
is a bijection from the set of triples $(k, P, h)$ with $1 \le k \le \lfloor n/2 \rfloor$, $P$
a Motzkin path of length $n$ and $h$ a hump of height $k$ in $P$, to the set of pairs $(k, p)$
with $1 \le k \le \lfloor n/2 \rfloor$ and $p$ a Motzkin prefix of length $n$ ending at height
$2k$ that contains a $U$ after which every step is $F$. This bijection keeps the index $k$, and
the hump $h$ is a peak exactly when the image path $p$ ends with an up step.

Source: Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal
        of Integer Sequences 28 (2025), Article 25.8.1, Lemma 3 (`jis-2025-25.8.1-lem-3`).
-/
public theorem_wanted motzkinHumpFamily_equiv_lastUpEvenFamily (n : ℕ) :
    ∃ e : MotzkinHumpFamily n ≃ MotzkinLastUpEvenFamily n,
      (∀ q, (e q).val.1 = q.val.1) ∧
        ∀ q, IsMotzkinPeak n q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ↔
          EndsWithUp n (e q).val.2

end

end MetaMathlibExt
