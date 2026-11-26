/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two combinatorial interpretations of Rascal numbers

Statements from Amelia Gibbs and Brian K. Miceli, "Two
Combinatorial Interpretations of Rascal Numbers", *Journal
of Integer Sequences* 27 (2024), Article 24.8.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Miceli/miceli9.html>;
arXiv:2405.11045).

The Rascal numbers `R_{n,k}` are defined in the paper by the
diamond recurrence of Angorro et al. together with the value
`0` outside `0 ≤ k ≤ n`; since Angorro et al. proved
`R_{n,k} = k(n-k) + 1` in range, `rascalZ` is defined
directly by that closed form on `ℤ`. The paper's `B_k(n)`
(binary words of length `n` with exactly `k` ones and at most
one ascent) and its generalization `B_k^{(j)}(n)` (at most `j`
ascents) are the list subtypes `RascalWord 1 k n` and
`RascalWord j k n`, with counts `rascalGen j k n` (the
generalized Rascal numbers `R_{n,k}^{(j)}`), extended to `ℤ`
by `0` out of range as `rascalGenZ`. The paper's
`\mathcal{A}_{\{001,210\}}(n, k)` (ascent sequences of length
`n` avoiding the patterns `001` and `210`, with exactly `k`
ascents) is `AscentSeqAvoid n k` with count `apkCard`;
pattern containment is order-isomorphic subsequence
(`List.Sublist`) as in the paper.

Corrections to the printed statements, each found by brute
force and verified numerically: Theorem 19's summation
index is `i` (the printed binder is `r`), and it needs
`k ≤ n`; Theorem 23 uses the paper's convention
`\binom{-1}{j} = (-1)^j` at `n = 0`. The corrections to
Theorems 4, 6 and 10 are recorded with their proofs in
`MathlibExt.Combinatorics.Enumerative.RascalNumberIdentities`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.RascalNumberIdentities
public import MathlibExt.Combinatorics.Enumerative.RascalNumbers
public import MathlibExt.Combinatorics.Enumerative.RascalWordEnds
public import MathlibExt.Combinatorics.Enumerative.RascalWords

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

/-- **Shape of ascent sequences avoiding 001 and 210.** Let $n$ and $k$ be natural numbers and
let $w$ be an ascent sequence of length $n$ with exactly $k$ ascents that avoids the patterns
$001$ and $210$. Then either $w$ consists of $0, 1, \ldots, k-1$ followed by $n - k$ copies of
$k$, or there are natural numbers $x$ and $y$ with $1 \le y < n - k$ and $x < k$ such that $w$
consists of $0, 1, \ldots, k-1$, followed by $y$ copies of $k$, followed by $n - k - y$ copies
of $x$. When $k = 0$ the initial part $0, 1, \ldots, k-1$ is empty.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Lemma 16. -/
theorem_wanted ascentSeqAvoid_form (n k : ℕ)
    (w : AscentSeqAvoid n k) :
    w.1 = List.range k ++ List.replicate (n - k) k ∨
      ∃ y x : ℕ, 1 ≤ y ∧ y < n - k ∧ x < k ∧
        w.1 = List.range k ++ List.replicate y k ++
          List.replicate (n - k - y) x

/-- **Ascent sequences avoiding 001 and 210 are counted by Rascal numbers.** For all natural
numbers $n$ and $k$, the number of ascent sequences of length $n + 1$ with exactly $k$ ascents
that avoid the patterns $001$ and $210$ equals the Rascal number $R_{n,k}$, which is
$k(n-k) + 1$ when $k \le n$ and $0$ when $k > n$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 17. -/
theorem_wanted apkCard_succ_eq_rascalZ (n k : ℕ) :
    (apkCard (n + 1) k : ℤ) = rascalZ (n : ℤ) (k : ℤ)

/-- **Generalized Rascal numbers as sums of products of binomial coefficients.** For all natural
numbers $j$, $n$ and $k$ with $k \le n$, the generalized Rascal number $R^{(j)}_{n,k}$, the
number of binary words of length $n$ with exactly $k$ ones and at most $j$ ascents (positions
where a $0$ is immediately followed by a $1$), equals
$\sum_{i=0}^{j} \binom{k}{i} \binom{n-k}{i}$.

The hypothesis $k \le n$ is needed: for $k > n$ the left side is $0$, while the right side,
with $n - k$ read as $0$, is $1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 19. -/
theorem_wanted rascalGen_eq_sum (j n k : ℕ) (hkn : k ≤ n) :
    (rascalGen j k n : ℤ) =
      ∑ i ∈ Finset.range (j + 1),
        (Nat.choose k i : ℤ) * (Nat.choose (n - k) i : ℤ)

/-- **Row sums of generalized Rascal numbers.** Write $R^{(j)}_{n,k}$ for the number of binary
words of length $n$ with exactly $k$ ones and at most $j$ ascents (positions where a $0$ is
immediately followed by a $1$). For all natural numbers $j$ and $n$,
$\sum_{k=0}^{n} R^{(j)}_{n,k} = \sum_{k=0}^{2j+1} \binom{n}{k}$, where $\binom{n}{k} = 0$ for
$k > n$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 20. -/
theorem_wanted sum_rascalGen_row (j n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (rascalGen j k n : ℤ) =
      ∑ k ∈ Finset.range (2 * j + 2), (Nat.choose n k : ℤ)

/-- **Forward differences of generalized Rascal row sums.** Fix a natural number $j$. For natural
numbers $n$ and $k$ let $R^{(j)}_{n,k}$ be the number of binary words of length $n$ with exactly
$k$ ones and at most $j$ ascents, and let $S(n) = \sum_{k=0}^{n} R^{(j)}_{n,k}$. Then
$(\Delta^{2j+1} S)(n) = 1$ for every natural number $n$, where $\Delta$ is the forward
difference $(\Delta a)(n) = a(n+1) - a(n)$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 22. -/
theorem_wanted iterate_forwardDiff_sum_rascalGen (j n : ℕ) :
    ((fun a : ℕ → ℤ => fun m => a (m + 1) - a m)^[2 * j + 1]
      (fun m => ∑ k ∈ Finset.range (m + 1),
        rascalGenZ j (m : ℤ) (k : ℤ))) n = 1

/-- **Alternating row sums of generalized Rascal numbers vanish on odd rows.** Write
$R^{(j)}_{n,k}$ for the number of binary words of length $n$ with exactly $k$ ones and at most
$j$ ascents (positions where a $0$ is immediately followed by a $1$). For all natural numbers
$j$ and $m$, $\sum_{k=0}^{2m+1} (-1)^k R^{(j)}_{2m+1,k} = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 23. -/
theorem_wanted sum_rascalGen_alternating_odd (j m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2),
        (-1 : ℤ) ^ k * (rascalGen j k (2 * m + 1) : ℤ) = 0

/-- **Alternating row sums of generalized Rascal numbers on even rows.** Write $R^{(j)}_{n,k}$ for
the number of binary words of length $n$ with exactly $k$ ones and at most $j$ ascents
(positions where a $0$ is immediately followed by a $1$). For natural numbers $j$ and $m$ with
$m \ge 1$, $\sum_{k=0}^{2m} (-1)^k R^{(j)}_{2m,k} = (-1)^j \binom{m-1}{j}$, and for $m = 0$ the
sum equals $1$.

This is the paper's formula with the convention $\binom{-1}{j} = (-1)^j$ at $m = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 23. -/
theorem_wanted sum_rascalGen_alternating_even (j m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ k * (rascalGen j k (2 * m) : ℤ) =
      (-1 : ℤ) ^ j *
        (if m = 0 then (-1 : ℤ) ^ j else (Nat.choose (m - 1) j : ℤ))

/-- **Generalized Rascal numbers count subsets with few small elements.** For all natural numbers
$j$, $n$ and $k$, the generalized Rascal number $R^{(j)}_{n,k}$ equals the number of $k$-element
subsets of $\{0, 1, \dots, n-1\}$ that have at most $j$ elements smaller than $n - k$.

Shifting by one, these are the $k$-element subsets of $\{1, \dots, n\}$ meeting
$\{1, \dots, n-k\}$ in at most $j$ elements, which is Gregory et al.'s interpretation of
$\binom{n}{k}_j$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 24. -/
theorem_wanted rascalGen_eq_card_subset (j n k : ℕ) :
    rascalGen j k n =
      Nat.card { S : Finset (Fin n) // S.card = k ∧
        (S.filter (fun i => i.val < n - k)).card ≤ j }

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
