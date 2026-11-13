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
`R_{n,k} = k(n-k) + 1` in range, `rascalZ` below is defined
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
force and verified numerically: Fleron's recurrence
(Theorem 4) holds only for `0 < k < n` (at `k = 0` or `k = n`
the right side is `2`, not `1`); Theorem 6 as printed fails
for `k > n` and needs `k ≤ n`; Theorem 10 as printed has
`2^{n-2}` where the correct exponent is `n - 1` (at `n = 2`
the sum is `6`, the printed right side is `5`), stated below
doubled to avoid negative exponents; Theorem 19's summation
index is `i` (the printed binder is `r`), and it needs
`k ≤ n`; Theorem 23 uses the paper's convention
`\binom{-1}{j} = (-1)^j` at `n = 0`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

/-- **Number of ascents of a word.** For a finite word
$w = w_1 w_2 \cdots w_n$ of natural numbers, the number of ascents
of $w$ is the number of indices $i$ with $1 \le i < n$ and
$w_i < w_{i+1}$. -/
def wordAscents : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a < b then 1 else 0) + wordAscents (b :: t)

/-- **Rascal numbers on the integers.** For integers $n$ and $k$, the Rascal number $R_{n,k}$ is
$k(n-k) + 1$ if $0 \le k \le n$, and $0$ otherwise.

Gibbs and Miceli define $R_{n,k}$ by the diamond recurrence of Angorro et al., with value $0$
outside $0 \le k \le n$; Angorro et al. proved that it equals $k(n-k) + 1$ in that range. -/
def rascalZ (n k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k ≤ n then k * (n - k) + 1 else 0

/-- **Binary words with few ascents.** For natural numbers $j$, $k$ and $n$, $B^{(j)}_k(n)$ is
the set of words $w$ of length $n$ over the alphabet $\{0, 1\}$ with exactly $k$ ones and at most
$j$ ascents, an ascent being a position $i$ with $w_i < w_{i+1}$, that is, a $0$ immediately
followed by a $1$. -/
def RascalWord (j k n : ℕ) : Type :=
  { w : List ℕ // w.length = n ∧ (∀ x ∈ w, x = 0 ∨ x = 1) ∧
      w.count 1 = k ∧ wordAscents w ≤ j }

/-- **Generalized Rascal numbers.** For natural numbers $j$, $k$ and $n$, the generalized Rascal
number $R^{(j)}_{n,k}$ is the number of binary words of length $n$ with exactly $k$ ones and at
most $j$ ascents, that is, the number of elements of $B^{(j)}_k(n)$; an ascent is a position at
which a $0$ is immediately followed by a $1$. -/
noncomputable def rascalGen (j k n : ℕ) : ℕ :=
  Nat.card (RascalWord j k n)

/-- **Generalized Rascal numbers at integer indices.** For a natural number $j$ and integers $n$
and $k$, $R^{(j)}_{n,k}$ is the generalized Rascal number of $n$ and $k$ (the number of binary
words of length $n$ with exactly $k$ ones and at most $j$ ascents) when $0 \le k \le n$, and $0$
otherwise. -/
noncomputable def rascalGenZ (j : ℕ) (n k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k ≤ n then (rascalGen j k.toNat n.toNat : ℤ) else 0

/-- **Ascent sequences.** A finite sequence $w_1 w_2 \cdots w_n$ of natural numbers is an
ascent sequence when $w_1 = 0$ (if $n \ge 1$) and
$w_i \le \operatorname{asc}(w_1 \cdots w_{i-1}) + 1$ for every $1 \le i \le n$, where
$\operatorname{asc}(v)$ counts the positions $j$ with $v_j < v_{j+1}$. In particular the empty
sequence is an ascent sequence. -/
def IsAscentSeq (w : List ℕ) : Prop :=
  (∀ h : 0 < w.length, w[0]'h = 0) ∧
    ∀ (i : ℕ) (h : i < w.length), w[i]'h ≤ wordAscents (w.take i) + 1

/-- **Avoiding the patterns 001 and 210.** A finite sequence $w$ of natural numbers avoids
$001$ and $210$ when it has no subsequence $x, x, y$ with $x < y$ and no subsequence $x, y, z$
with $x > y > z$. Subsequences need not consist of consecutive entries. -/
def Avoids001210 (w : List ℕ) : Prop :=
  ∀ x y z : ℕ, List.Sublist [x, y, z] w →
    ¬ (x = y ∧ y < z) ∧ ¬ (z < y ∧ y < x)

/-- **Ascent sequences avoiding 001 and 210.** For natural numbers $n$ and $k$, this is the set
of ascent sequences $w$ of length $n$ that avoid the patterns $001$ and $210$ and have exactly
$k$ ascents, an ascent of $w$ being a position $i$ with $w_i < w_{i+1}$. -/
def AscentSeqAvoid (n k : ℕ) : Type :=
  { w : List ℕ // w.length = n ∧ IsAscentSeq w ∧ Avoids001210 w ∧
      wordAscents w = k }

/-- **Number of ascent sequences avoiding 001 and 210.** For natural numbers $n$ and $k$, this
counts the ascent sequences of length $n$ with exactly $k$ ascents that avoid the patterns
$001$ and $210$. -/
noncomputable def apkCard (n k : ℕ) : ℕ :=
  Nat.card (AscentSeqAvoid n k)

/-- **Rascal numbers count binary words with at most one ascent.** For all integers $n$ and $k$,
$R_{n,k} = b_k(n)$, where $R_{n,k}$ is the Rascal number and $b_k(n)$ is the number of binary
words of length $n$ with exactly $k$ ones and at most one ascent (taken to be $0$ unless
$0 \le k \le n$).

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 1. -/
theorem_wanted rascalZ_eq_rascalGenZ_one (n k : ℤ) :
    rascalZ n k = rascalGenZ 1 n k

/-- **Symmetry of Rascal numbers.** For integers $n$ and $k$ with $0 \le k \le n$, the Rascal
numbers satisfy $R_{n,k} = R_{n,n-k}$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 2. -/
theorem_wanted rascalZ_symm (n k : ℤ) (h0 : 0 ≤ k) (h1 : k ≤ n) :
    rascalZ n k = rascalZ n (n - k)

/-- **Binary words with a prefix of ones and a suffix of zeros.** Let $n, k, \ell, u$ be natural
numbers with $\ell \le k$ and $k + u \le n$, and let $B_k(n)$ be the set of binary words $w$ of
length $n$ with exactly $k$ ones and at most one ascent (a position $i$ with $w_i < w_{i+1}$).
The number of words in $B_k(n)$ whose first $\ell$ letters are all $1$ and whose last $u$
letters are all $0$ equals the Rascal number $R_{n-u-\ell, k-\ell}$, where
$R_{a,b} = b(a-b) + 1$ for $0 \le b \le a$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Lemma 3. -/
theorem_wanted card_prefixOnes_suffixZeros (n k ℓ u : ℕ)
    (hℓ : ℓ ≤ k) (hu : k + u ≤ n) :
    (Nat.card { w : RascalWord 1 k n //
        (∀ x ∈ w.1.take ℓ, x = 1) ∧
          (∀ x ∈ w.1.drop (n - u), x = 0) } : ℤ) =
      rascalZ (n - u - ℓ : ℕ) (k - ℓ : ℕ)

/-- **Fleron's recurrence for Rascal numbers.** For integers $n$ and $k$ with $n \ge 2$ and
$0 < k < n$, the Rascal numbers $R_{n,k}$ satisfy
$R_{n,k} = R_{n-1,k} + R_{n-1,k-1} - R_{n-2,k-1} + 1$.

The hypothesis $0 < k < n$ is needed: at $k = 0$ or $k = n$ the right side equals $2$ while
$R_{n,k} = 1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 4. -/
theorem_wanted rascalZ_fleron (n k : ℤ) (hn : 2 ≤ n)
    (hk0 : 0 < k) (hkn : k < n) :
    rascalZ n k = rascalZ (n - 1) k + rascalZ (n - 1) (k - 1) -
      rascalZ (n - 2) (k - 1) + 1

/-- **Generalized diamond recurrence for Rascal numbers.** For integers $n$, $k$, $\ell$, $u$
with $\ell \ge 0$, $u \ge 0$ and $\ell \le k \le n - u$, the Rascal numbers satisfy
$R_{n,k} R_{n-u-\ell,k-\ell} = R_{n-u,k} R_{n-\ell,k-\ell} + u\ell$.

Since $R_{n-u-\ell,k-\ell} \ge 1$ under these hypotheses, this is the paper's formula
$R_{n,k} = (R_{n-u,k} R_{n-\ell,k-\ell} + u\ell) / R_{n-u-\ell,k-\ell}$ cleared of denominators.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 5. -/
theorem_wanted rascalZ_mul_eq (n k ℓ u : ℤ) (hℓ : 0 ≤ ℓ)
    (hu : 0 ≤ u) (h : ℓ ≤ k) (h2 : k ≤ n - u) :
    rascalZ n k * rascalZ (n - u - ℓ) (k - ℓ) =
      rascalZ (n - u) k * rascalZ (n - ℓ) (k - ℓ) + u * ℓ

/-- **Row-shift identity for the Rascal numbers.** For integers $n$, $m$ and $k$ with $m \ge 0$
and $0 \le k \le n$,
$$R_{n+m,k} = R_{n,k} + R_{m+k,k} - 1,$$
where $R_{a,b}$ denotes the Rascal numbers, which vanish unless $0 \le b \le a$.

The hypothesis $k \le n$, absent from the printed statement, is needed: for $n = 0$, $m = 1$ and
$k = 2$ the left side is $R_{1,2} = 0$ while the right side is $0 + 3 - 1 = 2$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 6. -/
theorem_wanted rascalZ_add_eq (n m k : ℤ) (hm : 0 ≤ m)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    rascalZ (n + m) k = rascalZ n k + rascalZ (m + k) k - 1

/-- **Diagonal recurrence for Rascal numbers.** For integers $n$ and $k$ with $0 < k < n$,
$$k R_{n-1,k-1} - 1 = (k-1) R_{n,k},$$
where $R_{a,b}$ is the Rascal number, equal to $b(a-b) + 1$ for $0 \le b \le a$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 7. -/
theorem_wanted mul_rascalZ_sub_one (n k : ℤ) (hk0 : 0 < k)
    (hkn : k < n) :
    k * rascalZ (n - 1) (k - 1) - 1 = (k - 1) * rascalZ n k

/-- **Row sums of the Rascal triangle.** For every natural number
$n$, the Rascal numbers $R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$)
satisfy $\sum_{k=0}^{n} R_{n,k} = \binom{n+1}{3} + n + 1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 8. -/
theorem_wanted sum_rascalZ_row (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), rascalZ (n : ℤ) (k : ℤ) =
      (Nat.choose (n + 1) 3 : ℤ) + (n : ℤ) + 1

/-- **Column sums of the Rascal triangle.** For all natural numbers
$k$ and $r$, the Rascal numbers $R_{n,k} = k(n-k) + 1$
($0 \le k \le n$) satisfy
$\sum_{i=0}^{r} R_{k+i,k} = k \binom{r+1}{2} + r + 1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 9. -/
theorem_wanted sum_rascalZ_column (k r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), rascalZ ((k + i : ℕ) : ℤ) (k : ℤ) =
      (k : ℤ) * (Nat.choose (r + 1) 2 : ℤ) + (r : ℤ) + 1

/-- **Binomial-weighted row sums of the Rascal triangle.** For
every natural number $n$, the Rascal numbers
$R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$) satisfy
$2 \sum_{k=0}^{n} \binom{n}{k} R_{n,k} = 2^n \binom{n}{2} + 2^{n+1}$.

The paper prints the exponent $n - 2$ where the correct exponent
is $n - 1$ in $\sum_{k} \binom{n}{k} R_{n,k} = 2^{n-1} \binom{n}{2} + 2^n$
(at $n = 2$ the sum is $6$, not $5$); the identity is stated
doubled so that no exponent is negative at $n = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 10. -/
theorem_wanted two_mul_sum_choose_mul_rascalZ (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * rascalZ (n : ℤ) (k : ℤ) =
      2 ^ n * (Nat.choose n 2 : ℤ) + 2 ^ (n + 1)

/-- **Sum of the interior Rascal numbers.** For every natural
number $n \ge 2$, the Rascal numbers $R_{i,j} = j(i-j) + 1$
($0 \le j \le i$) satisfy
$\sum_{i=1}^{n} \sum_{j=1}^{i-1} R_{i,j} = \binom{n+2}{4} + \binom{n}{2}$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 11. -/
theorem_wanted sum_sum_rascalZ (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (i - 1),
        rascalZ (i : ℤ) (j : ℤ) =
      (Nat.choose (n + 2) 4 : ℤ) + (Nat.choose n 2 : ℤ)

/-- **Vanishing higher finite differences of Rascal numbers.** For natural numbers $n$, $k$ and
$r$ with $k \le n$ and $r \ge 2$, the Rascal numbers satisfy
$\sum_{j=0}^{r} (-1)^{r-j} \binom{r}{j} R_{n+j,k} = 0$.

For $k \le n$ the value $R_{n+j,k}$ is a linear function of $j$, and the sum is its $r$-th
finite difference.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 12. -/
theorem_wanted sum_negOnePow_choose_rascalZ (n k r : ℕ)
    (hkn : k ≤ n) (hr : 2 ≤ r) :
    ∑ j ∈ Finset.range (r + 1),
        (-1 : ℤ) ^ (r - j) * (Nat.choose r j : ℤ) *
          rascalZ ((n + j : ℕ) : ℤ) (k : ℤ) = 0

/-- **Alternating row sums of the Rascal triangle, odd rows.**
For every natural number $m$, the Rascal numbers
$R_{n,k} = k(n-k) + 1$ ($0 \le k \le n$) satisfy
$\sum_{k=0}^{2m+1} (-1)^k R_{2m+1,k} = 0$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 13. -/
theorem_wanted sum_rascalZ_alternating_odd (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2),
        (-1 : ℤ) ^ k * rascalZ ((2 * m + 1 : ℕ) : ℤ) (k : ℤ) = 0

/-- **Alternating row sums of Rascal numbers on even rows.** For every natural number $m$, the
Rascal numbers satisfy $\sum_{k=0}^{2m} (-1)^k R_{2m,k} = 1 - m$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 13. -/
theorem_wanted sum_rascalZ_alternating_even (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ k * rascalZ ((2 * m : ℕ) : ℤ) (k : ℤ) =
      1 - (m : ℤ)

/-- **Subset-sum expansion of the product of the shifted Rascal numbers.** For natural numbers
$m$ and $n$ with $1 \le m \le n$, writing $[m] = \{1, \dots, m\}$,
$$\prod_{k=1}^{m} (R_{n,k} - 1) = \sum_{S \subseteq [m]} (-1)^{m-|S|} \prod_{i \in S} R_{n,i},$$
where $R_{n,k}$ denotes the Rascal numbers.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 14. -/
theorem_wanted prod_rascalZ_sub_one_eq_sum (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) =
      ∑ S ∈ (Finset.Icc 1 m).powerset,
        (-1 : ℤ) ^ (m - S.card) *
          ∏ i ∈ S, rascalZ (n : ℤ) (i : ℤ)

/-- **Closed form for the product of the shifted Rascal numbers.** For natural numbers $m$ and
$n$ with $1 \le m \le n$,
$$\prod_{k=1}^{m} (R_{n,k} - 1) = m! \, (n-1)^{\underline{m}},$$
where $R_{n,k}$ denotes the Rascal numbers and $x^{\underline{m}} = x(x-1)\cdots(x-m+1)$ is the
falling factorial.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 14. -/
theorem_wanted prod_rascalZ_sub_one_eq_factorial_mul (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) =
      (m.factorial : ℤ) * (Nat.descFactorial (n - 1) m : ℤ)

/-- **Binomial coefficients from products of Rascal numbers.** For natural numbers $n$ and $m$
with $1 \le m \le n$,
$$(m!)^2 \binom{n-1}{m} = \prod_{k=1}^{m} (R_{n,k} - 1),$$
where $R_{n,k} = k(n-k) + 1$ is the Rascal number for $0 \le k \le n$.

Equivalently, $\frac{1}{(m!)^2} \prod_{k=1}^{m} (R_{n,k} - 1) = \binom{n-1}{m}$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 15. -/
theorem_wanted factorial_sq_mul_choose_eq_prod (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (m.factorial : ℤ) ^ 2 * (Nat.choose (n - 1) m : ℤ) =
      ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1)

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

/-- **Generalized Fleron recurrence.** Let $j \ge 1$ be a natural number and let $n$ and $k$ be
integers with $n \ge 2$ and $0 \le k \le n$. Then
$$R^{(j)}_{n,k} = R^{(j)}_{n-1,k} + R^{(j)}_{n-1,k-1} - R^{(j)}_{n-2,k-1} + R^{(j-1)}_{n-2,k-1},$$
where $R^{(i)}_{a,b}$ is the generalized Rascal number for integer indices, taken to be $0$ unless
$0 \le b \le a$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 18. -/
theorem_wanted rascalGenZ_fleron (j : ℕ) (hj : 1 ≤ j)
    (n k : ℤ) (hn : 2 ≤ n) (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    rascalGenZ j n k = rascalGenZ j (n - 1) k +
      rascalGenZ j (n - 1) (k - 1) - rascalGenZ j (n - 2) (k - 1) +
      rascalGenZ (j - 1) (n - 2) (k - 1)

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

/-- **A power-of-two row sum of generalized Rascal numbers.** Write $R^{(j)}_{n,k}$ for the number
of binary words of length $n$ with exactly $k$ ones and at most $j$ ascents (positions where a
$0$ is immediately followed by a $1$). For every natural number $j$,
$\sum_{k=0}^{4j+3} R^{(j)}_{4j+3,k} = 2^{4j+2}$.

This was Conjecture 7.5 of Gregory et al.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 21. -/
theorem_wanted sum_rascalGen_four_mul_add_three (j : ℕ) :
    ∑ k ∈ Finset.range (4 * j + 4),
        (rascalGen j k (4 * j + 3) : ℤ) = 2 ^ (4 * j + 2)

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
