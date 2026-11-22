/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Explicit formulas for Bernoulli and Genocchi numbers

Statements from Schehrazade Zerroukhat and Laala Khaldi,
"A Note on Explicit Formulas for Bernoulli and Genocchi
Numbers", *Journal of Integer Sequences* 28 (2025),
Article 25.6.7
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>).

Notation: `Bₙ` is Mathlib's `bernoulli`, `Gₙ` is
MathlibExt's `genocchiNumber`, `S(n,k)` is
`Nat.stirlingSecond`, and `Δ` is the forward-difference
operator, with `Δᵏ xⁿ` evaluated at `x` written
`diffPowEval x k n` (the paper's `Δᵏ0ⁿ` and `Δᵏ1ⁿ` are
the cases `x = 0, 1`). The paper's auxiliary sums
`U(m,k) = ∑_{j ≥ 0} (-1)^{k+j+m} (k+j-1)!/2^{k+j-1} S(m,j)`
(finite, since `S(m,j) = 0` for `j > m`) and
`H_{n,m} = (-1)ⁿ n ∑_{k ≥ 1} U(m+1,k) S(n-m,k)` are
`zerroU` and `zerroH`. The first equality of Theorem 1,
`2(1-2ⁿ)Bₙ = Gₙ`, is MathlibExt's proved
`genocchiNumber_eq_bernoulli`; the declaration below
states the second equality. All identities were verified
by exact rational computation before stating.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.GenocchiNumber

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.GenocchiExplicitWanted

/-- **Iterated forward differences of a power on $\mathbb{Q}$.** For a rational number $x$ and
natural numbers $k$ and $n$, $\Delta^k x^n$ denotes the value at $x$ of the $k$-th iterate of the
forward difference operator applied to the function $y \mapsto y^n$ on $\mathbb{Q}$, where the
forward difference of $f \colon \mathbb{Q} \to \mathbb{Q}$ is the function
$y \mapsto f(y + 1) - f(y)$. -/
noncomputable def diffPowEval (x : ℚ) (k n : ℕ) : ℚ :=
  ((fun f : ℚ → ℚ => fun y => f (y + 1) - f y)^[k]
    (fun y => y ^ n)) x

/-- **The Zerroukhat–Khaldi sum $U(m, k)$.** For natural numbers $m$ and $k$, define the rational
number
$$U(m, k) = \sum_{j=0}^{m} (-1)^{k+j+m} \frac{(k+j-1)!}{2^{k+j-1}} S(m, j),$$
where $S(m, j)$ is the Stirling number of the second kind and, in the term with $k = j = 0$,
$k + j - 1$ is read as $0$, so that this term is $(-1)^m S(m, 0)$. -/
def zerroU (m k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℚ) ^ (k + j + m) * ((k + j - 1).factorial : ℚ) /
      2 ^ (k + j - 1) * (Nat.stirlingSecond m j : ℚ)

/-- **The Zerroukhat–Khaldi sum $H_{n,m}$.** For natural numbers $n$ and $m$, define the rational
number
$$H_{n,m} = (-1)^n \, n \sum_{k=1}^{n-m} U(m+1, k) \, S(n-m, k),$$
where $U(m+1, k)$ is the Zerroukhat–Khaldi sum $U$, $S(n-m, k)$ is the Stirling number of the
second kind, and $n - m$ is truncated at $0$, so that $H_{n,m} = 0$ when $m \ge n$. -/
def zerroH (n m : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (n : ℚ) *
    ∑ k ∈ Finset.Icc 1 (n - m), zerroU (m + 1) k *
      (Nat.stirlingSecond (n - m) k : ℚ)

/-- **Explicit formula for Genocchi numbers via Stirling numbers.** Let $n$ and $r$ be positive
integers with $n \ge r + 1$, let $G_n$ be the $n$-th Genocchi number and let $S(a, b)$ denote
the Stirling numbers of the second kind. For $k \ge 1$ write
$c_k = \sum_{j=0}^{r} (-1)^{k+j+r} \frac{(k+j-1)!}{2^{k+j-1}} S(r, j)$. Then
$G_n = (-1)^n \, n \sum_{k=1}^{n-r} c_k \, S(n-r, k)$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Theorem 1. -/
theorem_wanted genocchiNumber_eq_sum (n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hnr : r + 1 ≤ n) :
    MetaMathlibExt.genocchiNumber n =
      (-1 : ℚ) ^ n * (n : ℚ) *
        ∑ k ∈ Finset.Icc 1 (n - r),
          (∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ (k + j + r) *
              ((k + j - 1).factorial : ℚ) / 2 ^ (k + j - 1) *
              (Nat.stirlingSecond r j : ℚ)) *
          (Nat.stirlingSecond (n - r) k : ℚ)

/-- **Bernoulli numbers via forward differences at $0$.** Let $n$ and $r$ be positive integers
with $n \ge r + 1$, let $B_n$ be the $n$-th Bernoulli number, let $S(a, b)$ denote the Stirling
numbers of the second kind and let $\Delta^k 0^m$ be the $k$-th forward difference of
$y \mapsto y^m$ at $0$. For $k \ge 1$ write
$d_k = \sum_{j=0}^{r} (-1)^{k+j+r+1} \, 2^{r-j} \, \frac{(k+j-1)!}{k!} \, S(r, j)$. Then
$(-1)^n B_n = \frac{n}{2^n - 1} \sum_{k=1}^{n-r} d_k \, \frac{\Delta^k 0^{n-r}}{2^{k+r}}$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Corollary 2. -/
theorem_wanted neg_one_pow_mul_bernoulli_eq_sum_zero
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : r + 1 ≤ n) :
    (-1 : ℚ) ^ n * bernoulli n =
      (n : ℚ) / (2 ^ n - 1) *
        ∑ k ∈ Finset.Icc 1 (n - r),
          (∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ (k + j + r + 1) * 2 ^ (r - j) *
              ((k + j - 1).factorial : ℚ) / k.factorial *
              (Nat.stirlingSecond r j : ℚ)) *
          (diffPowEval 0 k (n - r) / 2 ^ (k + r))

/-- **Bernoulli numbers via forward differences at $1$.** Let $n$ and $r$ be positive integers
with $n \ge r + 1$, let $B_n$ be the $n$-th Bernoulli number, let $S(a, b)$ denote the Stirling
numbers of the second kind and let $\Delta^k 1^m$ be the $k$-th forward difference of
$y \mapsto y^m$ at $1$. For $k \ge 0$ write
$e_k = \sum_{j=0}^{r} (-1)^{k+j+r} \, 2^{r-j} \, \frac{(k+j)!}{k!} \, S(r, j)$. Then
$(-1)^n B_n = \frac{n}{2^n - 1} \sum_{k=0}^{n-1-r} e_k \, \frac{\Delta^k 1^{n-1-r}}{2^{k+1+r}}$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Corollary 2. -/
theorem_wanted neg_one_pow_mul_bernoulli_eq_sum_one
    (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) (hnr : r + 1 ≤ n) :
    (-1 : ℚ) ^ n * bernoulli n =
      (n : ℚ) / (2 ^ n - 1) *
        ∑ k ∈ Finset.range (n - r),
          (∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ (k + j + r) * 2 ^ (r - j) *
              ((k + j).factorial : ℚ) / k.factorial *
              (Nat.stirlingSecond r j : ℚ)) *
          (diffPowEval 1 k (n - 1 - r) / 2 ^ (k + 1 + r))

/-- **Recurrence for the Zerroukhat–Khaldi sums $U$.** Let $U(m, k)$ be the Zerroukhat–Khaldi
sum. For all natural numbers $r$ and $k$ with $k \ge 1$,
$U(r+1, k) = U(r, k+1) + k \, U(r, k)$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Lemma 3. -/
theorem_wanted zerroU_succ (r k : ℕ) (hk : 1 ≤ k) :
    zerroU (r + 1) k = zerroU r (k + 1) + (k : ℚ) * zerroU r k

/-- **A step identity for the Zerroukhat–Khaldi sums $H_{n,m}$.** Let $H_{n,m}$ denote the
Zerroukhat–Khaldi sum. For all natural numbers $n$ and $r$ with $r \ge 1$ and $n \ge r + 1$,
$H_{n,r} = H_{n,r-1}$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Lemma 3. -/
theorem_wanted zerroH_eq (n r : ℕ) (hr : 1 ≤ r)
    (hnr : r + 1 ≤ n) :
    zerroH n r = zerroH n (r - 1)

end MathlibExt.NumberTheory.GenocchiExplicitWanted
