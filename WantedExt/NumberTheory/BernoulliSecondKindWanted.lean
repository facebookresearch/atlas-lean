/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Formulas involving Bernoulli and Stirling numbers of both kinds

Statements from Bakir Farhi, "Formulas Involving Bernoulli
and Stirling Numbers of Both Kinds", *Journal of Integer
Sequences* 28 (2025), Article 25.2.6
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Farhi/farhi26.tex>).

Notation: `Bₙ` is Mathlib's `bernoulli`, `Bₙ(X)` is
Mathlib's `Polynomial.bernoulli`, `S(n,k)` is
`Nat.stirlingSecond`, the signed Stirling numbers of the
first kind `s(n,k)` are MathlibExt's `signedStirlingFirst`,
`X^{\underline n}` is Mathlib's falling-factorial
polynomial `descPochhammer`, and the Bernoulli numbers of the
second kind `Bₙ^*` (exponential generating function
`t / log(1 + t)`, in Roman's normalization) are
MathlibExt's `MetaMathlibExt.MetaMathlibExt.bernoulliSecond`. The paper's `ℕ` is the positive
integers; the convolution identities (Corollaries 7, 10,
Theorem 13, Corollary 15) are stated for `1 ≤ k ≤ n` as
printed, and Lemma 3's complex sequences are stated over
`ℚ`. All identities were verified by exact rational
computation before stating.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.Log
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst
public import MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

/-- **Bernoulli polynomials in the falling-factorial basis.** Let $B_m$ be the Bernoulli numbers
(with $B_1 = -1/2$), $B_n(X) = \sum_{i=0}^{n} \binom{n}{i} B_i X^{n-i}$ the Bernoulli
polynomials over $\mathbb{Q}$, $S(m, j)$ the Stirling numbers of the second kind and
$X^{\underline{k}} = X(X-1)\cdots(X-k+1)$ the falling factorial. For every natural number
$n$, in $\mathbb{Q}[X]$,
$$B_n(X) = B_n + \sum_{k=1}^{n} \frac{n}{k} \, S(n-1, k-1) \, X^{\underline{k}}.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 1. -/
theorem_wanted bernoulli_poly_eq (n : ℕ) :
    Polynomial.bernoulli n =
      Polynomial.C (bernoulli n) +
        ∑ k ∈ Finset.Icc 1 n, Polynomial.C
          ((n : ℚ) / k * (Nat.stirlingSecond (n - 1) (k - 1) : ℚ)) *
          descPochhammer ℚ k

/-- **Bernoulli numbers in terms of Bernoulli numbers of the second kind.** Let $B_m$ be the
Bernoulli numbers (with $B_1 = -1/2$), $B_m^*$ the Bernoulli numbers of the second kind and
$S(m, j)$ the Stirling numbers of the second kind. For every natural number $n \ge 1$,
$$B_n = -\sum_{k=1}^{n} \frac{n}{k} \, S(n-1, k-1) \, B_k^*.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 2. -/
theorem_wanted bernoulli_eq_neg_sum (n : ℕ) (hn : 1 ≤ n) :
    bernoulli n =
      -∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k *
        (Nat.stirlingSecond (n - 1) (k - 1) : ℚ) *
        MetaMathlibExt.bernoulliSecond k

/-- **Stirling inversion.** Let $s(m, j)$ be the signed Stirling numbers of the first kind and
$S(m, j)$ the Stirling numbers of the second kind. For all sequences $(u_n)_{n \ge 0}$ and
$(v_n)_{n \ge 0}$ of rational numbers, $u_n = \sum_{k=0}^{n} s(n, k) \, v_k$ for every natural
number $n$ if and only if $v_n = \sum_{k=0}^{n} S(n, k) \, u_k$ for every natural number $n$.

The paper states this for sequences of complex numbers.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Lemma 3. -/
theorem_wanted stirling_inversion_iff (u v : ℕ → ℚ) :
    (∀ n, u n = ∑ k ∈ Finset.range (n + 1),
      (MetaMathlibExt.signedStirlingFirst n k : ℚ) * v k) ↔
    (∀ n, v n = ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond n k : ℚ) * u k)

/-- **Bernoulli numbers of the second kind in terms of Bernoulli numbers.** Let $B_m$ be the
Bernoulli numbers (with $B_1 = -1/2$), $B_m^*$ the Bernoulli numbers of the second kind and
$s(m, j)$ the signed Stirling numbers of the first kind. For every natural number $n \ge 1$,
$$B_n^* = -\sum_{k=1}^{n} \frac{n}{k} \, s(n-1, k-1) \, B_k.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 4. -/
theorem_wanted bernoulliSecond_eq_neg_sum (n : ℕ)
    (hn : 1 ≤ n) :
    MetaMathlibExt.bernoulliSecond n =
      -∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k *
        (MetaMathlibExt.signedStirlingFirst (n - 1) (k - 1) : ℚ) * bernoulli k

/-- **Falling factorials in the Bernoulli polynomial basis.** Let $B_m^*$ be the Bernoulli
numbers of the second kind, $B_k(X)$ the Bernoulli polynomials over $\mathbb{Q}$ (so that
$B_1(X) = X - 1/2$), $s(m, j)$ the signed Stirling numbers of the first kind and
$X^{\underline{n}} = X(X-1)\cdots(X-n+1)$ the falling factorial. For every natural number
$n$, in $\mathbb{Q}[X]$,
$$X^{\underline{n}} = B_n^* + \sum_{k=1}^{n} \frac{n}{k} \, s(n-1, k-1) \, B_k(X).$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 5. -/
theorem_wanted descPochhammer_eq (n : ℕ) :
    descPochhammer ℚ n =
      Polynomial.C (MetaMathlibExt.bernoulliSecond n) +
        ∑ k ∈ Finset.Icc 1 n, Polynomial.C
          ((n : ℚ) / k * (MetaMathlibExt.signedStirlingFirst (n - 1) (k - 1) : ℚ)) *
          Polynomial.bernoulli k

/-- **Shifted Stirling convolution formula for Bernoulli numbers.** For natural numbers $k$ and $n$
with $1 \le k \le n$, write $S(m,j)$ for the Stirling numbers of the second kind, $s(m,j)$ for
the signed Stirling numbers of the first kind, and $B_m$ for the Bernoulli numbers with
$B_1 = -\tfrac12$. Then, in $\mathbb{Q}$,
$$
\sum_{i=k}^{n} \frac{S(n-1,i-1)\, s(i,k)}{i} = \frac{1}{n} \binom{n}{k} B_{n-k}.
$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 7. -/
theorem_wanted sum_stirlingSecond_signed_div (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (Nat.stirlingSecond (n - 1) (i - 1) : ℚ) *
          (MetaMathlibExt.signedStirlingFirst i k : ℚ) / i =
      (1 / (n : ℚ)) * (Nat.choose n k : ℚ) * bernoulli (n - k)

/-- **Bernoulli numbers via Stirling numbers of the second kind.** Let $B_m$ be the Bernoulli
numbers (with $B_1 = -1/2$) and $S(m, j)$ the Stirling numbers of the second kind. For every
natural number $n$,
$$B_n = \sum_{i=0}^{n} (-1)^i \, \frac{i!}{i+1} \, S(n, i).$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 9. -/
theorem_wanted bernoulli_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℚ) ^ i *
        ((i.factorial : ℚ) / (i + 1)) *
        (Nat.stirlingSecond n i : ℚ)

/-- **Unshifted Stirling convolution formula for Bernoulli numbers.** For natural numbers $k$
and $n$ with $1 \le k \le n$, write $S(m,j)$ for the Stirling numbers of the second kind,
$s(m,j)$ for the signed Stirling numbers of the first kind, and $B_m$ for the Bernoulli numbers
with $B_1 = -\tfrac12$. Then, in $\mathbb{Q}$,
$$
\sum_{i=k}^{n} \frac{S(n,i)\, s(i,k)}{i} = \frac{1}{n} \binom{n}{k} B_{n-k} + \delta_{n-1,k},
$$
where $\delta_{n-1,k}$ is $1$ if $k = n - 1$ and $0$ otherwise.

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 10. -/
theorem_wanted sum_stirlingSecond_signed_div_delta (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (Nat.stirlingSecond n i : ℚ) *
          (MetaMathlibExt.signedStirlingFirst i k : ℚ) / i =
      (1 / (n : ℚ)) * (Nat.choose n k : ℚ) * bernoulli (n - k) +
        (if n - 1 = k then 1 else 0)

/-- **Bernoulli numbers of the second kind via Stirling numbers of the first kind.** Let $B_m^*$
be the Bernoulli numbers of the second kind and $s(m, j)$ the signed Stirling numbers of the
first kind. For every natural number $n$,
$$B_n^* = \sum_{i=0}^{n} \frac{s(n, i)}{i+1}.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Proposition 11. -/
theorem_wanted bernoulliSecond_eq_sum (n : ℕ) :
    MetaMathlibExt.bernoulliSecond n =
      ∑ i ∈ Finset.range (n + 1),
        (MetaMathlibExt.signedStirlingFirst n i : ℚ) / (i + 1)

/-- **Shifted Stirling convolution as a Bernoulli number of the second kind.** Let $s(m, j)$ be
the signed Stirling numbers of the first kind, $S(m, j)$ the Stirling numbers of the second kind
and $B_m^*$ the Bernoulli numbers of the second kind. For all natural numbers $n$ and $k$ with
$1 \le k \le n$,
$$\sum_{i=k}^{n} \frac{s(n-1, i-1) \, S(i, k)}{i} = \frac{1}{n} \binom{n}{k} \, B_{n-k}^*.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 13. -/
theorem_wanted sum_signed_stirlingSecond_div (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (MetaMathlibExt.signedStirlingFirst (n - 1) (i - 1) : ℚ) *
          (Nat.stirlingSecond i k : ℚ) / i =
      (1 / (n : ℚ)) * (Nat.choose n k : ℚ) *
        MetaMathlibExt.bernoulliSecond (n - k)

/-- **Stirling convolution as a sum of Bernoulli numbers of the second kind.** Let $s(m, j)$ be
the signed Stirling numbers of the first kind, $S(m, j)$ the Stirling numbers of the second kind
and $B_m^*$ the Bernoulli numbers of the second kind. For all natural numbers $n$ and $k$ with
$1 \le k \le n$,
$$\sum_{i=k}^{n} \frac{s(n, i) \, S(i, k)}{i} =
(-1)^{n-k} \, \frac{(n-1)!}{k!} \sum_{l=0}^{n-k} \frac{(-1)^l}{l!} \, B_l^*.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Corollary 15. -/
theorem_wanted sum_signed_stirlingSecond_div_eq (n k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ i ∈ Finset.Icc k n,
        (MetaMathlibExt.signedStirlingFirst n i : ℚ) *
          (Nat.stirlingSecond i k : ℚ) / i =
      (-1 : ℚ) ^ (n - k) *
        ((n - 1).factorial : ℚ) / k.factorial *
        ∑ l ∈ Finset.range (n - k + 1),
          ((-1 : ℚ) ^ l / l.factorial) * MetaMathlibExt.bernoulliSecond l

/-- **Weighted alternating sums of Stirling numbers of the second kind.** For natural numbers
$r \ge 1$ and $n$, write $S(n,k)$ for the Stirling numbers of the second kind, $c(r,j)$ for the
unsigned Stirling numbers of the first kind, and $B_m$ for the Bernoulli numbers with
$B_1 = -\tfrac12$. Then, in $\mathbb{Q}$,
$$
\sum_{k=0}^{n} (-1)^k \frac{k!}{k+r} S(n,k) = \frac{1}{(r-1)!} \sum_{k=0}^{r-1} c(r,k+1) B_{n+k}.
$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 17. -/
theorem_wanted sum_stirlingSecond_div_add (r n : ℕ)
    (hr : 1 ≤ r) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
        ((k.factorial : ℚ) / (k + r)) *
        (Nat.stirlingSecond n k : ℚ) =
      (1 / ((r - 1).factorial : ℚ)) *
        ∑ k ∈ Finset.range r,
          (Nat.stirlingFirst r (k + 1) : ℚ) * bernoulli (n + k)

/-- **Sums of signed Stirling numbers of the first kind with shifted reciprocal weights.** Let
$s(m, j)$ be the signed Stirling numbers of the first kind, $S(m, j)$ the Stirling numbers of
the second kind and $B_m^*$ the Bernoulli numbers of the second kind. Let $r \ge 1$ and $n$ be
natural numbers, and for $0 \le k \le r - 1$ set
$\lambda_{r,n,k} = \sum_{l=0}^{r-1-k} \binom{r-1}{l} \, S(r-1-l, k) \, n^l$ (with $0^0 = 1$).
Then
$$\sum_{k=0}^{n} \frac{s(n, k)}{k + r} = \sum_{k=0}^{r-1} \lambda_{r,n,k} \, B_{n+k}^*.$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 19. -/
theorem_wanted sum_signed_div_add (r n : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.range (n + 1),
        (MetaMathlibExt.signedStirlingFirst n k : ℚ) / (k + r) =
      ∑ k ∈ Finset.range r,
        (∑ l ∈ Finset.range (r - k), (Nat.choose (r - 1) l : ℚ) *
          (Nat.stirlingSecond (r - 1 - l) k : ℚ) * (n : ℚ) ^ l) *
        MetaMathlibExt.bernoulliSecond (n + k)

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
