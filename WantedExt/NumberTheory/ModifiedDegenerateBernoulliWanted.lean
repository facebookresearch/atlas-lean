/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliThreeTerm
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.Binomial

/-!
# Symmetric identities on modified degenerate Bernoulli polynomials

The remaining identities are from Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified
Degenerate Bernoulli Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4.
Binomial coefficients with a complex upper argument are `Ring.choose`.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Symmetric identity for modified degenerate Bernoulli polynomials.** Let $m \ge 2$ and
$n \ge 1$ be integers, let $\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$,
let $r_1, \ldots, r_m$ and $x_1, \ldots, x_m$ be complex numbers, write
$\mathfrak{B}_{k,\lambda}(x)$ for the modified degenerate Bernoulli polynomials, and put
$r_0 = n - r_1 - \cdots - r_m$. Then

$$
r_0 \sum_{k_1 + \cdots + k_m = n} \prod_{j=1}^{m} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j)
= -\sum_{i=1}^{m} r_i \sum_{k_1 + \cdots + k_m = n} \binom{r_0}{k_i}
\mathfrak{B}_{k_i,\lambda}(1 - x_i)
\prod_{j \ne i} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $\binom{w}{k} = w(w-1) \cdots
(w-k+1)/k!$ is the binomial coefficient with a complex upper argument, and $[j > i]$ is $1$ if
$j > i$ and $0$ otherwise.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Theorem 1
(`jis-2024-24.5.4-thm-1`). -/
public theorem_wanted modifiedDegenerateBernoulli_symmetric_identity (m n : ℕ) (hm : 2 ≤ m)
    (hn : 1 ≤ n) (r x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) - ∑ j, r j) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * modifiedDegenerateBernoulli lam (k j) (x j) =
      -∑ i, r i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) * modifiedDegenerateBernoulli lam (k i) (1 - x i) *
          ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0)

/-- **Miki-type identity for modified degenerate Bernoulli numbers.** Let $n \ge 4$, let $\lambda$
be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, write
$\mathfrak{B}_{k,\lambda} = \mathfrak{B}_{k,\lambda}(0)$ for the value at $0$ of the modified
degenerate Bernoulli polynomial $\mathfrak{B}_{k,\lambda}(x)$, and let $H_n = \sum_{k=1}^{n} 1/k$
be the $n$-th harmonic number. Then

$$
\sum_{k=1}^{n-1} \frac{\mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda}}{k} -
\sum_{k=1}^{n-1} \binom{n}{k} \frac{\mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda}}{k} =
\frac{\lambda}{\log(1+\lambda)}\, H_n\, \mathfrak{B}_{n,\lambda} +
\frac{n}{2}\, \mathfrak{B}_{n-1,\lambda},
$$

where $\log$ is the principal branch.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(mikiD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_miki (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ k ∈ Icc 1 (n - 1), modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 -
      ∑ k ∈ Icc 1 (n - 1), (n.choose k : ℂ) * modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 =
      lam / Complex.log (1 + lam) * (harmonic n : ℂ) * modifiedDegenerateBernoulli lam n 0 +
        n / 2 * modifiedDegenerateBernoulli lam (n - 1) 0

/-- **A convolution lemma for modified degenerate Bernoulli polynomials.** Let $m \ge 2$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, let $s_1, \ldots, s_m$ be
nonnegative integers with $S = s_1 + \cdots + s_m$, and let $x_1, \ldots, x_m$ be complex numbers.
Writing $\mathfrak{B}_{n,\lambda}(x)$ for the modified degenerate Bernoulli polynomials,

$$
\sum_{i=1}^{m} s_i\, \mathfrak{B}_{s_i-1,\lambda}(x_i)
\prod_{j \ne i} \mathfrak{B}_{s_j,\lambda}(x_j) =
\sum_{i=1}^{m} s_i \sum_{k_1 + \cdots + k_m = S} \mathfrak{B}_{k_i-1,\lambda}(x_i)
\prod_{j \ne i} \binom{s_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $[j > i]$ is $1$ if $j > i$ and $0$
otherwise, and $\mathfrak{B}_{-1,\lambda}$ is read as $0$ (on the left this term has the factor
$s_i = 0$).

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Lemma 3
(`jis-2024-24.5.4-lem-3`). -/
public theorem_wanted modifiedDegenerateBernoulli_lemma_three (m : ℕ) (hm : 2 ≤ m)
    (s : Fin m → ℕ) (x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ i, (s i : ℂ) * modifiedDegenerateBernoulli lam (s i - 1) (x i) *
        ∏ j ∈ univ.erase i, modifiedDegenerateBernoulli lam (s j) (x j) =
      ∑ i, (s i : ℂ) * ∑ k ∈ Finset.Nat.antidiagonalTuple m (∑ j, s j),
        (if k i = 0 then 0 else modifiedDegenerateBernoulli lam (k i - 1) (x i)) *
          ∏ j ∈ univ.erase i, ((s j).choose (k j) : ℂ) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0)

end

end MetaMathlibExt
