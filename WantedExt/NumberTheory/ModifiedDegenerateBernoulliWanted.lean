/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliThreeTerm
public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliMiki
public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliModifiedDegenerateBernoulliSymmetricIdentity

/-!
# Symmetric identities on modified degenerate Bernoulli polynomials

The remaining identities are from Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified
Degenerate Bernoulli Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4.
Binomial coefficients with a complex upper argument are `Ring.choose`.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

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
