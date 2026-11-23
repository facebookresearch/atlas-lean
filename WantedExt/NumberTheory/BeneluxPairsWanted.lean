/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.PrimeFin

/-! # Benelux pairs below `1.4 · 10¹²`

Statement-only requests from Christian Hercher, *On One of Erdős' Problems—An Efficient
Search for Benelux Pairs*, Journal of Integer Sequences 28 (2025), Article 25.8.5. Following
the source (Section 1, arXiv:2506.01099v1), positive integers `m < n` form a *Benelux pair*
(of first kind) when `m` and `n` have the same prime factors and `m + 1` and `n + 1` have the
same prime factors, and a *Benelux pair of second kind* when `m` and `n + 1` have the same
prime factors and `m + 1` and `n` have the same prime factors. "Same prime factors" is
equality of `Nat.primeFactors`. The source's positivity of `m` is not assumed: at `m = 0` both
sides of each equivalence are false. Both classifications are results of a computer search.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Benelux pairs of the first kind below $1.4 \cdot 10^{12}$.** Let $m < n$ be
non-negative integers with $n < 1.4 \cdot 10^{12}$. Then $m$ and $n$ have the same prime
factors and $m + 1$ and $n + 1$ have the same prime factors (that is, $(m, n)$ is a Benelux
pair of the first kind) if and only if $(m, n) = (75, 1215)$ or
$(m, n) = (2^k - 2, 2^{2k} - 2^{k+1})$ for some integer $k$ with $2 \le k \le 20$.

Here $0$ is taken to have no prime factors; for $m = 0$ both sides are false.

Source: Christian Hercher, *On One of Erdős' Problems—An Efficient Search for Benelux
Pairs*, Journal of Integer Sequences 28 (2025), Article 25.8.5, Theorem 1 a)
(`jis-2025-25.8.5-thm-1`). -/
public theorem_wanted benelux_pair_first_kind_iff
    (m n : ℕ) (hmn : m < n) (hn : n < 14 * 10 ^ 11) :
    (m.primeFactors = n.primeFactors ∧ (m + 1).primeFactors = (n + 1).primeFactors) ↔
      (m = 75 ∧ n = 1215) ∨
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ 20 ∧ m = 2 ^ k - 2 ∧ n = 2 ^ (2 * k) - 2 ^ (k + 1)

/-- **Benelux pairs of the second kind below $1.4 \cdot 10^{12}$.** Let $m < n$ be
non-negative integers with $n < 1.4 \cdot 10^{12}$. Then $m$ and $n + 1$ have the same prime
factors and $m + 1$ and $n$ have the same prime factors (that is, $(m, n)$ is a Benelux pair
of the second kind) if and only if $(m, n) = (35, 4374)$ or
$(m, n) = (2^k + 1, 2^{2k} + 2^{k+1})$ for some integer $k$ with $0 \le k \le 20$.

Here $0$ is taken to have no prime factors; for $m = 0$ both sides are false.

Source: Christian Hercher, *On One of Erdős' Problems—An Efficient Search for Benelux
Pairs*, Journal of Integer Sequences 28 (2025), Article 25.8.5, Theorem 1 b)
(`jis-2025-25.8.5-thm-1`). -/
public theorem_wanted benelux_pair_second_kind_iff
    (m n : ℕ) (hmn : m < n) (hn : n < 14 * 10 ^ 11) :
    (m.primeFactors = (n + 1).primeFactors ∧ (m + 1).primeFactors = n.primeFactors) ↔
      (m = 35 ∧ n = 4374) ∨
        ∃ k : ℕ, k ≤ 20 ∧ m = 2 ^ k + 1 ∧ n = 2 ^ (2 * k) + 2 ^ (k + 1)

end

end MetaMathlibExt
