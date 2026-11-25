/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.PalapiesTriangularArrays
public import MathlibExt.NumberTheory.Diophantine.Linear

/-!
# Palapies, triangular arrays at negative row indices — wishlist

The remaining statement from Lars Palapies' INTEGERS 26 (2026) paper concerns reflection
of triangular arrays extended to negative indices. A triangular
array `a_{n,k}` (`n, k ≥ 0`) satisfies the linear recurrence (1)
`a_{n,k} = (αn + βk + γ) a_{n-1,k} + (α'n + β'k + γ') a_{n-1,k-1}` with
`a_{n,-1} = 0`, `a_{0,k} = δ_{k=0}` and integer parameters. Definitions 1 and 2 of
the paper continue it to all `n, k ∈ ℤ` (negative-positive `a^{NP}` and
negative-negative `a^{NN}` numbers) by running (1) backwards; the divisions are in
`ℚ`, where a zero denominator gives the junk value `0` (the paper assumes the
denominators do not vanish, and calls the numbers non-existent otherwise).

Theorem 2 (Hankel-transform representation) is not formalized: its hypotheses
(a)–(d) evaluate the generating function `F(u, y)` of the `a_{n,k}` with `n ≥ 0`
along a real integration range reaching `1/α` or `±∞`, i.e. an analytic
continuation of the closed form (7) (complex powers, seven limiting cases) whose
branch and domain the paper does not pin down.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **NP/NN duality.** Let $a$ be the array of a triangular recurrence with parameters
$(\alpha, \beta, \gamma; \alpha', \beta', \gamma')$, with weights
$w(n, k) = \alpha(n + 1) + \beta k + \gamma$ and $w'(n, k) = \alpha'(n + 1) + \beta' k + \gamma'$,
and let $\tilde a$ be the array of the reflected recurrence, with parameters
$(\alpha' + \beta', -\beta', \gamma'; \alpha + \beta, -\beta, \gamma)$ and weights $\tilde w$,
$\tilde w'$. Then for all integers $n, k$ the negative-positive and negative-negative numbers
satisfy $\tilde a^{NP}_{n,k} = a^{NN}_{n,n-k}$ and $\tilde a^{NN}_{n,n-k} = a^{NP}_{n,k}$.
Moreover, $\tilde w(n, k) \ne 0$ for all integers $n < 0 \le k$ if and only if
$w'(n, k + 1) \ne 0$ for all integers $k \le n < 0$; and $\tilde w'(n, k + 1) \ne 0$ for all
integers $k \le n < 0$ if and only if $w(n, k) \ne 0$ for all integers $n < 0 \le k$.

Thus the divisor condition of Definition 1 for $\tilde a$ is equivalent to that of Definition 2
for $a$, and conversely, so the left-hand sides exist exactly when the right-hand sides do.
With junk value $0$ for a zero divisor, the two identities need no existence hypothesis.

Source: Lars Palapies, *On Extensions of Triangular Arrays to Negative Row Indices
and Their Generating Functions*, INTEGERS 26 (2026), Article A83, Proposition 3. -/
public theorem_wanted TriangularRecurrence.reflect_negPos_eq_negNeg
    (P : TriangularRecurrence) :
    (∀ n k : ℤ, P.reflect.negPos n k = P.negNeg n (n - k)) ∧
    (∀ n k : ℤ, P.reflect.negNeg n (n - k) = P.negPos n k) ∧
    ((∀ n k : ℤ, n < 0 → 0 ≤ k → P.reflect.weight n k ≠ 0) ↔
      ∀ n k : ℤ, k ≤ n → n < 0 → P.weight' n (k + 1) ≠ 0) ∧
    ((∀ n k : ℤ, k ≤ n → n < 0 → P.reflect.weight' n (k + 1) ≠ 0) ↔
      ∀ n k : ℤ, n < 0 → 0 ≤ k → P.weight n k ≠ 0)

end

end MetaMathlibExt
