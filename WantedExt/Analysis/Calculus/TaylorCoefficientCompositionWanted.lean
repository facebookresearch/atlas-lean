/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.Calculus.TaylorCoefficientComposition
public import MathlibExt.NumberTheory.MultipleZeta.OddSquareStrictSums
public import MathlibExt.NumberTheory.MultipleZeta.Series

namespace MetaMathlibExt

@[expose] public section

/-- **Nested sums of reciprocal odd squares.** For every natural number $k$,
$$\sum_{i_1 \ge i_2 \ge \cdots \ge i_k \ge 1} \prod_{j=1}^{k} \frac{1}{(2 i_j - 1)^2} =
\frac{(\pi/2)^{2k} E^*_{2k}}{(2k)!},$$
where the sum runs over all weakly decreasing $k$-tuples $(i_1, \ldots, i_k)$ of positive integers
and $E^*_{2k} = \sec^{(2k)}(0)$ is the $2k$-th derivative at $0$ of $\sec x = 1/\cos x$ (the Euler
zig number, OEIS A000364). For $k = 0$ the sum has the single empty term and both sides equal $1$.

The source also claims that the sum equals $(\pi/4)\,\beta(2k+1)$, where $\beta$ is Dirichlet's beta
function; this is false as printed and is not stated here: at $k = 0$ the sum is $1$ but
$(\pi/4)\,\beta(1) = \pi^2/16$, and at $k = 1$ it is $\pi^2/8$ but $(\pi/4)\,\beta(3) = \pi^4/128$
(the correct factor is $4/\pi$).

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Theorem 1. -/
public theorem_wanted tsum_weaklyDecreasing_prod_inv_odd_sq_eq (k : ℕ) :
    ∑' m : MultipleZeta.WeaklyDecreasingTuple k,
        ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ =
      (Real.pi / 2) ^ (2 * k) * iteratedDeriv (2 * k) (fun x => (Real.cos x)⁻¹) 0 /
        (2 * k).factorial

/-- **Nested sums of reciprocal squares.** For every natural number $k$, the multiple zeta-star
value
$$\zeta^\star(\{2\}^k) =
\sum_{n_1 \ge n_2 \ge \cdots \ge n_k \ge 1} \frac{1}{n_1^2 n_2^2 \cdots n_k^2},$$
which is $1$ for $k = 0$, satisfies
$$\zeta^\star(\{2\}^k) = \frac{2\pi^{2k} |(2^{2k-1} - 1) B_{2k}|}{(2k)!} =
2\,(1 - 2^{1-2k})\,\zeta(2k),$$
where $B_{2k}$ is the $2k$-th Bernoulli number and $\zeta$ is the Riemann zeta function. The
right-hand side is $2\eta(2k)$ for Dirichlet's eta function $\eta(s) = (1 - 2^{1-s})\,\zeta(s)$;
at $k = 0$ all three expressions equal $1$, since $\zeta(0) = -1/2$.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Theorem 2. -/
public theorem_wanted starValue_replicate_two_eq (k : ℕ) :
    MultipleZeta.starValue (MultipleZeta.Index.replicate k 2)
        (MultipleZeta.Index.replicate_isAdmissibleOrEmpty k le_rfl) =
        2 * Real.pi ^ (2 * k) * |((2 : ℝ) ^ ((2 * k : ℤ) - 1) - 1) * bernoulli (2 * k)| /
          (2 * k).factorial ∧
      ((MultipleZeta.starValue (MultipleZeta.Index.replicate k 2)
          (MultipleZeta.Index.replicate_isAdmissibleOrEmpty k le_rfl) : ℝ) : ℂ) =
        2 * ((1 - (2 : ℂ) ^ ((1 : ℤ) - 2 * k)) * riemannZeta (2 * k))

end

end MetaMathlibExt
