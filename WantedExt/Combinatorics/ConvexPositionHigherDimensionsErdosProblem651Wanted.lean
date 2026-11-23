/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Convex position in higher dimensions (Erdős Problem 651)

Erdős Problem 651: let `f_k(n)` denote the smallest integer such that any `f_k(n)` points in general
position in `ℝᵏ` contain `n` which determine a convex polyhedron. Is it true that `f_k(n) > (1 +
c_k)^n` for some constant `c_k > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.LinearAlgebra.GeneralPosition

@[expose] public section

namespace MathlibExt.Combinatorics.ConvexPositionHigherDimensionsErdosProblem651Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #651, https://www.erdosproblems.com/651 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006970 (`EP-651`), dataset ulamai/UnsolvedMath v1.8.0.

General position is MathlibExt's `IsGeneralPosition ℝ k` (any at most `k + 1` of the points are
affinely independent); `n` points
determine a convex polyhedron when they are in convex position (`ConvexIndependent`: none lies in
the convex hull of the others). The question is for each dimension `k ≥ 2` (`k = 2` is the
Erdős-Szekeres setting), and `f_k(n) > (1 + c_k)^n` is required only for all large `n`, a weaker
claim whose refutation is stronger.
-/

/-- **Convex position threshold.** For natural numbers $k$ and $n$, $f_k(n)$ is the least natural
number $m$ such that every set of $m$ points of $\mathbb{R}^k$ in general position (any at most
$k + 1$ of them affinely independent) contains $n$ points in convex position (none of them in the
convex hull of the others). If there is no such $m$, then $f_k(n) = 0$.

For $k \ge 2$ such an $m$ exists by the Erdős-Szekeres theorem. -/
noncomputable def convexPositionThreshold (k n : ℕ) : ℕ :=
  sInf {m | ∀ P : Finset (EuclideanSpace ℝ (Fin k)), P.card = m →
    IsGeneralPosition ℝ k ((↑) : P → EuclideanSpace ℝ (Fin k)) →
    ∃ S ⊆ P, S.card = n ∧ ConvexIndependent ℝ ((↑) : S → EuclideanSpace ℝ (Fin k))}

/-- **Erdős Problem 651: exponential growth of convex position thresholds.** For natural numbers
$k$ and $n$ let $f_k(n)$ be the least $m$ such that every set of $m$ points of $\mathbb{R}^k$ in
general position (any at most $k + 1$ of them affinely independent) contains $n$ points in convex
position (none of them in the convex hull of the others), with $f_k(n) = 0$ if there is no such
$m$. The claim is that for every $k \ge 2$ there is a real $c > 0$ with $(1 + c)^n < f_k(n)$ for
all sufficiently large $n$.

Erdős asked for a constant $c_k > 0$ with $f_k(n) > (1 + c_k)^n$; requiring this only for all
large $n$ makes the claim weaker and its refutation stronger. -/
def convexPositionThresholdExponential : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    (1 + c) ^ n < (convexPositionThreshold k n : ℝ)

/--
**Erdős Problem 651 has a negative answer.** For natural numbers $k$ and $n$ let $f_k(n)$ be the
least $m$ such that every set of $m$ points of $\mathbb{R}^k$ in general position (any at most
$k + 1$ of them affinely independent) contains $n$ points in convex position (none of them in the
convex hull of the others), with $f_k(n) = 0$ if there is no such $m$. It is not the case that for
every $k \ge 2$ there is a real $c > 0$ with $(1 + c)^n < f_k(n)$ for all sufficiently large $n$.

Pohoata and Zakharov proved $f_d(n) = 2^{o(n)}$ for every $d \ge 3$, so for $k = 3$ and every
$c > 0$ the bound $f_3(n) \le (1 + c)^n$ holds for all large $n$; erdosproblems.com/651 lists the
problem as disproved.

Source: T. F. Bloom, Erdős Problems, Problem #651,
https://www.erdosproblems.com/651 (status DISPROVED (LEAN)); resolution: C. Pohoata and D. Zakharov,
Convex polytopes from fewer points, arXiv:2208.04878 (2022), abstract: ES_d(n) = 2^{o(n)} for all d
≥ 3, ES_d(n) being the least number such that any ES_d(n) points in general position in ℝ^d contain
n points in convex position; erdosproblems.com/651: the answer is no, even for k = 3,
https://arxiv.org/abs/2208.04878.
-/
public theorem_wanted convexPositionThresholdExponential_refuted :
    ¬ convexPositionThresholdExponential

end MathlibExt.Combinatorics.ConvexPositionHigherDimensionsErdosProblem651Wanted
