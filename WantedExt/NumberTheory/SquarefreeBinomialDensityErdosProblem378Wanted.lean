/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Density of integers with many squarefree binomial coefficients (Erdős Problem 378)

Erdős Problem 378: let `r ≥ 0`. Does the density of the integers `n` for which `C(n, k)` is
squarefree for at least `r` values of `1 ≤ k < n` exist? Is it positive?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Squarefree
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.NumberTheory.SquarefreeBinomialDensityErdosProblem378Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #378, https://www.erdosproblems.com/378 (status
PROVED). UnsolvedMath record UM-30006845 (`EP-378`), dataset ulamai/UnsolvedMath v1.8.0.

Natural density is `Set.HasDensity` (MathlibExt). The two questions are separate targets, each for
every `r`. formal-conjectures has no statement of this problem.
-/

/-- The number of `1 ≤ k < n` for which `n.choose k` is squarefree. -/
def squarefreeBinomialCount (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k => Squarefree (n.choose k)).card

/-- Erdős Problem 378, first question: for every `r`, the set of `n` for which `n.choose k` is
squarefree for at least `r` values `1 ≤ k < n` has a natural density. -/
def squarefreeBinomialDensityExists : Prop :=
  ∀ r : ℕ, ∃ d : ℝ, {n : ℕ | r ≤ squarefreeBinomialCount n}.HasDensity d

/-- Erdős Problem 378, second question: for every `r` that density is positive. -/
def squarefreeBinomialDensityPos : Prop :=
  ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧ {n : ℕ | r ≤ squarefreeBinomialCount n}.HasDensity d

/--
Resolved true: Granville and Ramaré proved that for each `m` the set of `n` for which `C(n, k)` is
squarefree for exactly `2m + 2` values of `k` has a density `η_m`; as Aggarwal and Cambie observed
(erdosproblems.com/378), the set in question then has density `1 - ∑_{0 ≤ m ≤ (r - 1)/2} η_m`.
Source: T. F. Bloom, Erdős Problems, Problem #378, https://www.erdosproblems.com/378 (status
PROVED); resolution: A. Granville and O. Ramaré, Explicit bounds on exponential sums and the
scarcity of squarefree binomial coefficients, Mathematika (1996), 73-107, the density η_m of the n
with exactly 2m + 2 squarefree C(n, k) exists and is positive; observation of Aggarwal and Cambie on
erdosproblems.com/378.
-/
public theorem_wanted squarefreeBinomialDensityExists_holds : squarefreeBinomialDensityExists

/--
Resolved true: the density is positive, since the set contains the `n` with exactly `2(r + 1) + 2`
squarefree `C(n, k)`, of density `η_{r+1} > 0` (Granville and Ramaré; erdosproblems.com/378).
Source: T. F. Bloom, Erdős Problems, Problem #378, https://www.erdosproblems.com/378 (status
PROVED); resolution: A. Granville and O. Ramaré, Explicit bounds on exponential sums and the
scarcity of squarefree binomial coefficients, Mathematika (1996), 73-107, the density η_m of the n
with exactly 2m + 2 squarefree C(n, k) exists and is positive; observation of Aggarwal and Cambie on
erdosproblems.com/378.
-/
public theorem_wanted squarefreeBinomialDensityPos_holds : squarefreeBinomialDensityPos

end MathlibExt.NumberTheory.SquarefreeBinomialDensityErdosProblem378Wanted
