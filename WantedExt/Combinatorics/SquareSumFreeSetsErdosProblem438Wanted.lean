/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets whose sumset avoids the squares (Erdős Problem 438)

Erdős Problem 438: how large can `A ⊆ {1, …, N}` be if `A + A` contains no square numbers?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.SquareSumFreeSetsErdosProblem438Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #438, https://www.erdosproblems.com/438 (status
SOLVED). UnsolvedMath record UM-30006869 (`EP-438`), dataset ulamai/UnsolvedMath v1.8.0.

`A + A` includes the sums `a + a`; excluding them changes the maximum by `O(√N)` only (the `a` with
`2a` a square). The answer is stated as `max |A| / N → 11/32`, the maximum being an `sSup` over a
bounded nonempty set. Compared with the formal-conjectures statement `ErdosProblems/438.lean`
(equivalent; no code imported).
-/

/-- No sum `a + b` of two (possibly equal) elements of `A` is a perfect square. -/
def IsSquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

/-- The largest size of a set `A ⊆ {1, …, N}` such that `A + A` contains no perfect square. -/
noncomputable def maxSquareSumFreeSize (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSquareSumFree A ∧ A.card = k}

/-- Erdős Problem 438: the largest `A ⊆ {1, …, N}` with no perfect square in `A + A` has
`(11/32 + o(1)) N` elements. -/
def maxSquareSumFreeDensity : Prop :=
  Filter.Tendsto (fun N : ℕ => (maxSquareSumFreeSize N : ℝ) / N) Filter.atTop (nhds (11 / 32))

/--
Resolved true: Khalfalah, Lodha and Szemerédi proved that such `A` has at most `(11/32 + o(1)) N`
elements, and Massias's example (the residues `1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30 mod 32`) has
`11N/32 + O(1)`; erdosproblems.com/438 lists the problem as solved. Source: T. F. Bloom, Erdős
Problems, Problem #438, https://www.erdosproblems.com/438 (status SOLVED); resolution: A. Khalfalah,
S. Lodha and E. Szemerédi, Tight bound for the density of sequence of integers the sum of no two of
which is a perfect square, Discrete Math. (2002), 243-255, max |A| ≤ (11/32 + o(1)) N; Massias's
residues mod 32 give the lower bound (erdosproblems.com/438).
-/
public theorem_wanted maxSquareSumFreeDensity_holds : maxSquareSumFreeDensity

end MathlibExt.Combinatorics.SquareSumFreeSetsErdosProblem438Wanted
