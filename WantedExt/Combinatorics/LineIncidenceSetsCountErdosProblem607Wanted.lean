/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting the sets of line-incidence numbers (Erdős Problem 607)

Erdős Problem 607: for `n` points `P ⊆ ℝ²` let `A = {|ℓ ∩ P|}` over the lines `ℓ` determined by `P`,
and let `F(n)` count the possible sets `A`. Is `F(n) ≤ exp(O(√n))`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #607, https://www.erdosproblems.com/607 (status
PROVED). UnsolvedMath record UM-30006949 (`EP-607`), dataset ulamai/UnsolvedMath v1.8.0.

The lines determined by `P` are the lines `line[ℝ, p, q]` through two distinct points of `P`. Every
`A(P)` is a subset of `{0, …, n}`, so `F(n)` is counted inside that powerset. `exp(O(√n))` is `∃ C,
∀ n, F(n) ≤ exp(C √n)`, equivalent because `F(n)` is finite for each `n` and `F(0) = 1`.
-/

open Classical in
/-- `A(P)`: the set of the numbers `|ℓ ∩ P|` over the lines `ℓ` determined by `P` (the lines
through at least two points of `P`). -/
noncomputable def lineIncidenceSet (P : Finset (ℝ × ℝ)) : Finset ℕ :=
  P.offDiag.image fun pq => (P.filter fun r => r ∈ line[ℝ, pq.1, pq.2]).card

open Classical in
/-- `F(n)`: the number of distinct sets `A(P)` over all `n`-point sets `P ⊆ ℝ²` (every `A(P)` is a
subset of `{0, …, n}`). -/
noncomputable def lineIncidenceSetCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).powerset.filter fun A =>
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineIncidenceSet P = A).card

/-- Erdős Problem 607: `F(n) ≤ exp(O(√n))`. -/
def lineIncidenceSetCountSubexponential : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, (lineIncidenceSetCount n : ℝ) ≤ Real.exp (C * Real.sqrt n)

/--
Resolved true: erdosproblems.com/607 records that Szemerédi and Trotter proved `F(n) ≤ exp(O(√n))`.
Source: T. F. Bloom, Erdős Problems, Problem #607, https://www.erdosproblems.com/607 (status
PROVED); resolution: E. Szemerédi and W. T. Trotter, Extremal problems in discrete geometry,
Combinatorica 3 (1983), 381-392, erdosproblems.com/607: proved by Szemerédi and Trotter [SzTr83],
https://doi.org/10.1007/BF02579194.
-/
public theorem_wanted lineIncidenceSetCountSubexponential_holds :
    lineIncidenceSetCountSubexponential

end MathlibExt.Combinatorics.LineIncidenceSetsCountErdosProblem607Wanted
