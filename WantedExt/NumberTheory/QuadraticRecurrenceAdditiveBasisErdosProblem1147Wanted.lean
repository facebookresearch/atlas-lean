/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Quadratic recurrence sets as additive bases of order 2 (Erdős Problem 1147)

Erdős Problem 1147: let `α > 0` be irrational. Is `A = {n ≥ 1 : ‖α n²‖ < 1 / log n}`, with `‖·‖` the
distance to the nearest integer, an additive basis of order `2`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import MathlibExt.Combinatorics.Additive.Basis

@[expose] public section

namespace MathlibExt.NumberTheory.QuadraticRecurrenceAdditiveBasisErdosProblem1147Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1147, https://www.erdosproblems.com/1147 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007188 (`EP-1147`), dataset ulamai/UnsolvedMath v1.8.0.

The question is read for every irrational `α > 0`; additive basis of order `2` means asymptotic
basis (`Set.IsAsymptoticAddBasisOfOrder 2`: all large integers are sums of two elements). `n = 1` is
excluded since `1 / log 1` is undefined. Compared with the formal-conjectures statement
`ErdosProblems/1147.lean` (equivalent; no code imported).
-/

/-- `{n ≥ 2 : ‖α n²‖ < 1 / log n}`, where `‖y‖ = |y - round y|` is the distance from `y` to the
nearest integer (`n = 1` is excluded since `1 / log 1` is undefined). -/
def quadraticRecurrenceSet (α : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ |α * n ^ 2 - round (α * n ^ 2)| < 1 / Real.log n}

/-- Erdős Problem 1147: for every irrational `α > 0` the set is an asymptotic additive basis of
order `2` (every sufficiently large integer is the sum of two of its elements). -/
def quadraticRecurrenceSetIsBasisOfOrderTwo : Prop :=
  ∀ α : ℝ, 0 < α → Irrational α → (quadraticRecurrenceSet α).IsAsymptoticAddBasisOfOrder 2

/--
Resolved false: Konieczny proved that `A` is not an additive basis of order `2` for `α = √2` and for
almost every `α > 0` (indeed for every `ε(n) → 0` in place of `1 / log n`, for almost every `α`);
erdosproblems.com/1147 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#1147, https://www.erdosproblems.com/1147 (status DISPROVED (LEAN)); resolution: J. Konieczny, Sets
of recurrence as bases for the positive integers, Acta Arith. (2016), 309-338,
erdosproblems.com/1147: false for almost every α > 0 and for α = √2; formal proof plby/lean-proofs
src/latest/ErdosProblems/Erdos1147.lean.
-/
public theorem_wanted quadraticRecurrenceSetIsBasisOfOrderTwo_refuted :
    ¬ quadraticRecurrenceSetIsBasisOfOrderTwo

end MathlibExt.NumberTheory.QuadraticRecurrenceAdditiveBasisErdosProblem1147Wanted
