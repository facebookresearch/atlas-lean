/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decreasing denominators of harmonic blocks (Erdős Problem 290)

Erdős Problem 290: let `a ≥ 1`. Must there be `b > a` such that, writing `∑_{a ≤ n ≤ b} 1/n = r₁/s₁`
and `∑_{a ≤ n ≤ b + 1} 1/n = r₂/s₂` in lowest terms, `s₂ < s₁`? If so, how does `b(a)` grow with
`a`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.HarmonicBlockDenominatorDropErdosProblem290Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #290, https://www.erdosproblems.com/290 (status PROVED
(LEAN)). UnsolvedMath record UM-30006808 (`EP-290`), dataset ulamai/UnsolvedMath v1.8.0.

Only the existence question is stated; the growth question is open-ended (van Doorn proves `a + 0.54
log a < b(a) ≤ 4.374 (a - 1)` for large `a`). `Rat.den` is the reduced denominator. Compared with
the formal-conjectures statement `ErdosProblems/290.lean` (identical statement; no code imported).
-/

/-- `∑_{a ≤ n ≤ b} 1/n` as a rational number. -/
def harmonicBlock (a b : ℕ) : ℚ :=
  ∑ n ∈ Finset.Icc a b, (1 : ℚ) / n

/-- Erdős Problem 290: for every `a ≥ 1` there is `b > a` such that the reduced denominator of
`∑_{a ≤ n ≤ b + 1} 1/n` is smaller than that of `∑_{a ≤ n ≤ b} 1/n`. -/
def harmonicBlockDenominatorDrops : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∃ b : ℕ, a < b ∧ (harmonicBlock a (b + 1)).den < (harmonicBlock a b).den

/--
Resolved true: van Doorn proved that `b(a)` exists for every `a` (indeed `b(a) ≪ a`).
erdosproblems.com/290 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#290, https://www.erdosproblems.com/290 (status PROVED (LEAN)); resolution: W. van Doorn, On the
non-monotonicity of the denominator of generalized harmonic sums, arXiv:2411.03073 (2024); formal
proof github.com/Woett/Lean-files, ErdosProblem290.lean, abstract: answers the first question in the
affirmative (for every a there is b with v_{a,b} < v_{a,b-1}) and proves a + 0.54 log(a) < b(a) ≤
4.374(a - 1) for large a, https://arxiv.org/abs/2411.03073.
-/
public theorem_wanted harmonicBlockDenominatorDrops_holds : harmonicBlockDenominatorDrops

end MathlibExt.NumberTheory.HarmonicBlockDenominatorDropErdosProblem290Wanted
