/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Erdős discrepancy problem (Erdős Problem 67)

Erdős Problem 67: if `f : ℕ → {-1, +1}` then is it true that for every `C > 0` there exist `d, m ≥
1` such that `|∑_{1 ≤ k ≤ m} f(kd)| > C`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.SignSequenceDiscrepancyErdosProblem67Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #67, https://www.erdosproblems.com/67 (status PROVED).
UnsolvedMath record UM-30006708 (`EP-67`), dataset ulamai/UnsolvedMath v1.8.0.

`f` is an integer-valued function taking only the values `±1` (its value at `0` is irrelevant).
Compared with the formal-conjectures statement `ErdosProblems/67.lean` (equivalent; no code
imported).
-/

/-- Erdős Problem 67 (the Erdős discrepancy problem): for every `f : ℕ → {-1, +1}` and every
`C > 0` there are `d, m ≥ 1` with `|∑_{1 ≤ k ≤ m} f(kd)| > C`. -/
def signSequenceUnboundedDiscrepancy : Prop :=
  ∀ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) → ∀ C : ℝ, 0 < C →
    ∃ d m : ℕ, 1 ≤ d ∧ 1 ≤ m ∧ C < |((∑ k ∈ Finset.Icc 1 m, f (k * d) : ℤ) : ℝ)|

/--
Resolved true: Tao proved that every sequence `f : ℕ → {-1, +1}` has unbounded discrepancy `sup_{m,
d ≥ 1} |∑_{k ≤ m} f(kd)|`; erdosproblems.com/67 lists the problem as proved. Source: T. F. Bloom,
Erdős Problems, Problem #67, https://www.erdosproblems.com/67 (status PROVED); resolution: T. Tao,
The Erdős discrepancy problem, Discrete Anal. 2016, Paper No. 1, 29 pp., abstract of
arXiv:1509.05363: for any f : ℕ → {-1, +1} the discrepancy sup_{n, d} |∑_{j ≤ n} f(jd)| is infinite;
erdosproblems.com/67: proved by Tao, https://arxiv.org/abs/1509.05363.
-/
public theorem_wanted signSequenceUnboundedDiscrepancy_holds : signSequenceUnboundedDiscrepancy

end MathlibExt.NumberTheory.SignSequenceDiscrepancyErdosProblem67Wanted
