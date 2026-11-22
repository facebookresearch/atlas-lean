/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Few prime factors in all shifts (Erdős Problem 248)

Erdős Problem 248 (Erdős and Straus): are there infinitely many `n` such that `ω(n + k) ≪ k` for all
`k ≥ 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

namespace MathlibExt.NumberTheory.DistinctPrimeFactorsShiftsErdosProblem248Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #248, https://www.erdosproblems.com/248 (status PROVED
(LEAN)). UnsolvedMath record UM-30006792 (`EP-248`), dataset ulamai/UnsolvedMath v1.8.0.

The implied constant is uniform in `n`; if it could depend on `n`, every `n` would qualify since
`ω(m) ≤ log₂ m`. Compared with the formal-conjectures statement `ErdosProblems/248.lean`
(equivalent, there with `C > 0`; no code imported).
-/

/-- Erdős Problem 248: there are a constant `C` and infinitely many `n` such that
`ω(n + k) ≤ C k` for all `k ≥ 1`, where `ω` counts distinct prime factors. -/
def infinitelyManyLinearOmegaShifts : Prop :=
  ∃ C : ℝ, {n : ℕ | ∀ k : ℕ, 1 ≤ k →
    (ArithmeticFunction.cardDistinctFactors (n + k) : ℝ) ≤ C * k}.Infinite

/--
Resolved true: Tao and Teräväinen proved that there are an absolute `C` and infinitely many `n` with
`ω(n + k) ≤ Ω(n + k) ≤ C k` for all `k ≥ 1`; erdosproblems.com/248 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #248, https://www.erdosproblems.com/248 (status PROVED
(LEAN)); resolution: T. Tao and J. Teräväinen, Quantitative correlations and some problems on prime
factors of consecutive integers, arXiv:2512.01739 (2025), abstract, first result: infinitely many n
with ω(n + k) ≤ Ω(n + k) ≪ k for all k ≥ 1 (the Erdős-Straus conjecture); erdosproblems.com/248,
https://arxiv.org/abs/2512.01739.
-/
public theorem_wanted infinitelyManyLinearOmegaShifts_holds : infinitelyManyLinearOmegaShifts

end MathlibExt.NumberTheory.DistinctPrimeFactorsShiftsErdosProblem248Wanted
