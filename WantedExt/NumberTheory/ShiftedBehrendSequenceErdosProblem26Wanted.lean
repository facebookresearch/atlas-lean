/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Behrend translates of infinite sets (Erdős Problem 26)

Erdős Problem 26 (Erdős and Tenenbaum): let `A ⊆ ℕ` be infinite. Must there be `k ≥ 1` such that
almost all integers have a divisor of the form `a + k` with `a ∈ A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ShiftedBehrendSequenceErdosProblem26Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #26, https://www.erdosproblems.com/26 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006687 (`EP-26`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is a set of positive integers (with `0 ∈ A` and `k = 1` the divisor `1` would trivialize the
claim for that `A`); "almost all" means natural density `1` among the positive integers.
formal-conjectures `ErdosProblems/26.lean` states the stronger refutation for sequences with `∑ 1/a
= ∞` (van Doorn); this module states the problem as posed (no code imported).
-/

open Filter Topology

/-- The positive integers having a divisor of the form `a + k` with `a ∈ A`. -/
def shiftedMultiples (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a ∈ A, a + k ∣ n}

/-- Erdős Problem 26: for every infinite set `A` of positive integers there is `k ≥ 1` such that
almost all integers have a divisor of the form `a + k` with `a ∈ A`, i.e. `shiftedMultiples A k`
has natural density `1`. -/
def existsShiftWithDensityOneMultiples : Prop :=
  ∀ A : Set ℕ, A.Infinite → 0 ∉ A → ∃ k : ℕ, 1 ≤ k ∧
    Tendsto (fun N : ℕ => ((shiftedMultiples A k ∩ Set.Icc 1 N).ncard : ℝ) / N) atTop (𝓝 1)

/--
Resolved false: by Davenport and Erdős a set whose multiples have density `1` has a divergent
reciprocal sum, so for an infinite `A` with `∑_{a ∈ A} 1/a < ∞` (for example the powers of `2`) no
translate `A + k` works; Ruzsa also gave an explicit counterexample. erdosproblems.com/26 lists the
problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #26,
https://www.erdosproblems.com/26 (status DISPROVED (LEAN)); resolution: H. Davenport and P. Erdős,
On sequences of positive integers, J. Indian Math. Soc. (N.S.) (1951), 19-24, erdosproblems.com/26:
every Behrend sequence B (almost all integers have a divisor in B) has ∑_{b∈B} 1/b = ∞ [DaEr51], so
any infinite A with ∑ 1/a < ∞ is a counterexample; Ruzsa's explicit counterexample is also recorded
there, https://www.erdosproblems.com/26.
-/
public theorem_wanted existsShiftWithDensityOneMultiples_refuted :
    ¬ existsShiftWithDensityOneMultiples

end MathlibExt.NumberTheory.ShiftedBehrendSequenceErdosProblem26Wanted
