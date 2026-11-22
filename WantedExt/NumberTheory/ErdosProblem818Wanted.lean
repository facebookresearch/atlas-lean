/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 818
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic

@[expose] public section

open scoped Pointwise

namespace MathlibExt.NumberTheory.ErdosProblem818Wanted

/-! Source record `FC-ErdosProblem818`, ported from FormalConjectures
`ErdosProblems/818.lean` and checked against erdosproblems.com/818.
The upstream `answer(True)` is dropped. Status: resolved true externally by
Solymosi [So09d]. This module states the historical proposition but does not
prove it; the stronger theorem and an external Lean proof are cited in the
registry. -/

/-- The historical sum-product growth question for small-doubling integer sets. -/
def conjecture : Prop :=
  ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ A : Finset ℤ, 2 ≤ A.card → ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
      c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C ≤ ((A * A).card : ℝ)

/--
Resolved true: Resolved externally by József Solymosi, who proved the stronger
logarithmic-denominator bound. This repository records the historical proposition, not an
internal proof. Source: József Solymosi, Bounding multiplicative energy by the sumset, Advances
in Mathematics 222 (2009), 402–408, https://doi.org/10.1016/j.aim.2009.04.006. Moved from
`OpenConjectures/NumberTheory/ErdosProblem818`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem818Wanted
