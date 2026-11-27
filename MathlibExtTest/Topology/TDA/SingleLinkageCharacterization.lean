/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.SingleLinkageCharacterization

@[expose] public section

open MathlibExt.Topology.TDA

/-- Joint-satisfiability check only: single linkage itself satisfies the hypotheses of the
characterization, so the theorem is not vacuous (its conclusion is then trivial). -/
example {X : Type} [Finite X] {d : X → X → ℝ} (hd : IsMetricFn d) :
    slDist d = slDist d :=
  eq_slDist_of_axioms (T := fun _ _ d => slDist d) slDist_axioms.1 slDist_axioms.2.1
    slDist_axioms.2.2.1 slDist_axioms.2.2.2 hd

/-- Condition (I) for single linkage: the two-point space at distance `3` is merged at `3`. -/
example : slDist (twoPointDist 3) true false = 3 := by
  have := congrFun (congrFun (slDist_axioms.2.1 3 (by norm_num)) true) false
  simpa [twoPointDist] using this

example : IsMetricFn (twoPointDist 1) := isMetricFn_twoPointDist one_pos
