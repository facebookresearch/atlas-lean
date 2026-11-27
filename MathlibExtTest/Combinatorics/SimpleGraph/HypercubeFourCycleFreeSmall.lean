/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeSmall

/-! # Regression tests for the exact small hypercube Turán numbers -/

open MathlibExt.Combinatorics.SimpleGraph.HypercubeFourCycleFreeWanted
open SimpleGraph

example : (List.range 6).map (fun i => hypercubeTuranNumber (i + 1) (cycleGraph 4)) =
    [1, 3, 9, 24, 56, 132] :=
  hypercubeTuranNumber_cycleGraph_four_one_to_six

example : ∃ S : (hypercubeGraph 6).Subgraph,
    (cycleGraph 4).Free S.coe ∧ S.edgeSet.ncard = 132 := by
  have hSix := congrArg (fun xs : List ℕ => xs[5]?)
    hypercubeTuranNumber_cycleGraph_four_one_to_six
  have hval : hypercubeTuranNumber 6 (cycleGraph 4) = 132 := Option.some.inj hSix
  have hne : ∃ S : (hypercubeGraph 6).Subgraph, (cycleGraph 4).Free S.coe := by
    refine ⟨⊥, ?_⟩
    intro h
    obtain ⟨f⟩ := h
    exact f 0 |>.property
  rw [← hval]
  exact exists_attains_hypercubeTuranNumber 6 hne
