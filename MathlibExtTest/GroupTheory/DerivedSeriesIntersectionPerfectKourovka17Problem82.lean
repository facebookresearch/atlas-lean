/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.DerivedSeriesIntersectionPerfectKourovka17Problem82

open MathlibExt.GroupTheory.DerivedSeriesIntersectionPerfectKourovka17Problem82Wanted

example : ∃ (G : Type) (inst : Group G), letI := inst
    Group.IsFinitelyPresented G ∧
      ⁅⨅ n, Subgroup.derivedSeries G n, ⨅ n, Subgroup.derivedSeries G n⁆ ≠
        ⨅ n, Subgroup.derivedSeries G n := by
  classical
  by_contra h
  apply derivedSeriesIntersectionPerfect_refuted
  intro G inst hfp
  by_contra hnp
  exact h ⟨G, inst, hfp, hnp⟩
