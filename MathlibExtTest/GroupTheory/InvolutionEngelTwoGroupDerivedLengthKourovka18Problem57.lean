/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.InvolutionEngelTwoGroupDerivedLengthKourovka18Problem57

open MathlibExt.GroupTheory.InvolutionEngelTwoGroupDerivedLengthKourovka18Problem57Wanted

-- Each proposed bound yields a finite witness with a nontrivial term in its derived series.
example (d : ℕ) :
    ∃ (G : Type) (group : Group G) (_ : Finite G),
      @IsInvolutionEngelTwoGroup G group ∧ @Subgroup.derivedSeries G group d ≠ ⊥ := by
  classical
  by_contra h
  apply involutionEngelTwoGroupsBoundedDerivedLength_refuted
  refine ⟨d, fun G group finite hG ↦ ?_⟩
  by_contra hD
  exact h ⟨G, group, finite, hG, hD⟩
