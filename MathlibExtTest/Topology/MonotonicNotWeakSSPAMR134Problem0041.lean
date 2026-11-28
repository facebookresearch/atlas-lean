/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MonotonicNotWeakSSPAMR134Problem0041

open MathlibExt.Topology.MonotonicNotWeakSSPAMR134Problem0041Wanted
open MathlibExt.Topology.SelectionPrinciplesShared

example : HasMonotonicSSP cantorSet ∧ ¬ HasWeakSSP cantorSet := by
  let _ : CompactSpace cantorSet := isCompact_iff_compactSpace.mp isCompact_cantorSet
  exact ⟨hasMonotonicSSP_of_compactSpace cantorSet, cantorSet_not_hasWeakSSP⟩

example : HasMonotonicSSP PUnit := hasMonotonicSSP_of_compactSpace PUnit

example : ¬ (∀ X : Set ℝ, HasMonotonicSSP X → HasWeakSSP X) :=
  monotonicSSPImpliesWeakSSP_refuted
