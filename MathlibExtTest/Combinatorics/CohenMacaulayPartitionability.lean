/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CohenMacaulayPartitionability

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared
open MathlibExt.Combinatorics.CohenMacaulayPartitionabilityAMR156Problem0005Wanted

-- The empty face is itself a facet of this complex. Its sole interval covers it.
example : IsPartitionable {∅} := by
  refine ⟨fun _ => ∅, by simp, ?_⟩
  intro σ hσ
  obtain rfl := Finset.mem_singleton.mp hσ
  refine ⟨∅, ⟨⟨by simp, ?_⟩, by simp⟩, ?_⟩
  · intro G hG _
    exact Finset.mem_singleton.mp hG
  · intro F hF
    exact Finset.mem_singleton.mp hF.1.1

example : ∃ K, IsSimplicialComplex K ∧ IsPure K ∧ IsCohenMacaulayOverRat K ∧
    ¬ IsPartitionable K := by
  simpa only [cohenMacaulayPartitionable, Classical.not_forall, exists_prop] using
    cohenMacaulayPartitionable_refuted
