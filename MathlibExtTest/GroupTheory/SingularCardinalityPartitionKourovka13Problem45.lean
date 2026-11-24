/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SingularCardinalityPartitionKourovka13Problem45
import Mathlib.Tactic.Push

open Cardinal
open scoped Pointwise
open MathlibExt.GroupTheory.SingularCardinalityPartitionKourovka13Problem45Wanted

-- Check that the exported refutation gives the counterexample in the wiki's existential form.
example :
    ∃ (G : Type) (_ : Group G), Infinite G ∧ ¬ (#G).IsRegular ∧
      ∀ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ → Disjoint A₁ A₂ →
        ∃ F : Set G, #F < #G ∧ (A₁ * F = Set.univ ∨ A₂ * F = Set.univ) := by
  have h := singularCardinalityPartition_refuted
  unfold singularCardinalityPartition at h
  push +distrib Not at h
  obtain ⟨G, group, hG, hSingular, h⟩ := h
  refine ⟨G, group, hG, hSingular, fun A₁ A₂ hUnion hDisjoint => ?_⟩
  exact ((h A₁ A₂).resolve_left (not_ne_iff.mpr hUnion)).resolve_left (not_not_intro hDisjoint)
