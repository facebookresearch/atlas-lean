/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.NormalClosureMinimalElementKourovka11Problem82

open MathlibExt.GroupTheory.NormalClosureMinimalElementKourovka11Problem82Wanted

-- Recover a counterexample with both commutator exclusions for every conjugating parameter.
example : ∃ (α : Type) (_ : DecidableEq α) (r : FreeGroup α), r ≠ 1 ∧
    ∃ s ∈ Subgroup.normalClosure {r}, s ≠ 1 ∧
      (∀ t ∈ Subgroup.normalClosure {r}, t ≠ 1 → s.norm ≤ t.norm) ∧
      ¬ IsConj s r ∧ ¬ IsConj s r⁻¹ ∧
      ∀ f : FreeGroup α, ¬ IsConj s (r⁻¹ * f⁻¹ * r * f) ∧ ¬ IsConj s (r * f⁻¹ * r⁻¹ * f) := by
  have h := minimalNormalClosureElementConj_refuted
  unfold minimalNormalClosureElementConj at h
  push Not at h
  exact h

-- Including the identity among the comparison words rules out every nontrivial minimum.
example {α : Type} [DecidableEq α] (r s : FreeGroup α) (hs : s ≠ 1) :
    ¬ ∀ t ∈ Subgroup.normalClosure {r}, s.norm ≤ t.norm := by
  intro h
  have h₀ := h 1 (Subgroup.one_mem _)
  exact hs (FreeGroup.norm_eq_zero.mp (by simpa using h₀))
