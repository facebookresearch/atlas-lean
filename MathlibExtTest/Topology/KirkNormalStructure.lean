/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.KirkNormalStructure
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # Tests for Kirk's normal-structure fixed-point theorem -/

namespace MathlibExtTest.KirkNormalStructure

open MathlibExt.Topology.KirkNormalStructureWanted.Topology.KirkNormalStructure
open Set

-- In [-1, 1] the endpoints are two units apart, and the midpoint has radius one.
example : ¬ IsDiametralPoint (Icc (-1 : ℝ) 1) 0 := by
  have hd : metricDiameter (Icc (-1 : ℝ) 1) = 2 := by
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨-1, by norm_num, 1, by norm_num, by norm_num [Real.dist_eq]⟩
    · rintro _ ⟨x, ⟨hx, hx'⟩, y, ⟨hy, hy'⟩, rfl⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
  have hr : pointRadiusIn 0 (Icc (-1 : ℝ) 1) = 1 := by
    apply IsGreatest.csSup_eq
    constructor
    · exact ⟨1, by norm_num, by norm_num [Real.dist_eq]⟩
    · rintro _ ⟨x, hx, rfl⟩
      simpa [Real.dist_eq, abs_le] using hx
  intro h
  have heq := h.2
  rw [hd, hr] at heq
  norm_num at heq

-- Normal structure also includes a singleton, where the two-point hypothesis never holds.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (href : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (a : E) (T : ({a} : Set E) → ({a} : Set E)) : ∃ x, Function.IsFixedPt T x := by
  refine kirk_normal_structure href {a} (singleton_nonempty a) isClosed_singleton
    Bornology.isBounded_singleton (convex_singleton a) ?_ T ?_
  · intro H hH _ hnon
    exact (hnon.not_subsingleton (subsingleton_singleton.anti hH)).elim
  · apply LipschitzWith.mk_one
    intro x y
    simp [Subsingleton.elim x y]

end MathlibExtTest.KirkNormalStructure
