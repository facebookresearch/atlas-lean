/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.CocompactAsymptoticallyEquivalentMetrics

open MathlibExt.Geometry.CocompactAsymptoticallyEquivalentMetricsWanted

universe u v

-- One pair of metrics, with independently specified group and space universes, defeats every bound.
example : ∃ (Γ : Type u) (M : Type v) (_ : Group Γ) (_ : MetricSpace M) (_ : CompleteSpace M)
    (_ : MulAction Γ M) (D : OWR1319022Data Γ M), ∀ C : ℝ, ∃ x y : M,
      C < |dist x y - D.d2 x y| := by
  by_contra! h
  apply conjecture_refuted.{u, v}
  intro Γ M _ _ _ _ D
  exact h Γ M _ _ _ _ D

-- For tolerance one, the ratio estimate on a nonempty space must exclude the diagonal.
example {Γ M : Type*} [Group Γ] [MetricSpace M] [CompleteSpace M] [MulAction Γ M] [Nonempty M]
    (D : OWR1319022Data Γ M) :
    ∃ R > 0, ∀ x y : M, R ≤ dist x y → |dist x y / D.d2 x y - 1| < 1 := by
  obtain ⟨R, hR⟩ := D.asymptotic 1 zero_lt_one
  refine ⟨R, lt_of_not_ge fun h ↦ ?_, hR⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  simpa using hR x x (by simpa using h)
