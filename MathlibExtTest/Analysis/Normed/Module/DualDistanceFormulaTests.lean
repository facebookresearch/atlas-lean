/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Module.DualDistanceFormula
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Tests for the dual distance formula

* On `ℝ × ℝ`, the distance from `(0, 1)` to the zero subspace is `1`,
  and the attainment theorem produces a functional of norm at most `1`
  with value `1` at `(0, 1)`; the supremum formula gives `1`.
* The distance to the whole space `⊤` is `0`, and the attaining
  functional is the zero functional.
* On `ℝ × ℝ`, the distance from `(0, 1)` to the `x`-axis
  `span ℝ {(1, 0)}` is `1`, and the closed-subspace form produces a
  functional of norm exactly `1` with value `1` at `(0, 1)` that
  vanishes on the `x`-axis.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Module.DualDistanceFormulaTests

open MathlibExt.Analysis.Normed.Module.DualDistanceFormula
open Metric

/-- The distance from `(0, 1)` to a point `(c, 0)` of the `x`-axis is
`max |c| 1`. -/
theorem dist_axis (c : ℝ) : dist ((0, 1) : ℝ × ℝ) (c • (1, 0)) = max |c| 1 := by
  simp [Prod.dist_eq, Real.dist_eq]

/-- The distance from `(0, 1)` to the zero subspace of `ℝ × ℝ` is `1`. -/
example : Metric.infDist ((0, 1) : ℝ × ℝ)
    ((⊥ : Submodule ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) = 1 := by
  rw [Submodule.bot_coe, Metric.infDist_singleton, dist_eq_norm]
  simp [Prod.norm_def]

/-- The attainment theorem on the zero subspace: a functional of norm at
most `1` with value `1` at `(0, 1)`. -/
example : ∃ f : (ℝ × ℝ) →L[ℝ] ℝ, (∀ s ∈ (⊥ : Submodule ℝ (ℝ × ℝ)), f s = 0) ∧
    ‖f‖ ≤ 1 ∧ f (0, 1) = 1 := by
  obtain ⟨f, hfvan, hf_norm, hf_val⟩ :=
    exists_annihilating_apply_eq_infDist (⊥ : Submodule ℝ (ℝ × ℝ)) (0, 1)
  have hdist : Metric.infDist ((0, 1) : ℝ × ℝ)
      ((⊥ : Submodule ℝ (ℝ × ℝ)) : Set (ℝ × ℝ)) = 1 := by
    rw [Submodule.bot_coe, Metric.infDist_singleton, dist_eq_norm]
    simp [Prod.norm_def]
  rw [hdist] at hf_val
  exact ⟨f, hfvan, hf_norm, by simpa using hf_val⟩

/-- The supremum formula on the zero subspace: the supremum is `1`. -/
example : sSup { r : ℝ | ∃ f : (ℝ × ℝ) →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧
    (∀ s ∈ (⊥ : Submodule ℝ (ℝ × ℝ)), f s = 0) ∧ ‖f (0, 1)‖ = r } = 1 := by
  rw [← infDist_eq_sSup_norm_apply (⊥ : Submodule ℝ (ℝ × ℝ)) (0, 1)]
  rw [Submodule.bot_coe, Metric.infDist_singleton, dist_eq_norm]
  simp [Prod.norm_def]

/-- The distance from any point to the whole space is `0`. -/
example (x : ℝ) : Metric.infDist x ((⊤ : Submodule ℝ ℝ) : Set ℝ) = 0 := by
  refine le_antisymm ?_ Metric.infDist_nonneg
  have h : Metric.infDist x ((⊤ : Submodule ℝ ℝ) : Set ℝ) ≤ dist x x :=
    Metric.infDist_le_dist_of_mem Submodule.mem_top
  simpa using h

/-- The attaining functional for the whole space is the zero
functional. -/
example (x : ℝ) : ∃ f : ℝ →L[ℝ] ℝ, (∀ s ∈ (⊤ : Submodule ℝ ℝ), f s = 0) ∧
    ‖f‖ ≤ 1 ∧ f = 0 := by
  obtain ⟨f, hfvan, hf_norm, -⟩ := exists_annihilating_apply_eq_infDist (⊤ : Submodule ℝ ℝ) x
  refine ⟨f, hfvan, hf_norm, ?_⟩
  refine ContinuousLinearMap.ext fun y => ?_
  have h := hfvan y Submodule.mem_top
  simpa using h

/-- The distance from `(0, 1)` to the `x`-axis in `ℝ × ℝ` is `1`: the
distance to a point `(c, 0)` of the axis is `max |c| 1 ≥ 1`, and `0`
realizes `1`. -/
example : Metric.infDist ((0, 1) : ℝ × ℝ)
    ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) = 1 := by
  apply le_antisymm
  · have h : Metric.infDist ((0, 1) : ℝ × ℝ)
        ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) ≤
        dist ((0, 1) : ℝ × ℝ) 0 :=
      Metric.infDist_le_dist_of_mem (zero_mem _)
    simpa [Prod.dist_eq, Real.dist_eq] using h
  · refine (Metric.le_infDist ⟨0, zero_mem _⟩).mpr fun s hs => ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hs
    rw [← hc, dist_axis c]
    exact le_max_right _ _

/-- The `x`-axis is closed, as the span of a single vector. -/
example : IsClosed ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) :=
  Submodule.closed_of_finiteDimensional _

/-- `(0, 1)` is not on the `x`-axis. -/
example : ((0, 1) : ℝ × ℝ) ∉ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)) := by
  intro h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp h
  have h2 := congrArg Prod.snd hc
  simp at h2

/-- The closed-subspace form on the `x`-axis: a functional of norm
exactly `1` with value `1` at `(0, 1)` that vanishes on the axis. -/
example : ∃ f : (ℝ × ℝ) →L[ℝ] ℝ,
    (∀ s ∈ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)), f s = 0) ∧ ‖f‖ = 1 ∧
      f (0, 1) = 1 := by
  have hclosed : IsClosed ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) :=
    Submodule.closed_of_finiteDimensional _
  have hnot : ((0, 1) : ℝ × ℝ) ∉ Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ)) := by
    intro h
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp h
    have h2 := congrArg Prod.snd hc
    simp at h2
  obtain ⟨f, hfvan, hf_norm, hf_val⟩ :=
    exists_annihilating_of_notMem (Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) hclosed hnot
  have hdist : Metric.infDist ((0, 1) : ℝ × ℝ)
      ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) = 1 := by
    apply le_antisymm
    · have h : Metric.infDist ((0, 1) : ℝ × ℝ)
          ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) ≤
          dist ((0, 1) : ℝ × ℝ) 0 :=
        Metric.infDist_le_dist_of_mem (zero_mem _)
      simpa [Prod.dist_eq, Real.dist_eq] using h
    · refine (Metric.le_infDist ⟨0, zero_mem _⟩).mpr fun s hs => ?_
      obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hs
      rw [← hc, dist_axis c]
      exact le_max_right _ _
  rw [hdist] at hf_val
  exact ⟨f, hfvan, hf_norm, by simpa using hf_val⟩

/-- The quotient-map norm identity on the `x`-axis: the class of
`(0, 1)` has norm `1`. -/
example : ‖(Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))).mkQL (0, 1)‖ = 1 := by
  rw [norm_mkQL_apply]
  apply le_antisymm
  · have h : Metric.infDist ((0, 1) : ℝ × ℝ)
        ((Submodule.span ℝ ({(1, 0)} : Set (ℝ × ℝ))) : Set (ℝ × ℝ)) ≤
        dist ((0, 1) : ℝ × ℝ) 0 :=
      Metric.infDist_le_dist_of_mem (zero_mem _)
    simpa [Prod.dist_eq, Real.dist_eq] using h
  · refine (Metric.le_infDist ⟨0, zero_mem _⟩).mpr fun s hs => ?_
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hs
    rw [← hc, dist_axis c]
    exact le_max_right _ _

end MathlibExtTest.Analysis.Normed.Module.DualDistanceFormulaTests
