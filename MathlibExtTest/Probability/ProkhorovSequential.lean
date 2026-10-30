/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProkhorovSequential
public import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Tests for Prokhorov's theorem, sequential form on `ℝ`

Restatement of the public signature in
`MathlibExt.Probability.ProkhorovSequential`, plus concrete checks: the
constant Dirac sequence is tight (via the sequential direction), Dirac
masses supported in `{0, 1}` are tight (directly from the compact-set
characterization with `K = [0, 1]`), and the tightness-to-subsequence
direction applies to the constant Dirac sequence.
-/

@[expose] public section

open MeasureTheory Filter Set Topology ENNReal

open MathlibExt.Probability.ProkhorovSequential

namespace MathlibExtTest.Probability.ProkhorovSequential

/-- The sequential form of Prokhorov's theorem, with the exact public signature. -/
example (μ : ℕ → ProbabilityMeasure ℝ) :
    IsTightMeasureSet {((μ n : ProbabilityMeasure ℝ) : Measure ℝ) | n} ↔
      ∀ f : ℕ → ℕ, StrictMono f →
        ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ ν : ProbabilityMeasure ℝ,
          Tendsto (μ ∘ f ∘ g) atTop (𝓝 ν) :=
  prokhorov_sequential μ

/-- The constant Dirac sequence is tight. -/
theorem diracProba_const_tight :
    IsTightMeasureSet
      {(((fun _ : ℕ => diracProba (0 : ℝ)) n : ProbabilityMeasure ℝ) : Measure ℝ) | n} := by
  rw [prokhorov_sequential]
  intro f _
  exact ⟨id, strictMono_id, diracProba 0, tendsto_const_nhds⟩

/-- Dirac masses supported in `{0, 1}` are tight: the compact set
`[0, 1]` already captures all the mass. -/
theorem diracProba_mod_two_tight :
    IsTightMeasureSet
      {(((fun n : ℕ => diracProba ((n % 2 : ℕ) : ℝ)) n : ProbabilityMeasure ℝ) :
        Measure ℝ) | n} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε _
  refine ⟨Set.Icc (0 : ℝ) 1, isCompact_Icc, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hnot : ((n % 2 : ℕ) : ℝ) ∉ (Set.Icc (0 : ℝ) 1)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_not]
    constructor
    · exact Nat.cast_nonneg _
    · exact_mod_cast (by omega : n % 2 ≤ 1)
  have hzero : (diracProba ((n % 2 : ℕ) : ℝ) : Measure ℝ) (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    show (diracProba ((n % 2 : ℕ) : ℝ)).toMeasure (Set.Icc (0 : ℝ) 1)ᶜ = 0
    rw [diracProba_toMeasure_apply]
    exact Set.indicator_of_notMem hnot _
  rw [hzero]
  exact bot_le

/-- The tightness-to-subsequence direction applies to the constant Dirac
sequence: every subsequence has a convergent further subsequence. -/
example (f : ℕ → ℕ) (hf : StrictMono f) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∃ ν : ProbabilityMeasure ℝ,
      Tendsto ((fun _ : ℕ => diracProba (0 : ℝ)) ∘ f ∘ g) atTop (𝓝 ν) :=
  (prokhorov_sequential _).mp diracProba_const_tight f hf

end MathlibExtTest.Probability.ProkhorovSequential
