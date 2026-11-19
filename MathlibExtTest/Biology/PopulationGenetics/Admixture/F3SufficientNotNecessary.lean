/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.F3SufficientNotNecessary

/-!
# Tests for negative `f3` sufficiency and non-necessity

The examples restate the drift-model contrapositive, the exact masking
formula, the realized admixed/star pair, and the numerical acceptance cases.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsCovariance

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.F3SufficientNotNecessary

example {Ω P E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [Fintype E]
    (M : DriftModel μ E P) {C A B : P}
    (hA : ∀ e, 0 ≤ M.weight A e ∧ M.weight A e ≤ 1)
    (hB : ∀ e, 0 ≤ M.weight B e ∧ M.weight B e ≤ 1)
    (h : f3 μ M.freq C A B < 0) :
    ∃ e, M.weight C e ≠ 0 ∧ M.weight C e ≠ 1 :=
  M.exists_weight_ne_zero_ne_one_of_f3_neg hA hB h

example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {α a b c : ℝ}
    {M : DriftModel μ (Fin 3) (Fin 3)} (hw : M.weight = admixWeight α)
    (hl : M.len = ![a, b, c]) :
    f3 μ M.freq 2 0 1 = c - α * (1 - α) * (a + b) :=
  f3_admixWeight hw hl

example {α a b c : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : α * (1 - α) * (a + b) ≤ c) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 3)) (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω')
      (_ : IsProbabilityMeasure μ') (M' : DriftModel μ' (Fin 3) (Fin 3)),
        M.weight = admixWeight α ∧ M.len = ![a, b, c] ∧ ¬ M.HasBinaryLoadings ∧
        f3 μ M.freq 2 0 1 = c - α * (1 - α) * (a + b) ∧ 0 ≤ f3 μ M.freq 2 0 1 ∧
        M'.weight = starWeight ∧ M'.len = starLen α a b c ∧ M'.HasBinaryLoadings ∧
        (∀ X Y, f2 μ M.freq X Y = f2 μ' M'.freq X Y) ∧
        (∀ C A B, f3 μ M.freq C A B = f3 μ' M'.freq C A B) ∧
        (∀ A B C D, f4 μ M.freq A B C D = f4 μ' M'.freq A B C D) :=
  exists_admix_star_f3_nonneg hα0 hα1 ha hb hc

/-- Acceptance: `α = 1/2, a = b = 1, c = 1` gives `f3 = 1/2 > 0` with
admixture (non-binary loadings), indistinguishable by f-statistics from a star
tree with nonnegative lengths. -/
theorem half_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 3)),
        M.weight = admixWeight (1 / 2) ∧ ¬ M.HasBinaryLoadings ∧ f3 μ M.freq 2 0 1 = 1 / 2 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, _, _, _, _, _, hw, _, hnb, hf3, _⟩ :=
    exists_admix_star_f3_nonneg (α := 1 / 2) (a := 1) (b := 1) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Ω, hΩ, μ, hμ, M, hw, hnb, by rw [hf3]; norm_num⟩

/-- The masking boundary: at `c = α (1 - α) (a + b)` the admixed model has
`f3 = 0` (here `α = 1/2, a = b = 1, c = 1/2`), still with non-binary loadings. -/
theorem boundary_example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 3)),
        ¬ M.HasBinaryLoadings ∧ f3 μ M.freq 2 0 1 = 0 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, _, _, _, _, _, _, _, hnb, hf3, _⟩ :=
    exists_admix_star_f3_nonneg (α := 1 / 2) (a := 1) (b := 1) (c := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Ω, hΩ, μ, hμ, M, hnb, by rw [hf3]; norm_num⟩

/-- Explicit exclusion of the converse, inside the drift-model class:
`f3 ≥ 0` (here `f3 > 0`) does not imply binary loadings. -/
theorem f3_pos_not_binary :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (M : DriftModel μ (Fin 3) (Fin 3)),
        ¬ M.HasBinaryLoadings ∧ 0 < f3 μ M.freq 2 0 1 := by
  obtain ⟨Ω, hΩ, μ, hμ, M, _, hnb, hf3⟩ := half_example
  exact ⟨Ω, hΩ, μ, hμ, M, hnb, by rw [hf3]; norm_num⟩

/-- Endpoint `α = 0`: the admixture weights are binary and `f3 = c`, checked at
the level of the exact formula `f3_admixWeight` on an arbitrary model with
those weights and lengths. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {M : DriftModel μ (Fin 3) (Fin 3)}
    (hw : M.weight = admixWeight 0) (hl : M.len = ![1, 1, 1]) :
    f3 μ M.freq 2 0 1 = 1 := by
  rw [f3_admixWeight hw hl]
  norm_num

end MathlibExtTest.Biology.PopulationGenetics.Admixture.F3SufficientNotNecessary
