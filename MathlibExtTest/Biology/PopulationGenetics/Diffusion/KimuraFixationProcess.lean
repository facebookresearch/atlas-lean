/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess

/-! Tests for the process-level fixation probability and absorption time of the Wright–Fisher
diffusion: non-vacuity witnesses for the martingale problem (the processes frozen at `0` and at
`1`), the three main results instantiated on them, the junk value of `absorptionTime` on a path
that is never absorbed, and the regularity facts about Kimura's formula. -/

open MeasureTheory Set
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess

open MathlibExt.Biology.PopulationGenetics.Diffusion
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Non-vacuity witness: the process frozen at a boundary point `c ∈ {0, 1}` solves the
Wright–Fisher martingale problem for every `σ`, filtration and measure, because the generator
vanishes at `0` and `1`. -/
theorem isWrightFisherSolution_const {c : ℝ} (hc : c = 0 ∨ c = 1) (σ : ℝ)
    (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) :
    IsWrightFisherSolution σ ℱ μ (fun _ _ => c) := by
  have hgen : ∀ f : ℝ → ℝ, generator σ f c = 0 := fun f => by
    rcases hc with rfl | rfl <;> simp [generator]
  refine ⟨fun _ _ => ?_, fun _ => continuous_const, stronglyAdapted_const ℱ _, fun f _ => ?_⟩
  · rcases hc with rfl | rfl <;> simp
  · have h0 : (fun (t : ℝ≥0) (_ : Ω) =>
        f c - f c - ∫ s in (0 : ℝ)..(t : ℝ), generator σ f c) = 0 := by
      funext t ω
      simp [hgen]
    simpa only [h0] using martingale_zero ℝ ℱ μ

/-! ### The main results on the witnesses -/

/-- The frozen process is absorbed. -/
example (σ : ℝ) (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∀ᵐ ω ∂μ, ∃ t₀ : ℝ≥0, (∀ t ≥ t₀, (fun _ _ => (0 : ℝ)) t ω = 0) ∨
      (∀ t ≥ t₀, (fun _ _ => (0 : ℝ)) t ω = 1) :=
  ae_exists_absorbed (isWrightFisherSolution_const (Or.inl rfl) σ ℱ μ)

/-- Started at `x = 1`, the allele is fixed with probability `kimuraFixation σ 1 = 1`. -/
example (σ : ℝ) (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun _ _ => (1 : ℝ)) t ω = 1} = 1 :=
  (measureReal_fixation (isWrightFisherSolution_const (Or.inr rfl) σ ℱ μ) (x := 1)
    (ae_of_all _ fun _ => rfl)).trans (kimuraFixation_one_right σ)

/-- Started at `x = 0`, the allele is never fixed: `kimuraFixation σ 0 = 0`. -/
example (σ : ℝ) (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun _ _ => (0 : ℝ)) t ω = 1} = 0 :=
  (measureReal_fixation (isWrightFisherSolution_const (Or.inl rfl) σ ℱ μ) (x := 0)
    (ae_of_all _ fun _ => rfl)).trans (kimuraFixation_zero_right σ)

/-- Started at a boundary, the expected absorption time is `meanAbsorptionTime 0 = 0`. -/
example (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∫ ω, (absorptionTime (fun _ _ => (0 : ℝ)) ω : ℝ) ∂μ = 0 := by
  simpa using (integral_absorptionTime (isWrightFisherSolution_const (Or.inl rfl) 0 ℱ μ)
    (x := 0) (ae_of_all _ fun _ => rfl)).2

/-! ### `absorptionTime` -/

/-- A path that starts at a boundary has absorption time `0`. -/
example (ω : Ω) : absorptionTime (fun _ _ => (1 : ℝ)) ω = 0 :=
  le_antisymm (csInf_le (OrderBot.bddBelow _) (Or.inr rfl)) zero_le

/-- Junk value: a path that is never absorbed also gets absorption time `0`
(`sInf ∅ = 0` in `ℝ≥0`); `ae_exists_absorbed` shows this does not happen for solutions. -/
example (ω : Ω) : absorptionTime (fun _ _ => (1 / 2 : ℝ)) ω = 0 := by
  have h : {t : ℝ≥0 | (1 / 2 : ℝ) = 0 ∨ (1 / 2 : ℝ) = 1} = ∅ := by
    ext t
    norm_num
  simp only [absorptionTime, h, NNReal.sInf_empty]

/-! ### Kimura's formula -/

example : ContDiff ℝ 2 (kimuraFixation (-3)) := contDiff_kimuraFixation (-3)

example : 0 < kimuraSlope (-3) := kimuraSlope_pos (-3)

/-- Deleterious alleles are still fixed more often from a higher starting frequency. -/
example : kimuraFixation (-2) (1 / 4) < kimuraFixation (-2) (1 / 2) :=
  strictMono_kimuraFixation (-2) (by norm_num)

#print axioms ae_exists_absorbed
#print axioms measureReal_fixation
#print axioms integral_absorptionTime

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
