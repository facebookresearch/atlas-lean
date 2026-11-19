/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem.Fixation

/-! Tests for fixation and absorption of the neutral Wright–Fisher martingale problem: the
boundary results on the frozen solutions at `0` and `1` (non-vacuity witnesses from the
`KimuraFixationProcess` tests), allele relabeling turning one witness into the other, and the
interior results instantiated at `x = 1 / 2` for an arbitrary solution. -/

open MeasureTheory Set
open scoped NNReal

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem

open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
open MathlibExt.Biology.PopulationGenetics.Diffusion (generator)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Non-vacuity witness (local copy of the module-private witness in the
`KimuraFixationProcess` tests): the process frozen at `c ∈ {0, 1}` solves the Wright–Fisher
martingale problem, because the generator vanishes at `0` and `1`. -/
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

/-! ### Structural lemmas on the witnesses -/

/-- The frozen process at `0` is a martingale. -/
example (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Martingale (fun _ _ => (0 : ℝ)) ℱ μ :=
  martingale_of_neutral (isWrightFisherSolution_const (Or.inl rfl) 0 ℱ μ)

/-- Relabeling the frozen solution at `0` gives a solution frozen at `1`. -/
example (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) :
    IsWrightFisherSolution 0 ℱ μ (fun _ _ => (1 : ℝ) - 0) :=
  isWrightFisherSolution_one_sub (isWrightFisherSolution_const (Or.inl rfl) 0 ℱ μ)

/-! ### Boundary `x = 0` -/

section Zero

variable (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]

example : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (fun _ _ => (0 : ℝ)) t ω = 0 :=
  ae_forall_eq_zero (isWrightFisherSolution_const (Or.inl rfl) 0 ℱ μ) (ae_of_all _ fun _ => rfl)

/-- Started at `0`, the allele is lost with probability `1`. -/
example : μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun _ _ => (0 : ℝ)) t ω = 0} = 1 :=
  (measureReal_loss_eq (isWrightFisherSolution_const (Or.inl rfl) 0 ℱ μ)
    (x := 0) (ae_of_all _ fun _ => rfl)).trans (sub_zero 1)

/-- Started at `0`, the allele is fixed with probability `0`. -/
example : μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun _ _ => (0 : ℝ)) t ω = 1} = 0 :=
  measureReal_fixation_eq (isWrightFisherSolution_const (Or.inl rfl) 0 ℱ μ)
    (ae_of_all _ fun _ => rfl)

example : ∀ᵐ ω ∂μ, absorptionTime (fun _ _ => (0 : ℝ)) ω = 0 :=
  ae_absorptionTime_eq_zero (μ := μ) (x := 0) (ae_of_all _ fun _ => rfl) (Or.inl rfl)

end Zero

/-! ### Boundary `x = 1` -/

section One

variable (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]

example : ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (fun _ _ => (1 : ℝ)) t ω = 1 :=
  ae_forall_eq_one (isWrightFisherSolution_const (Or.inr rfl) 0 ℱ μ) (ae_of_all _ fun _ => rfl)

/-- Started at `1`, the allele is fixed with probability `1`. -/
example : μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun _ _ => (1 : ℝ)) t ω = 1} = 1 :=
  measureReal_fixation_eq (isWrightFisherSolution_const (Or.inr rfl) 0 ℱ μ)
    (ae_of_all _ fun _ => rfl)

/-- Started at `1`, the allele is lost with probability `0`. -/
example : μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, (fun _ _ => (1 : ℝ)) t ω = 0} = 0 :=
  (measureReal_loss_eq (isWrightFisherSolution_const (Or.inr rfl) 0 ℱ μ)
    (x := 1) (ae_of_all _ fun _ => rfl)).trans (sub_self 1)

/-- The mean absorption time from a boundary is `0`. -/
example : ∫ ω, (absorptionTime (fun _ _ => (1 : ℝ)) ω : ℝ) ∂μ = 0 := by
  simpa using (integral_absorptionTime_eq (isWrightFisherSolution_const (Or.inr rfl) 0 ℱ μ)
    (x := 1) (ae_of_all _ fun _ => rfl)).2

end One

/-! ### Interior `x = 1 / 2`, for an arbitrary neutral solution -/

section Half

variable {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ}
  (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = 1 / 2)
include hX hX0

/-- Fixation and loss are equally likely from frequency `1 / 2`. -/
example : μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 1} =
    μ.real {ω | ∃ t₀ : ℝ≥0, ∀ t ≥ t₀, X t ω = 0} := by
  rw [measureReal_fixation_eq hX hX0, measureReal_loss_eq hX hX0]
  norm_num

/-- The mean frequency stays at `1 / 2`. -/
example (t : ℝ≥0) : ∫ ω, X t ω ∂μ = 1 / 2 := integral_apply_eq hX hX0 t

/-- The mean absorption time from frequency `1 / 2` is `2 log 2` (`≈ 1.386 · 2N`
generations). -/
example : ∫ ω, (absorptionTime X ω : ℝ) ∂μ = 2 * Real.log 2 := by
  rw [(integral_absorptionTime_eq hX hX0).2, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    one_div, Real.log_inv]
  ring

example : 0 < ∫ ω, (absorptionTime X ω : ℝ) ∂μ :=
  integral_absorptionTime_pos hX hX0 (by norm_num)

example : ∀ᵐ ω ∂μ, 0 < absorptionTime X ω :=
  ae_absorptionTime_pos hX hX0 (by norm_num)

end Half

#print axioms martingale_of_neutral
#print axioms isWrightFisherSolution_one_sub
#print axioms integral_apply_eq
#print axioms ae_forall_eq_zero
#print axioms ae_forall_eq_one
#print axioms measureReal_fixation_eq
#print axioms measureReal_loss_eq
#print axioms integral_absorptionTime_eq
#print axioms integral_absorptionTime_pos
#print axioms ae_absorptionTime_pos
#print axioms ae_absorptionTime_eq_zero

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.NeutralMartingaleProblem
