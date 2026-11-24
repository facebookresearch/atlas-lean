/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.PoissonDirichlet

/-! Tests for the GEM and Poisson–Dirichlet laws: a concrete ranking, the first-coordinate
mean and the a.e. summation as importing restatements, and the `θ = 0` boundary. -/

open MeasureTheory Filter Finset Topology
open scoped ENNReal

namespace MathlibExtTest.Probability.PoissonDirichlet

open ProbabilityTheory

example :
    rankDesc ((fun i : ℕ => if i = 0 then (1 / 2 : ℝ) else if i = 1 then 3 / 10
        else if i = 2 then 1 / 5 else 0) ∘ Equiv.swap 0 1) =
      fun i => if i = 0 then (1 / 2 : ℝ) else if i = 1 then 3 / 10 else if i = 2 then 1 / 5
        else 0 := by
  have hanti : Antitone fun i : ℕ => if i = 0 then (1 / 2 : ℝ) else if i = 1 then 3 / 10
      else if i = 2 then 1 / 5 else 0 := by
    refine antitone_nat_of_succ_le fun n => ?_
    rcases n with _ | _ | _ | n <;> simp <;> norm_num
  have hb : BddAbove (Set.range fun i : ℕ => if i = 0 then (1 / 2 : ℝ) else if i = 1 then 3 / 10
      else if i = 2 then 1 / 5 else 0) :=
    ⟨1 / 2, by rintro _ ⟨i, rfl⟩; exact (hanti (Nat.zero_le i)).trans_eq (by simp)⟩
  rw [rankDesc_comp_equiv hb, rankDesc_of_antitone hanti]

example (θ : ℝ) (hθ : 0 < θ) : ∫ p, p 0 ∂gemMeasure θ hθ = 1 / (1 + θ) :=
  integral_gemMeasure_zero θ hθ

example {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P : StickBreakingProcess μ X} {θ : ℝ} (hP : P.IsDirichlet θ) :
    μ[P.weight 0] = 1 / (1 + θ) := by
  rw [hP.integral_weight]; simp

example (θ : ℝ) (hθ : 0 < θ) : ∀ᵐ p ∂gemMeasure θ hθ, HasSum p 1 :=
  (ae_hasSum_gemMeasure θ hθ).mono fun _ h => h.2

example {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {P : StickBreakingProcess μ X} {θ : ℝ} (hP : P.IsDirichlet θ) :
    ∀ᵐ ω ∂μ, HasSum (fun k => P.weight k ω) 1 :=
  hP.ae_hasSum_weight

example : betaMeasure 1 0 = 0 := by
  unfold betaMeasure
  have : betaPDF 1 0 = 0 := by
    funext x
    simp [betaPDF, betaPDFReal, ProbabilityTheory.beta, Real.Gamma_zero]
  rw [this, withDensity_zero]

end MathlibExtTest.Probability.PoissonDirichlet
