/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.GaussianDistortionFeasibility

@[expose] public section

open MathlibExt.InformationTheory.GaussianDistortionFeasibility MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.InformationTheory.GaussianDistortionFeasibility

/-- The square-error expectation/lower-integral agreement is the public
conversion used by the feasibility characterization. -/
example (μ : ProbabilityMeasure (ℝ × ℝ))
    (hint : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ))) :
    ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) =
      ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ)) :=
  ofReal_integral_sq_error_eq_lintegral μ hint

/-- Exact (diagonal) reconstruction is feasible at zero distortion. -/
example (σ2 : ℝ≥0) : diagonalReconstruction σ2 ∈ distortionFeasible σ2 0 := by
  have hmeas : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
  have hcomp : (Prod.fst ∘ fun x : ℝ => (x, x)) = id := rfl
  refine ⟨le_rfl, ?_, ?_⟩
  · change ((gaussianReal 0 σ2).map (fun x : ℝ => (x, x))).map Prod.fst = _
    rw [Measure.map_map measurable_fst hmeas, hcomp, Measure.map_id]
  · change ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
        ∂((gaussianReal 0 σ2).map (fun x : ℝ => (x, x))) ≤ _
    have hf : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - z.2) ^ 2)) :=
      ((measurable_fst.sub measurable_snd).pow_const 2).ennreal_ofReal
    rw [lintegral_map hf hmeas]
    simp

/-- A negative distortion level admits no joint law, even the zero-error one. -/
example (σ2 : ℝ≥0) : diagonalReconstruction σ2 ∉ distortionFeasible σ2 (-1) :=
  fun h => absurd h.1 (by norm_num)

/-- Hence the rate-distortion function is `⊤` at a negative level. -/
example (σ2 : ℝ≥0) : rateDistortion σ2 (-1) = ⊤ := by
  unfold rateDistortion
  simp only [iInf_eq_top]
  intro μ hμ
  exact absurd hμ.1 (by norm_num)

/-- Constant reconstruction attains `R(σ2) = 0`. -/
example (σ2 : ℝ≥0) : rateDistortion σ2 σ2 = 0 :=
  rateDistortion_self_eq_zero σ2

/-- The finite-distortion equivalence needs no positive variance: for the degenerate source
`σ2 = 0`, constant reconstruction has integrable square error with expectation at most `0`. -/
example : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)
      (constantReconstruction 0 : Measure (ℝ × ℝ)) ∧
    ∫ z, (z.1 - z.2) ^ 2 ∂(constantReconstruction 0 : Measure (ℝ × ℝ)) ≤ 0 := by
  have h := constantReconstruction_mem_distortionFeasible 0
  rw [mem_distortionFeasible_iff (NNReal.coe_nonneg 0)] at h
  exact ⟨h.2.1, by simpa using h.2.2⟩

/-- Kernel characterization: the identity reconstruction kernel is feasible at `D = 0`. -/
example (σ2 : ℝ≥0) :
    (⟨gaussianReal 0 σ2 ⊗ₘ Kernel.id, inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) ∈
      distortionFeasible σ2 0 := by
  rw [compProd_mem_distortionFeasible_iff σ2 le_rfl]
  simp [Kernel.id_apply]

end MathlibExtTest.InformationTheory.GaussianDistortionFeasibility
