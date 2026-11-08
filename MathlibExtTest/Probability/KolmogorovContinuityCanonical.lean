/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.KolmogorovContinuity

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open MathlibExt.Probability.KolmogorovContinuity

namespace MathlibExtTest.Probability.KolmogorovContinuityCanonical

private def constantProcess : ℝ → Unit → ℝ := fun _ _ => 3

private theorem constant_canonical :
    IsKolmogorovProcess constantProcess (Measure.dirac ()) 2 (1 + 1) 0 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro s
    exact measurable_const
  · intro s t
    norm_num [constantProcess]
  · norm_num
  · norm_num

private def identityProcess : ℝ → Unit → ℝ := fun t _ => t

private theorem identity_canonical :
    IsKolmogorovProcess identityProcess (Measure.dirac ()) 2 (1 + 1) 1 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro s
    exact measurable_const
  · intro s t
    norm_num [identityProcess]
  · norm_num
  · norm_num

-- The direct result bounds X on one common full-measure set of sample points.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β K γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hK : 0 ≤ K)
    (hX_int : ∀ s t : ℝ, Integrable (fun ω => |X s ω - X t ω| ^ β) μ)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α))
    (hγα : γ < α / β) (hγ : 0 < γ) :
    ∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧ ∀ q r : ℝ,
      q ∈ dyadicRationals ∩ Set.Icc 0 1 → r ∈ dyadicRationals ∩ Set.Icc 0 1 →
      |X q ω - X r ω| ≤ C * |q - r| ^ γ := by
  exact kolmogorov_ae_holder_on_dyadics hα hβ hK hX_int hkolm γ hγα hγ

-- Standard witnesses need no additional caller integrability or real-integral bound.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β γ : ℝ} {M : ℝ≥0} (hα : 0 < α)
    (hX : IsKolmogorovProcess X μ β (1 + α) M) (hγα : γ < α / β) (hγ : 0 < γ) :
    ∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧ ∀ q r : ℝ,
      q ∈ dyadicRationals ∩ Set.Icc 0 1 → r ∈ dyadicRationals ∩ Set.Icc 0 1 →
      |X q ω - X r ω| ≤ C * |q - r| ^ γ := by
  exact kolmogorov_ae_holder_on_dyadics_of_isKolmogorovProcess hα hX γ hγα hγ

-- A genuine zero-bound canonical process is admitted.
example : ∀ᵐ ω ∂Measure.dirac (), ∃ C : ℝ, 0 < C ∧ ∀ q r : ℝ,
    q ∈ dyadicRationals ∩ Set.Icc 0 1 → r ∈ dyadicRationals ∩ Set.Icc 0 1 →
    |constantProcess q ω - constantProcess r ω| ≤ C * |q - r| ^ (1 / 4 : ℝ) := by
  exact kolmogorov_ae_holder_on_dyadics_of_isKolmogorovProcess
    (by norm_num : (0 : ℝ) < 1) constant_canonical (1 / 4) (by norm_num) (by norm_num)

-- The nonconstant deterministic identity process has β=2, α=1, M=1.
example : ∀ᵐ ω ∂Measure.dirac (), ∃ C : ℝ, 0 < C ∧ ∀ q r : ℝ,
    q ∈ dyadicRationals ∩ Set.Icc 0 1 → r ∈ dyadicRationals ∩ Set.Icc 0 1 →
    |identityProcess q ω - identityProcess r ω| ≤ C * |q - r| ^ (1 / 4 : ℝ) := by
  exact kolmogorov_ae_holder_on_dyadics_of_isKolmogorovProcess
    (by norm_num : (0 : ℝ) < 1) identity_canonical (1 / 4) (by norm_num) (by norm_num)

-- Both boundary times belong to the same dyadic domain and the same a.e. event.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {α β γ : ℝ} {M : ℝ≥0} (hα : 0 < α)
    (hX : IsKolmogorovProcess X μ β (1 + α) M) (hγα : γ < α / β) (hγ : 0 < γ) :
    ∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧ |X 0 ω - X 1 ω| ≤ C := by
  have h := kolmogorov_ae_holder_on_dyadics_of_isKolmogorovProcess hα hX γ hγα hγ
  filter_upwards [h] with ω hω
  obtain ⟨C, hC, hbound⟩ := hω
  refine ⟨C, hC, ?_⟩
  have h0 : (0 : ℝ) ∈ dyadicRationals ∩ Set.Icc 0 1 := by
    refine ⟨⟨0, 0, ?_⟩, ?_⟩ <;> norm_num
  have h1 : (1 : ℝ) ∈ dyadicRationals ∩ Set.Icc 0 1 := by
    refine ⟨⟨1, 0, ?_⟩, ?_⟩ <;> norm_num
  simpa using hbound 0 1 h0 h1

end MathlibExtTest.Probability.KolmogorovContinuityCanonical
