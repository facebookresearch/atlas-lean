/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.AMSEstimator
public import MathlibExtTest.Probability.Streaming.AMSSketch

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Streaming.AMS

namespace MathlibExtTest.Probability.Streaming.AMS

/-! ## A non-degenerate instance of the median-of-means estimator

Sixteen independent copies of five fair signs (`s₁ = 16`, `λ = 1`) and one block (`s₂ = 1`)
satisfy every hypothesis of `measureReal_ams_estimate_le`. -/

-- Independence transported along a measure-preserving map.
theorem iIndepFun_comp_of_measurePreserving {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [Fintype ι] {f : ι → Ω → ℝ} {g : Ω' → Ω}
    (hg : MeasurePreserving g μ' μ) (hf : ∀ i, Measurable (f i)) (h : iIndepFun f μ) :
    iIndepFun (fun i => f i ∘ g) μ' := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hf i).comp hg.measurable).aemeasurable)]
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hf i).aemeasurable)] at h
  have hF : Measurable fun ω (i : ι) => f i ω := Measurable.of_eval hf
  have h1 : μ'.map (fun ω' i => (f i ∘ g) ω') = (μ'.map g).map (fun ω i => f i ω) := by
    rw [Measure.map_map hF hg.measurable]; rfl
  have h2 : ∀ i, μ'.map (f i ∘ g) = μ.map (f i) := fun i => by
    rw [← Measure.map_map (hf i) hg.measurable, hg.map_eq]
  rw [h1, hg.map_eq, h]
  simp_rw [h2]

-- Sixteen independent copies of the five-coin space.
noncomputable abbrev copies : Measure (Fin 16 → Fin 5 → Bool) := Measure.pi fun _ => coins

-- The sign families `ε 0 k i ω = ±1` read off copy `k`.
def blockSigns (_j : Fin 1) (k : Fin 16) (i : Fin 5) (ω : Fin 16 → Fin 5 → Bool) : ℝ :=
  signs i (ω k)

theorem blockSigns_measurable (j : Fin 1) (k : Fin 16) (i : Fin 5) :
    Measurable (blockSigns j k i) :=
  (signs_measurable i).comp (measurable_pi_apply k)

theorem blockSigns_mean (j : Fin 1) (k : Fin 16) (i : Fin 5) : copies[blockSigns j k i] = 0 := by
  have : ∫ ω, blockSigns j k i ω ∂copies = ∫ ω, signs i ω ∂coins :=
    integral_comp_eval (μ := fun _ => coins) (signs_measurable i).aestronglyMeasurable
  rw [this, signs_mean]

theorem blockSigns_fourWise (j : Fin 1) (k : Fin 16) :
    FourWiseIndependent (blockSigns j k) copies := by
  intro S hS
  exact iIndepFun_comp_of_measurePreserving (f := fun i : S => signs i)
    (measurePreserving_eval (fun _ => coins) k) (fun i => signs_measurable i)
    (signs_fourWise S hS)

theorem blockSigns_row :
    iIndepFun (fun j ω => fun k i => blockSigns j k i ω) copies :=
  iIndepFun.of_subsingleton

theorem blockSigns_col (j : Fin 1) :
    iIndepFun (fun k ω => fun i => blockSigns j k i ω) copies :=
  iIndepFun_pi (μ := fun _ => coins) (X := fun _ v i => signs i v) fun _ =>
    (Measurable.of_eval fun i => signs_measurable i).aemeasurable

-- The estimator with `λ = 1`, `s₁ = 16`, `s₂ = 1` on the stream `0, 1, 1`.
example : copies.real {ω | 1 * secondMoment ([0, 1, 1] : List (Fin 5)) <
    |MathlibExt.Probability.MedianOfMeans.sampleMedian (fun j => (1 / 16 : ℝ) *
      ∑ k, sketch (blockSigns j k) ([0, 1, 1] : List (Fin 5)) ω ^ 2) -
        secondMoment ([0, 1, 1] : List (Fin 5))|} ≤ Real.exp (-9 * 1 / 32) := by
  have := measureReal_ams_estimate_le (s₁ := 16) (s₂ := 1) blockSigns blockSigns_measurable
    (fun j k i ω => signs_sign i (ω k)) blockSigns_mean blockSigns_fourWise blockSigns_row
    blockSigns_col (lam := 1) one_pos (by norm_num) ([0, 1, 1] : List (Fin 5))
  simpa using this

end MathlibExtTest.Probability.Streaming.AMS
