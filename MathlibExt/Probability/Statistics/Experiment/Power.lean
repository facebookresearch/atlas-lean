/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Probability.Distributions.CochranIndependence
public import MathlibExt.Probability.Distributions.GaussianCdf

/-!
# Law of the known-variance z statistic

For `n > 0` and known nonzero variance, the z statistic over an iid Gaussian
sample has a standard-unit-variance Gaussian law with the standardized mean.
Consequently the one-sided rejection set `zTestReject` has probability
`1 - Φ(c - √n δ / √v)` under a true mean shifted by `δ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace MathlibExt.Probability.Statistics.Experiment

/-- The known-variance z statistic. -/
noncomputable def zStat (n : ℕ) (μ0 : ℝ) (v : NNReal) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (n : ℝ) * ((∑ i, x i) / (n : ℝ) - μ0) / Real.sqrt (v : ℝ)

private theorem hasLaw_zStat_variance {n : ℕ} (hn : 0 < n) {v : NNReal} (hv : v ≠ 0) :
    (Real.sqrt (n : ℝ) / Real.sqrt (v : ℝ)) ^ 2 * ((v : ℝ) / (n : ℝ)) = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt v.coe_nonneg]
  field_simp

/-- Law of the known-variance z statistic under the iid Gaussian sample law. -/
theorem hasLaw_zStat {n : ℕ} (hn : 0 < n) (μ μ0 : ℝ) {v : NNReal} (hv : v ≠ 0) :
    HasLaw (zStat n μ0 v)
      (gaussianReal (Real.sqrt (n : ℝ) * (μ - μ0) / Real.sqrt (v : ℝ)) 1)
      (Measure.pi fun _ : Fin n => gaussianReal μ v) := by
  have hmean := hasLaw_sampleMean hn μ v
  have hsub : HasLaw (fun m : ℝ => m - μ0) (gaussianReal (μ - μ0) (v / n))
      (gaussianReal μ (v / n)) :=
    ⟨(measurable_id.sub_const μ0).aemeasurable, gaussianReal_map_sub_const μ0⟩
  have hmul : HasLaw (fun y : ℝ => (Real.sqrt (n : ℝ) / Real.sqrt (v : ℝ)) * y)
      (gaussianReal (Real.sqrt (n : ℝ) * (μ - μ0) / Real.sqrt (v : ℝ)) 1)
      (gaussianReal (μ - μ0) (v / n)) := by
    refine ⟨(measurable_const_mul _).aemeasurable, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · refine NNReal.coe_inj.mp ?_
      push_cast
      exact hasLaw_zStat_variance hn hv
  have hg : (fun m : ℝ => Real.sqrt (n : ℝ) * (m - μ0) / Real.sqrt (v : ℝ))
      = (fun y : ℝ => (Real.sqrt (n : ℝ) / Real.sqrt (v : ℝ)) * y)
        ∘ (fun m : ℝ => m - μ0) := by
    funext m
    simp only [Function.comp_apply]
    ring
  have hz : zStat n μ0 v
      = (fun m : ℝ => Real.sqrt (n : ℝ) * (m - μ0) / Real.sqrt (v : ℝ))
        ∘ (fun x : Fin n → ℝ => (∑ i, x i) / n) := by
    funext x
    simp only [zStat, Function.comp_apply]
  rw [hz, hg]
  exact hmul.comp (hsub.comp hmean)

/-- The one-sided z-test rejection set. -/
noncomputable def zTestReject (n : ℕ) (μ0 : ℝ) (v : NNReal) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | c < zStat n μ0 v x}

/-- Rejection probability of the one-sided z-test (tail form). -/
theorem measureReal_zTestReject {n : ℕ} (hn : 0 < n) (μ0 δ c : ℝ) {v : NNReal} (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real (zTestReject n μ0 v c)
      = 1 - cdf (gaussianReal 0 1) (c - Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ)) := by
  have h := hasLaw_zStat hn (μ0 + δ) μ0 hv
  rw [show (μ0 + δ) - μ0 = δ by ring] at h
  have h2 : (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real
        {x | c < zStat n μ0 v x}
      = (gaussianReal (Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ)) 1).real {y | c < y} :=
    h.measureReal_eq (p := fun y => c < y) measurableSet_Ioi
  have hcompl : {y : ℝ | c < y} = (Set.Iic c)ᶜ := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Iic, not_le]
  have hstd := cdf_gaussianReal_eq_std (Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ)) c
    (v := 1) one_ne_zero
  rw [NNReal.coe_one, Real.sqrt_one, div_one] at hstd
  change (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real
    {x | c < zStat n μ0 v x}
      = 1 - cdf (gaussianReal 0 1) (c - Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ))
  rw [h2, hcompl, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, hstd]

/-- Power of the one-sided z-test (`Φ` form): under true mean `μ0 + δ` the rejection set
`zTestReject n μ0 v c` has probability `Φ(√n δ / √v - c)`. -/
theorem measureReal_zTestReject_eq_cdf {n : ℕ} (hn : 0 < n) (μ0 δ c : ℝ) {v : NNReal}
    (hv : v ≠ 0) :
    (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real (zTestReject n μ0 v c)
      = cdf (gaussianReal 0 1) (Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ) - c) := by
  rw [measureReal_zTestReject hn μ0 δ c hv, ← cdf_gaussianReal_neg, neg_sub]

/-- Conservative integer sample-size certificate for the one-sided z test: with
`z_α = Φ⁻¹(1 - α)` and `z_β = Φ⁻¹(1 - β)`, any `n ≥ ⌈(√v (z_α + z_β) / δ)²⌉` gives power
at least `1 - β` against the shift `δ > 0`. -/
theorem power_ge_of_le_ceil {α β δ μ0 : ℝ} {v : NNReal}
    (hα : α ∈ Set.Ioo 0 (1 / 2)) (hβ : β ∈ Set.Ioo 0 (1 / 2)) (hδ : 0 < δ) (hv : v ≠ 0)
    {n : ℕ}
    (hN : ⌈(Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α)
        + cdfQuantile (gaussianReal 0 1) (1 - β)) / δ) ^ 2⌉₊ ≤ n) :
    1 - β ≤ (Measure.pi fun _ : Fin n => gaussianReal (μ0 + δ) v).real
      (zTestReject n μ0 v (cdfQuantile (gaussianReal 0 1) (1 - α))) := by
  have hzα : 0 < cdfQuantile (gaussianReal 0 1) (1 - α) := by
    apply cdfQuantile_gaussianReal_pos
    obtain ⟨h0, h1⟩ := hα
    exact ⟨by linarith, by linarith⟩
  have hzβ : 0 < cdfQuantile (gaussianReal 0 1) (1 - β) := by
    apply cdfQuantile_gaussianReal_pos
    obtain ⟨h0, h1⟩ := hβ
    exact ⟨by linarith, by linarith⟩
  have hvR : 0 < (v : ℝ) := by
    have h : (0 : NNReal) < v := pos_iff_ne_zero.mpr hv
    exact_mod_cast h
  have hsv : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hvR
  have hxnn : 0 ≤ Real.sqrt (v : ℝ) *
      (cdfQuantile (gaussianReal 0 1) (1 - α) +
        cdfQuantile (gaussianReal 0 1) (1 - β)) / δ :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (le_of_lt (add_pos hzα hzβ))) (le_of_lt hδ)
  have hx2 : (Real.sqrt (v : ℝ) *
      (cdfQuantile (gaussianReal 0 1) (1 - α) +
        cdfQuantile (gaussianReal 0 1) (1 - β)) / δ) ^ 2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hxn : Real.sqrt (v : ℝ) *
      (cdfQuantile (gaussianReal 0 1) (1 - α) +
        cdfQuantile (gaussianReal 0 1) (1 - β)) / δ ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt hx2
    rwa [Real.sqrt_sq hxnn] at h
  have h1 : Real.sqrt (v : ℝ) *
      (cdfQuantile (gaussianReal 0 1) (1 - α) +
        cdfQuantile (gaussianReal 0 1) (1 - β)) ≤ Real.sqrt (n : ℝ) * δ :=
    (div_le_iff₀ hδ).mp hxn
  have h2 : cdfQuantile (gaussianReal 0 1) (1 - α) +
      cdfQuantile (gaussianReal 0 1) (1 - β) ≤
      Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ) := by
    rw [le_div_iff₀ hsv]
    calc (cdfQuantile (gaussianReal 0 1) (1 - α) +
          cdfQuantile (gaussianReal 0 1) (1 - β)) * Real.sqrt (v : ℝ)
        = Real.sqrt (v : ℝ) * (cdfQuantile (gaussianReal 0 1) (1 - α) +
          cdfQuantile (gaussianReal 0 1) (1 - β)) := mul_comm _ _
      _ ≤ Real.sqrt (n : ℝ) * δ := h1
  have hkey : cdfQuantile (gaussianReal 0 1) (1 - β) ≤
      Real.sqrt (n : ℝ) * δ / Real.sqrt (v : ℝ) -
        cdfQuantile (gaussianReal 0 1) (1 - α) := by
    rw [le_sub_iff_add_le]
    linarith [h2]
  have hn : 0 < n := lt_of_lt_of_le
    (Nat.ceil_pos.mpr (pow_pos (div_pos (mul_pos hsv (add_pos hzα hzβ)) hδ) 2)) hN
  rw [measureReal_zTestReject_eq_cdf hn μ0 δ _ hv]
  have hu : 1 - β ∈ Set.Ioo (0 : ℝ) 1 := by
    obtain ⟨h0, h1⟩ := hβ
    exact ⟨by linarith, by linarith⟩
  exact (cdfQuantile_mem (gaussianReal 0 1) hu).trans
    (monotone_cdf (gaussianReal 0 1) hkey)

end MathlibExt.Probability.Statistics.Experiment
