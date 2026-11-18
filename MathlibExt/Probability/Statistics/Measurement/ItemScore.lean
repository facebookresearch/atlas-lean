/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemResponse
public import MathlibExt.Probability.Statistics.Measurement.ProductMoments
public import MathlibExt.Probability.Statistics.FisherInformation
public import MathlibExt.Probability.Statistics.VectorInference

/-!
# Canonical finite 2PL law and score

For a finite item type with arbitrary real discriminations `a` and
difficulties `b`, the canonical density law of counting measure with
the existing two-parameter logistic PMF as density is the PMF's own
measure, and the score at `E = Real` is, at every response pattern,
`sum_j a j * (Y j - p_j (theta))`. Its integral under that law is zero.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.Statistics.Measurement

private theorem pmf_sum_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ x, (p x).toReal) = 1 := by
  have hreal : (∑' x, p x).toReal = (1 : ENNReal).toReal := by
    rw [PMF.tsum_coe]
  rw [ENNReal.tsum_toReal_eq (fun x => PMF.apply_ne_top p x), tsum_fintype] at hreal
  simpa using hreal

theorem twoPLPMF_toReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (t : ℝ) (Y : ι → Bool) :
    (twoPLPMF a b t Y).toReal
      = ∏ i, (if Y i then Real.sigmoid (a i * (t - b i))
        else 1 - Real.sigmoid (a i * (t - b i))) := by
  exact localIndepPMF_toReal_apply _ _ _ _

theorem localIndepPMF_coord_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (j : ι) :
    (∑ Y : ι → Bool, (localIndepPMF q hq0 hq1 Y).toReal * (if Y j then (1 : ℝ) else 0))
      = q j := by
  have h := (localIndepPMF_coordinate_moments q hq0 hq1).1 j
  rw [PMF.integral_eq_sum] at h
  simpa [smul_eq_mul] using h

theorem twoPLPMF_coord_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) (j : ι) :
    (∑ Y : ι → Bool, (twoPLPMF a b θ Y).toReal * (if Y j then (1 : ℝ) else 0))
      = Real.sigmoid (a j * (θ - b j)) := by
  exact localIndepPMF_coord_sum _ _ _ _

theorem score_summand_hasDerivAt {ι : Type*}
    (a b : ι → ℝ) (θ : ℝ) (Y : ι → Bool) (j : ι) :
    HasDerivAt
      (fun t : ℝ => Real.log (if Y j then Real.sigmoid (a j * (t - b j))
        else 1 - Real.sigmoid (a j * (t - b j))))
      (a j * ((if Y j then (1 : ℝ) else 0) - Real.sigmoid (a j * (θ - b j)))) θ := by
  have haff : HasDerivAt (fun t : ℝ => a j * (t - b j)) (a j) θ := by
    simpa using HasDerivAt.const_mul (a j) ((hasDerivAt_id θ).sub_const (b j))
  have hsig : HasDerivAt (fun t : ℝ => Real.sigmoid (a j * (t - b j)))
      ((Real.sigmoid (a j * (θ - b j)) * (1 - Real.sigmoid (a j * (θ - b j))))
        * a j) θ :=
    HasDerivAt.comp θ (h := fun t : ℝ => a j * (t - b j)) (h₂ := Real.sigmoid)
      (Real.hasDerivAt_sigmoid _) haff
  by_cases hY : Y j = true
  · simp only [ite_eq_left hY]
    have hs0 : Real.sigmoid (a j * (θ - b j)) ≠ 0 :=
      ne_of_gt (Real.sigmoid_pos _)
    have hder : a j * (1 - Real.sigmoid (a j * (θ - b j)))
        = ((Real.sigmoid (a j * (θ - b j)) * (1 - Real.sigmoid (a j * (θ - b j))))
          * a j) / Real.sigmoid (a j * (θ - b j)) := by
      field_simp
    rw [hder]
    exact hsig.log hs0
  · simp only [ite_eq_right hY]
    have hs1 : (1 : ℝ) - Real.sigmoid (a j * (θ - b j)) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (Real.sigmoid_lt_one _))
    have hsub : HasDerivAt (fun t : ℝ => 1 - Real.sigmoid (a j * (t - b j)))
        (-((Real.sigmoid (a j * (θ - b j)) * (1 - Real.sigmoid (a j * (θ - b j))))
          * a j)) θ :=
      HasDerivAt.const_sub 1 hsig
    have hder : a j * (0 - Real.sigmoid (a j * (θ - b j)))
        = (-((Real.sigmoid (a j * (θ - b j)) * (1 - Real.sigmoid (a j * (θ - b j))))
          * a j)) / (1 - Real.sigmoid (a j * (θ - b j))) := by
      field_simp
      ring
    rw [hder]
    exact hsub.log hs1

end MathlibExt.Probability.Statistics.Measurement

namespace MathlibExt.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics

/-- **Canonical 2PL law.** The canonical density law of counting
measure on `ι → Bool` with the existing twoPL PMF as density via
`toReal` is exactly the PMF's own measure. No new law definition is
introduced. -/
theorem twoPL_lawOf_eq_toMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    FisherInformation.lawOf Measure.count
        (fun t Y => (twoPLPMF a b t Y).toReal) θ
      = (twoPLPMF a b θ).toMeasure := by
  show Measure.count.withDensity
      (fun x => ENNReal.ofReal ((twoPLPMF a b θ x).toReal))
      = (twoPLPMF a b θ).toMeasure
  apply Measure.ext_iff.mpr
  intro s hs
  rw [withDensity_apply _ hs, PMF.toMeasure_apply_fintype]
  rw [← lintegral_indicator hs, lintegral_count, tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- **Canonical 2PL score.** The `VectorInference.score` (parameter
space `E = ℝ`) of the twoPL density at `θ` is, at every response
pattern `Y`, `∑ j, a j * ((if Y j then 1 else 0) - p_j (θ))` with
`p_j (θ) = Real.sigmoid (a j * (θ - b j))`. No new score definition is
introduced. -/
theorem twoPL_score_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
  (a b : ι → ℝ) (θ : ℝ) (Y : ι → Bool) :
  VectorInference.score (fun t Y => (twoPLPMF a b t Y).toReal) θ Y
    = ∑ j, a j * ((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j))) := by

  show gradient (fun t : ℝ => Real.log ((twoPLPMF a b t Y).toReal)) θ
    = ∑ j, a j * ((if Y j then (1 : ℝ) else 0)
      - Real.sigmoid (a j * (θ - b j)))
  rw [gradient_eq_deriv']
  have hlog : ∀ t : ℝ, Real.log ((twoPLPMF a b t Y).toReal)
      = ∑ j, Real.log (if Y j then Real.sigmoid (a j * (t - b j))
        else 1 - Real.sigmoid (a j * (t - b j))) := by
    intro t
    have hne : ∀ j : ι, (if Y j then Real.sigmoid (a j * (t - b j))
        else 1 - Real.sigmoid (a j * (t - b j))) ≠ 0 := by
      intro j
      by_cases hY : Y j = true
      · simp only [ite_eq_left hY]
        exact ne_of_gt (Real.sigmoid_pos _)
      · simp only [ite_eq_right hY]
        exact ne_of_gt (sub_pos.mpr (Real.sigmoid_lt_one _))
    rw [twoPLPMF_toReal]
    exact Real.log_prod (fun j _ => hne j)
  simp only [hlog]
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ j, Real.log (if Y j then Real.sigmoid (a j * (t - b j))
        else 1 - Real.sigmoid (a j * (t - b j))))
      (∑ j, a j * ((if Y j then (1 : ℝ) else 0)
        - Real.sigmoid (a j * (θ - b j)))) θ :=
    HasDerivAt.fun_sum (fun j _ => score_summand_hasDerivAt a b θ Y j)
  rw [hsum.deriv]

/-- **The 2PL score has actual mean zero** .

For the same finite item type and arbitrary real discriminations, the Bochner integral of the
`VectorInference.score` of the `toReal`-of-`twoPLPMF` density, taken
against its canonical `FisherInformation.lawOf` on counting measure
(which `twoPL_lawOf_eq_toMeasure` identifies with the actual PMF measure
`(twoPLPMF a b θ).toMeasure`), is `0`.  This is the score mean-zero
identity for this model only; no generic score theorem is restated. -/
theorem integral_vector_score_twoPL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (θ : ℝ) :
    ∫ Y, VectorInference.score (fun t Y => (twoPLPMF a b t Y).toReal) θ Y
        ∂(FisherInformation.lawOf Measure.count
          (fun t Y => (twoPLPMF a b t Y).toReal) θ) = 0 := by
  have h1 := twoPL_lawOf_eq_toMeasure a b θ
  have h2 := twoPL_score_eq_sum a b θ
  rw [h1]
  simp only [h2]
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  have hfactor : ∀ Y : ι → Bool, (twoPLPMF a b θ Y).toReal
      * (a j * ((if Y j then (1 : ℝ) else 0) - Real.sigmoid (a j * (θ - b j))))
      = a j * ((twoPLPMF a b θ Y).toReal * (if Y j then (1 : ℝ) else 0)
        - (twoPLPMF a b θ Y).toReal * Real.sigmoid (a j * (θ - b j))) := by
    intro Y
    ring
  simp only [hfactor, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hconst : (∑ Y : ι → Bool,
      (twoPLPMF a b θ Y).toReal * Real.sigmoid (a j * (θ - b j)))
      = Real.sigmoid (a j * (θ - b j))
        * ∑ Y : ι → Bool, (twoPLPMF a b θ Y).toReal := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Y _
    ring
  simp only [twoPLPMF_coord_sum a b θ j, hconst, pmf_sum_toReal_eq_one (twoPLPMF a b θ),
    mul_one, sub_self, mul_zero]

end MathlibExt.Probability.Statistics.Measurement
