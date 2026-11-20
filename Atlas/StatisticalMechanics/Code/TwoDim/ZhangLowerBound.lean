/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































































import Code.Universality.KestenHalf
import Code.Universality.RSWStrip

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality












theorem kzh_theta_real :
    (percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one).toReal
      = halfMeasure.real (percolationEvent 2) := rfl





theorem kzh_percProb_eq_zero_of_thetaReal_zero
    (h : halfMeasure.real (percolationEvent 2) = 0) :
    percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  unfold percolationProbability
  have hle : halfMeasure (percolationEvent 2) ≤ 1 :=
    le_trans (measure_mono (subset_univ _)) (by simp [measure_univ])
  have hfin : halfMeasure (percolationEvent 2) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  have hr : (halfMeasure (percolationEvent 2)).toReal = 0 := h
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right hfin























theorem kzh_crossing_to_one_of_union
    (hpa : PositivelyAssociated halfMeasure)
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hAm : ∀ n, MeasurableSet (A n)) (hBm : ∀ n, MeasurableSet (B n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hunion : Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1)) :
    Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 1) := by
  
  have hlb : ∀ n,
      1 - Real.sqrt (1 - halfMeasure.real (A n ∪ B n)) ≤ halfMeasure.real (A n) :=
    fun n => rsw_sqrt_trick_eq halfMeasure hpa (hAinc n) (hBinc n) (hAm n) (hBm n) (heq n)
  
  have hub : ∀ n, halfMeasure.real (A n) ≤ 1 := fun _ => measureReal_le_one
  
  have hlbtends :
      Tendsto (fun n => 1 - Real.sqrt (1 - halfMeasure.real (A n ∪ B n))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => (1 : ℝ) - halfMeasure.real (A n ∪ B n)) atTop (𝓝 0) := by
      have := hunion.const_sub (1 : ℝ); simpa using this
    have h2 : Tendsto (fun n => Real.sqrt (1 - halfMeasure.real (A n ∪ B n))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1; simpa using this
    have := h2.const_sub (1 : ℝ); simpa using this
  
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlbtends tendsto_const_nhds hlb hub







































theorem kzh_corLowerBound
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {A B : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated halfMeasure)
    (hAinc : ∀ n, IsIncreasing (A n)) (hBinc : ∀ n, IsIncreasing (B n))
    (hBm : ∀ n, MeasurableSet (B n))
    (hHm : ∀ n, MeasurableSet (A n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (A n)ᶜ = (R ∘ dualConfig) ⁻¹' (A n))
    (heq : ∀ n, halfMeasure.real (A n) = halfMeasure.real (B n))
    (hZhangUnion : BoxCrossingProperty halfMeasure 2 →
        0 < halfMeasure.real (percolationEvent 2) →
        Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1)) :
    BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  intro hbxp
  
  have hbalance : ∀ n : ℕ, halfMeasure.real (A n) = 1 / 2 := fun n =>
    half_crossingProb_of_selfDual_dichotomy (hHm n) hRmeas hRpres (hdich n)
  
  have hθ0 : halfMeasure.real (percolationEvent 2) = 0 := by
    by_contra hne
    have hpos : 0 < halfMeasure.real (percolationEvent 2) :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    
    have hunion : Tendsto (fun n => halfMeasure.real (A n ∪ B n)) atTop (𝓝 1) :=
      hZhangUnion hbxp hpos
    
    have hto1 : Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 1) :=
      kzh_crossing_to_one_of_union hpa hAinc hBinc hHm hBm heq hunion
    
    have hconst : Tendsto (fun n => halfMeasure.real (A n)) atTop (𝓝 (1 / 2 : ℝ)) := by
      have hfun : (fun n => halfMeasure.real (A n)) = fun _ => (1 / 2 : ℝ) := funext hbalance
      rw [hfun]; exact tendsto_const_nhds
    have hbad : (1 / 2 : ℝ) = 1 := tendsto_nhds_unique hconst hto1
    norm_num at hbad
  
  exact kzh_percProb_eq_zero_of_thetaReal_zero hθ0

end TwoDim

end StatMech
