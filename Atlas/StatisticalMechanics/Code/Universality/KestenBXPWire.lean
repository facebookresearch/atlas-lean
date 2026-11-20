/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









































































import Code.Universality.KestenAssembly
import Code.Universality.BXPAllAspect
import Code.Universality.BXPMinimalHyp
import Code.TwoDim.KestenCrossingDecay

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.RSW.Box












theorem kbw_halfMeasure_eq_rba : halfMeasure = rba_selfDualMeasure := rfl



theorem kbw_bxp_half_faithful
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (ρ : ℝ) (hρ : 1 < ρ) :
    BoxCrossingProperty halfMeasure ρ :=
  bmh_boxCrossingProperty_selfDual_faithful hpa hmeasGenH hmeasGenV
    hmeasFace hmeasThin h2box ρ hρ

























theorem kbw_bxp_half_supplied
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    (ρ : ℝ) (hρ : 1 < ρ) :
    BoxCrossingProperty halfMeasure ρ :=
  bxa_boxCrossingProperty_all hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV
    hseed h2box hband hrefl ρ hρ































theorem kbw_kesten_bxp_supplied
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 :=
  kesten_pc_eq_half_of_bxp (ρ := 2) (R := R) (boxFam := boxFam)
    (kbw_bxp_half_supplied hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV
      hseed h2box hband hrefl 2 (by norm_num))
    hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold






theorem kbw_criticalProbability_le_half_square_faithful
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1))) :
    criticalProbability 2 ≤ 1 / 2 := by
  let boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2))) := fun n =>
    horizontalCrossingEvent 0 ((n + 1 : ℕ) : ℤ) 0 ((n + 1 : ℕ) : ℤ)
  have hbalance : ∀ n : ℕ, (1 : ℝ) / 2 ≤ halfMeasure.real (boxFam n) := by
    intro n
    have hn : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by positivity
    exact crr_square_half ((n + 1 : ℕ) : ℤ) hn
      (hmeasGenH _ _ hn hn) (hmeasFace _ hn) (hmeasThin _ hn)
  by_contra hgt
  rw [not_le] at hgt
  have hlt : ((2⁻¹ : ℝ≥0) : ℝ) < criticalProbability 2 := by
    norm_num
    exact hgt
  have hT := (TwoDim.kcd_horizontal_sharpThreshold
    (2⁻¹ : ℝ≥0) half_le_one hlt).comp (tendsto_add_atTop_nat 1)
  have hlimge : (1 / 2 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hT
      (Filter.Eventually.of_forall hbalance)
  norm_num at hlimge







theorem kbw_kesten_square_faithful
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent (-1) n 0 (n - 1)))
    (h2box : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 8 ≤ rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    : criticalProbability 2 = 1 / 2 := by
  have hbxp : BoxCrossingProperty halfMeasure 2 :=
    kbw_bxp_half_faithful hpa hmeasGenH hmeasGenV hmeasFace hmeasThin h2box
      2 (by norm_num)
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical (hCorLowerBound hbxp)
  have hle : criticalProbability 2 ≤ (1 : ℝ) / 2 :=
    kbw_criticalProbability_le_half_square_faithful hmeasGenH hmeasFace hmeasThin
  linarith





theorem kbw_kesten_no_percolation_supplied
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hpa : PositivelyAssociated rba_selfDualMeasure)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hmeas2box : ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hmeasband : ∀ n : ℤ, 0 < n →
      MeasurableSet (verticalCrossingEvent 0 n 0 n))
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (horizontalCrossingEvent 0 a 0 b))
    (hmeasGenV : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (verticalCrossingEvent 0 a 0 b))
    (hseed : ∀ n : ℤ, 0 < n → β ≤ rai_cross rba_selfDualMeasure n 1)
    (h2box : ∀ n : ℤ, 0 < n →
      γ ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) 0 n))
    (hband : ∀ n : ℤ, 0 < n →
      (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n))
    (hrefl : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n))
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 ∧
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
  have hbxp : BoxCrossingProperty halfMeasure 2 :=
    kbw_bxp_half_supplied hpa hβ hγ hmeas2box hmeasband hmeasGenH hmeasGenV
      hseed h2box hband hrefl 2 (by norm_num)
  exact kesten_no_percolation_at_pc (ρ := 2) (R := R) (boxFam := boxFam)
    hbxp hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold

end Universality

end StatMech
