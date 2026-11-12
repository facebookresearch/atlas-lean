/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.RSW.Defs
import Code.Universality.Defs
import Code.Universality.BXPTransfer
import Code.Universality.RSWStrip
import Code.Universality.KestenHalf

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim



























theorem ka_rsw_strip_glue_extend
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d)
    {cL cV cR : ℝ}
    (hL : cL ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d))
    (hV : cV ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent m m' c d))
    (hR : cR ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent m b c d))
    (hcV0 : 0 ≤ cV) (hcR0 : 0 ≤ cR) :
    cL * cV * cR ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a b c d) := by
  have hglue := StatMech.Lattice.jec_rsw_strip_glue μ hpa ham hmm' hm'b hamL hmbR hcd
  have h1 : (0 : ℝ) ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d) :=
    measureReal_nonneg
  calc cL * cV * cR
      ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a m' c d)
          * μ.real (StatMech.RSW.Box.verticalCrossingEvent m m' c d)
          * μ.real (StatMech.RSW.Box.horizontalCrossingEvent m b c d) := by
        apply mul_le_mul
        · exact mul_le_mul hL hV hcV0 h1
        · exact hR
        · exact hcR0
        · positivity
    _ ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent a b c d) := hglue











theorem ka_wide_box_extend
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) {n : ℤ} (hn : 0 < n) {cW cS : ℝ}
    (hcW0 : 0 ≤ cW) (hcS0 : 0 ≤ cS)
    (hW1 : cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (2 * n) 0 n))
    (hW2 : cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent n (3 * n) 0 n))
    (hS : cS ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent n (2 * n) 0 n)) :
    cW * cS * cW ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (3 * n) 0 n) :=
  ka_rsw_strip_glue_extend μ hpa (a := 0) (m := n) (m' := 2 * n) (b := 3 * n) (c := 0) (d := n)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    hW1 hS hW2 hcS0 hcW0











theorem ka_floor_two_mul (n : ℕ) : ⌊(2 : ℝ) * (n : ℝ)⌋ = (2 * n : ℤ) := by
  rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast]










theorem ka_bxp_of_box_seed (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c)
    (hH : ∀ (n : ℕ) (τ : Site 2),
        c ≤ μ.real (translatedHorizontalCrossingEvent τ (2 * (n : ℤ)) (n : ℤ)))
    (hV : ∀ (n : ℕ) (τ : Site 2),
        c ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) (2 * (n : ℤ)))) :
    BoxCrossingProperty μ 2 := by
  refine ⟨by norm_num, 0, ?_⟩
  unfold boxCrossingInf
  refine lt_of_lt_of_le hc (le_csInf (boxCrossingProbabilities_nonempty μ 2 0) ?_)
  rintro x ⟨n, τ, _hn, rfl | rfl⟩
  · rw [ka_floor_two_mul n]; exact hH n τ
  · rw [ka_floor_two_mul n]; exact hV n τ






















structure KaSelfDualBoxSeed (μ : Measure (ConfigSpace (Sym2 (Site 2)))) where
  
  c : ℝ
  
  c_pos : 0 < c
  

  wide : ∀ n : ℕ, c ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (2 * (n : ℤ)) 0 (n : ℤ))
  

  tall : ∀ n : ℕ, c ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent 0 (n : ℤ) 0 (2 * (n : ℤ)))







structure KaCrossingTranslationInvariant
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) : Prop where
  
  horiz : ∀ (τ : Site 2) (a b : ℤ),
    μ.real (translatedHorizontalCrossingEvent τ a b)
      = μ.real (TwoDim.horizontalCrossingEvent a b)
  
  vert : ∀ (τ : Site 2) (a b : ℤ),
    μ.real (translatedVerticalCrossingEvent τ a b)
      = μ.real (TwoDim.verticalCrossingEvent a b)




theorem ka_twoDim_horizontalCrossingEvent_eq (a b : ℤ) :
    TwoDim.horizontalCrossingEvent a b
      = StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b := by
  ext ω
  rw [TwoDim.mem_horizontalCrossingEvent, StatMech.RSW.Box.mem_horizontalCrossingEvent,
    StatMech.RSW.Box.horizontalCrossing_eq_twoDim]




theorem ka_twoDim_verticalCrossingEvent_eq (a b : ℤ) :
    TwoDim.verticalCrossingEvent a b
      = StatMech.RSW.Box.verticalCrossingEvent 0 a 0 b := rfl




















theorem ka_bxp_half_of_rsw
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure) :
    BoxCrossingProperty halfMeasure 2 := by
  refine ka_bxp_of_box_seed halfMeasure hseed.c_pos ?_ ?_
  · intro n τ
    rw [htinv.horiz τ (2 * (n : ℤ)) (n : ℤ),
      ka_twoDim_horizontalCrossingEvent_eq (2 * (n : ℤ)) (n : ℤ)]
    exact hseed.wide n
  · intro n τ
    rw [htinv.vert τ (n : ℤ) (2 * (n : ℤ)),
      ka_twoDim_verticalCrossingEvent_eq (n : ℤ) (2 * (n : ℤ))]
    exact hseed.tall n





























theorem ka_kesten_pc_eq_half
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure)
    
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 :=
  kesten_pc_eq_half_of_bxp (ρ := 2) (R := R) (boxFam := boxFam)
    (ka_bxp_half_of_rsw hseed htinv) hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold






theorem ka_kesten_no_percolation_at_pc
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hseed : KaSelfDualBoxSeed halfMeasure)
    (htinv : KaCrossingTranslationInvariant halfMeasure)
    (hCorLowerBound : BoxCrossingProperty halfMeasure 2 →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 ∧
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  ⟨ka_kesten_pc_eq_half hseed htinv hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold,
    hCorLowerBound (ka_bxp_half_of_rsw hseed htinv)⟩

end Universality

end StatMech
