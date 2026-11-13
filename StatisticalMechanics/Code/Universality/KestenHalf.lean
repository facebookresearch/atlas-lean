/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.Universality.Defs
import Code.Universality.G3PercDualityFull

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim








noncomputable def halfMeasure : Measure (ConfigSpace (Sym2 (Site 2))) :=
  bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one

instance instIsProbabilityMeasure_halfMeasure : IsProbabilityMeasure halfMeasure := by
  unfold halfMeasure; infer_instance




theorem halfMeasure_eq :
    halfMeasure = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := rfl





theorem measurable_dualConfig :
    Measurable (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
  rw [dualConfig_eq_comp]
  exact measurable_complement.comp measurable_reindex






theorem dualConfig_preserves_half :
    Measure.map dualConfig halfMeasure = halfMeasure :=
  bernoulliProductMeasure_selfDual_half
























theorem selfDualRotation_preserves_half
    (R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure) :
    Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure := by
  rw [← Measure.map_map hRmeas measurable_dualConfig, dualConfig_preserves_half, hRpres]












theorem half_crossingProb_of_selfDual_dichotomy
    {H : Set (ConfigSpace (Sym2 (Site 2)))} (hHm : MeasurableSet H)
    {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : Hᶜ = (R ∘ dualConfig) ⁻¹' H) :
    halfMeasure.real H = 1 / 2 := by
  have hSmeas : Measurable (R ∘ dualConfig) := hRmeas.comp measurable_dualConfig
  have hSpres : Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure :=
    selfDualRotation_preserves_half R hRmeas hRpres
  
  have hpre : halfMeasure.real ((R ∘ dualConfig) ⁻¹' H) = halfMeasure.real H := by
    have h1 : halfMeasure ((R ∘ dualConfig) ⁻¹' H) = halfMeasure H := by
      rw [← Measure.map_apply hSmeas hHm, hSpres]
    unfold Measure.real; rw [h1]
  
  rw [← hdich, measureReal_compl hHm, probReal_univ] at hpre
  linarith










theorem percolationProbability_congr {d : ℕ} {p q : ℝ≥0}
    (hp : p ≤ 1) (hq : q ≤ 1) (h : p = q) :
    percolationProbability d p hp = percolationProbability d q hq := by
  subst h; rfl




theorem subcriticalDensities_bddAbove (d : ℕ) : BddAbove (subcriticalDensities d) :=
  ⟨1, by rintro p ⟨_, hp1, _⟩; exact hp1⟩



theorem half_mem_subcriticalDensities
    (h : percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
    ((1 : ℝ) / 2) ∈ subcriticalDensities 2 := by
  have hp0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hp1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
  refine ⟨hp0, hp1, ?_⟩
  rw [percolationProbability_congr (by exact_mod_cast hp1) half_le_one
    (show (⟨(1 : ℝ) / 2, hp0⟩ : ℝ≥0) = (2⁻¹ : ℝ≥0) by
      apply NNReal.coe_injective
      show (1 : ℝ) / 2 = ((2⁻¹ : ℝ≥0) : ℝ)
      rw [NNReal.coe_inv]; norm_num)]
  exact h





theorem half_le_criticalProbability_of_subcritical
    (h : percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0) :
    (1 : ℝ) / 2 ≤ criticalProbability 2 := by
  unfold criticalProbability
  exact le_csSup (subcriticalDensities_bddAbove 2) (half_mem_subcriticalDensities h)























theorem criticalProbability_le_half_of_sharpThreshold
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0))
    (hbalance : ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2) :
    criticalProbability 2 ≤ (1 : ℝ) / 2 := by
  by_contra hgt
  rw [not_le] at hgt
  
  have hlt : ((2⁻¹ : ℝ≥0) : ℝ) < criticalProbability 2 := by
    have hc : ((2⁻¹ : ℝ≥0) : ℝ) = 1 / 2 := by rw [NNReal.coe_inv]; norm_num
    rw [hc]; exact hgt
  have hT := hSharpThreshold (2⁻¹ : ℝ≥0) half_le_one hlt
  
  have hconst : (fun n => (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one).real (boxFam n))
      = fun _ => (1 : ℝ) / 2 := funext hbalance
  rw [hconst] at hT
  have hcontra := tendsto_nhds_unique hT tendsto_const_nhds
  norm_num at hcontra






































theorem kesten_pc_eq_half_of_bxp
    {ρ : ℝ} {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    
    (hbxp : BoxCrossingProperty halfMeasure ρ)
    
    (hCorLowerBound : BoxCrossingProperty halfMeasure ρ →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 := by
  
  have hbalance : ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := fun n =>
    half_crossingProb_of_selfDual_dichotomy (hHm n) hRmeas hRpres (hdich n)
  
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical (hCorLowerBound hbxp)
  have hle : criticalProbability 2 ≤ (1 : ℝ) / 2 :=
    criticalProbability_le_half_of_sharpThreshold hSharpThreshold hbalance
  linarith






theorem kesten_no_percolation_at_pc
    {ρ : ℝ} {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
    {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
    (hbxp : BoxCrossingProperty halfMeasure ρ)
    (hCorLowerBound : BoxCrossingProperty halfMeasure ρ →
        percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0)
    (hHm : ∀ n, MeasurableSet (boxFam n))
    (hRmeas : Measurable R) (hRpres : Measure.map R halfMeasure = halfMeasure)
    (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n))
    (hSharpThreshold : ∀ (p : ℝ≥0) (hp : p ≤ 1), (p : ℝ) < criticalProbability 2 →
        Tendsto (fun n => (bernoulliProductMeasure p hp).real (boxFam n)) atTop (𝓝 0)) :
    criticalProbability 2 = 1 / 2 ∧
      percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 :=
  ⟨kesten_pc_eq_half_of_bxp hbxp hCorLowerBound hHm hRmeas hRpres hdich hSharpThreshold,
    hCorLowerBound hbxp⟩

end Universality

end StatMech
