/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.FunctionalBKRGeneralProductApprox

open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal

namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]

theorem tendsto_min_natCast (r : ℝ) :
    Tendsto (fun n : ℕ => min r n) atTop (𝓝 (r)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge r
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [min_eq_left]
  exact hN.trans (by exact_mod_cast hn)

theorem tendsto_lintegral_of_monotone_ae
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (u : ℕ → X → ℝ≥0∞) (v : X → ℝ≥0∞)
    (hu : ∀ n, Measurable (u n)) (hmono : ∀ x, Monotone fun n => u n x)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto (fun n => ∫⁻ x, u n x ∂mu) atTop (𝓝 (∫⁻ x, v x ∂mu)) := by
  have hsup : ∀ᵐ x ∂mu, (⨆ n, u n x) = v x := by
    filter_upwards [hlim] with x hx
    exact tendsto_nhds_unique (tendsto_atTop_iSup (hmono x)) hx
  have hint : (∫⁻ x, v x ∂mu) = ⨆ n, ∫⁻ x, u n x ∂mu := by
    calc
      (∫⁻ x, v x ∂mu) = ∫⁻ x, ⨆ n, u n x ∂mu :=
        lintegral_congr_ae <| by
          filter_upwards [hsup] with x hx
          exact hx.symm
      _ = ⨆ n, ∫⁻ x, u n x ∂mu := lintegral_iSup hu (fun n m hnm x => hmono x hnm)
  rw [hint]
  exact tendsto_atTop_iSup fun n m hnm =>
    lintegral_mono fun x => hmono x hnm

theorem measurableFamilyBKR_and_dual
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : Set E → (∀ e, S e) → ℝ)
    (hFm : ∀ K, Measurable (F K)) (hGm : ∀ K, Measurable (G K))
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hFdep : ∀ K, PiDependsOn K (F K))
    (hGdep : ∀ K, PiDependsOn K (G K)) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)
          ∂Measure.pi mu := by
  let Ft : ℕ → Set E → (∀ e, S e) → ℝ := fun n K x => min (F K x) n
  let Gt : ℕ → Set E → (∀ e, S e) → ℝ := fun n K x => min (G K x) n
  have hFtm : ∀ n K, Measurable (Ft n K) := fun n K => (hFm K).min measurable_const
  have hGtm : ∀ n K, Measurable (Gt n K) := fun n K => (hGm K).min measurable_const
  have hFt0 : ∀ n K x, 0 ≤ Ft n K x := fun n K x =>
    le_min (hF0 K x) (Nat.cast_nonneg n)
  have hGt0 : ∀ n K x, 0 ≤ Gt n K x := fun n K x =>
    le_min (hG0 K x) (Nat.cast_nonneg n)
  have hFtN : ∀ n K x, Ft n K x ≤ (n : ℝ) := fun n K x => min_le_right _ _
  have hGtN : ∀ n K x, Gt n K x ≤ (n : ℝ) := fun n K x => min_le_right _ _
  have hFtdep : ∀ n K, PiDependsOn K (Ft n K) := by
    intro n K x y hxy
    simp only [Ft]
    rw [hFdep K hxy]
  have hGtdep : ∀ n K, PiDependsOn K (Gt n K) := by
    intro n K x y hxy
    simp only [Gt]
    rw [hGdep K hxy]
  have hbounded : ∀ n,
      (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax (Ft n) (Gt n) x)
          ∂Measure.pi mu) ≤
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Ft n) x)
            ∂Measure.pi mu) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Gt n) x)
            ∂Measure.pi mu ∧
        (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt (Ft n) (Gt n) p.1 p.2)
            ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
          ∫⁻ x, ENNReal.ofReal
            (piFunctionalFamilyMax (Ft n) x * piFunctionalFamilyMax (Gt n) x)
            ∂Measure.pi mu := by
    intro n
    exact measurableFamilyBKR_bounded_and_dual mu (Ft n) (Gt n)
      (hFtm n) (hGtm n) (hFt0 n) (hGt0 n) (hFtdep n) (hGtdep n)
      n n (Nat.cast_nonneg n) (Nat.cast_nonneg n) (hFtN n) (hGtN n)
  have hconvF : ∀ K x, Tendsto (fun n => Ft n K x) atTop (𝓝 (F K x)) :=
    fun K x => tendsto_min_natCast (F K x)
  have hconvG : ∀ K x, Tendsto (fun n => Gt n K x) atTop (𝓝 (G K x)) :=
    fun K x => tendsto_min_natCast (G K x)
  have hmonoF : ∀ K x, Monotone fun n => Ft n K x := by
    intro K x n m hnm
    exact min_le_min_left _ (by exact_mod_cast hnm)
  have hmonoG : ∀ K x, Monotone fun n => Gt n K x := by
    intro K x n m hnm
    exact min_le_min_left _ (by exact_mod_cast hnm)
  have hmonoMaxF : ∀ x, Monotone fun n => piFunctionalFamilyMax (Ft n) x := by
    intro x n m hnm
    unfold piFunctionalFamilyMax
    exact Finset.sup'_mono_fun fun K _ => hmonoF K x hnm
  have hmonoMaxG : ∀ x, Monotone fun n => piFunctionalFamilyMax (Gt n) x := by
    intro x n m hnm
    unfold piFunctionalFamilyMax
    exact Finset.sup'_mono_fun fun K _ => hmonoG K x hnm
  have hmonoDisjoint : ∀ x, Monotone fun n =>
      piFunctionalFamilyDisjointMax (Ft n) (Gt n) x := by
    intro x n m hnm
    unfold piFunctionalFamilyDisjointMax piFunctionalFamilyDisjointMaxAt
    apply Finset.sup'_mono_fun
    intro pair _
    exact mul_le_mul (hmonoF pair.1 x hnm) (hmonoG pair.2 x hnm)
      (hGt0 n pair.2 x) (hFt0 m pair.1 x)
  have hmonoDual : ∀ p : (∀ e, S e) × (∀ e, S e), Monotone fun n =>
      piFunctionalFamilyDisjointMaxAt (Ft n) (Gt n) p.1 p.2 := by
    intro p n m hnm
    unfold piFunctionalFamilyDisjointMaxAt
    apply Finset.sup'_mono_fun
    intro pair _
    exact mul_le_mul (hmonoF pair.1 p.1 hnm) (hmonoG pair.2 p.2 hnm)
      (hGt0 n pair.2 p.2) (hFt0 m pair.1 p.1)
  have hmonoSame : ∀ x, Monotone fun n =>
      piFunctionalFamilyMax (Ft n) x * piFunctionalFamilyMax (Gt n) x := by
    intro x n m hnm
    exact mul_le_mul (hmonoMaxF x hnm) (hmonoMaxG x hnm)
      (piFunctionalFamilyMax_nonneg (Gt n) (hGt0 n) x)
      (piFunctionalFamilyMax_nonneg (Ft m) (hFt0 m) x)
  have hlimMaxF : ∀ x, Tendsto (fun n => piFunctionalFamilyMax (Ft n) x) atTop
      (𝓝 (piFunctionalFamilyMax F x)) := fun x =>
    tendsto_piFunctionalFamilyMax Ft F x (fun K => hconvF K x)
  have hlimMaxG : ∀ x, Tendsto (fun n => piFunctionalFamilyMax (Gt n) x) atTop
      (𝓝 (piFunctionalFamilyMax G x)) := fun x =>
    tendsto_piFunctionalFamilyMax Gt G x (fun K => hconvG K x)
  have hlimDisjoint : ∀ x, Tendsto (fun n =>
      piFunctionalFamilyDisjointMax (Ft n) (Gt n) x) atTop
      (𝓝 (piFunctionalFamilyDisjointMax F G x)) := fun x =>
    tendsto_piFunctionalFamilyDisjointMax Ft Gt F G x
      (fun K => hconvF K x) (fun K => hconvG K x)
  have hlimDual : ∀ p : (∀ e, S e) × (∀ e, S e), Tendsto (fun n =>
      piFunctionalFamilyDisjointMaxAt (Ft n) (Gt n) p.1 p.2) atTop
      (𝓝 (piFunctionalFamilyDisjointMaxAt F G p.1 p.2)) := fun p =>
    tendsto_piFunctionalFamilyDisjointMaxAt Ft Gt F G p.1 p.2
      (fun K => hconvF K p.1) (fun K => hconvG K p.2)
  have hlimSame : ∀ x, Tendsto (fun n =>
      piFunctionalFamilyMax (Ft n) x * piFunctionalFamilyMax (Gt n) x) atTop
      (𝓝 (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x)) := fun x =>
    (hlimMaxF x).mul (hlimMaxG x)
  have tMaxF := tendsto_lintegral_of_monotone_ae (Measure.pi mu)
    (fun n x => ENNReal.ofReal (piFunctionalFamilyMax (Ft n) x))
    (fun x => ENNReal.ofReal (piFunctionalFamilyMax F x))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyMax (Ft n) (hFtm n)))
    (fun x n m hnm => ENNReal.ofReal_le_ofReal (hmonoMaxF x hnm))
    (ae_of_all _ fun x => (ENNReal.continuous_ofReal.tendsto _).comp (hlimMaxF x))
  have tMaxG := tendsto_lintegral_of_monotone_ae (Measure.pi mu)
    (fun n x => ENNReal.ofReal (piFunctionalFamilyMax (Gt n) x))
    (fun x => ENNReal.ofReal (piFunctionalFamilyMax G x))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyMax (Gt n) (hGtm n)))
    (fun x n m hnm => ENNReal.ofReal_le_ofReal (hmonoMaxG x hnm))
    (ae_of_all _ fun x => (ENNReal.continuous_ofReal.tendsto _).comp (hlimMaxG x))
  have tDisjoint := tendsto_lintegral_of_monotone_ae (Measure.pi mu)
    (fun n x => ENNReal.ofReal (piFunctionalFamilyDisjointMax (Ft n) (Gt n) x))
    (fun x => ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyDisjointMax (Ft n) (Gt n) (hFtm n) (hGtm n)))
    (fun x n m hnm => ENNReal.ofReal_le_ofReal (hmonoDisjoint x hnm))
    (ae_of_all _ fun x => (ENNReal.continuous_ofReal.tendsto _).comp (hlimDisjoint x))
  have tDual := tendsto_lintegral_of_monotone_ae
    ((Measure.pi mu).prod (Measure.pi mu))
    (fun n p => ENNReal.ofReal
      (piFunctionalFamilyDisjointMaxAt (Ft n) (Gt n) p.1 p.2))
    (fun p => ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G p.1 p.2))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyDisjointMaxAt (Ft n) (Gt n) (hFtm n) (hGtm n)))
    (fun p n m hnm => ENNReal.ofReal_le_ofReal (hmonoDual p hnm))
    (ae_of_all _ fun p => (ENNReal.continuous_ofReal.tendsto _).comp (hlimDual p))
  have tSame := tendsto_lintegral_of_monotone_ae (Measure.pi mu)
    (fun n x => ENNReal.ofReal
      (piFunctionalFamilyMax (Ft n) x * piFunctionalFamilyMax (Gt n) x))
    (fun x => ENNReal.ofReal (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      ((measurable_piFunctionalFamilyMax (Ft n) (hFtm n)).mul
        (measurable_piFunctionalFamilyMax (Gt n) (hGtm n))))
    (fun x n m hnm => ENNReal.ofReal_le_ofReal (hmonoSame x hnm))
    (ae_of_all _ fun x => (ENNReal.continuous_ofReal.tendsto _).comp (hlimSame x))
  constructor
  · let BF : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu
    let BG : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu
    by_cases hbadF : BF = 0 ∧ BG = ∞
    · apply le_of_tendsto tDisjoint
      filter_upwards [] with n
      have hFn : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Ft n) x)
          ∂Measure.pi mu) = 0 := by
        apply nonpos_iff_eq_zero.mp
        calc
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Ft n) x)
              ∂Measure.pi mu) ≤ BF := by
            unfold BF
            apply lintegral_mono
            intro x
            apply ENNReal.ofReal_le_ofReal
            unfold piFunctionalFamilyMax
            apply Finset.sup'_mono_fun
            intro K _
            exact min_le_left _ _
          _ = 0 := hbadF.1
      simpa [hFn, BF, BG, hbadF.1, hbadF.2] using (hbounded n).1
    · by_cases hbadG : BG = 0 ∧ BF = ∞
      · apply le_of_tendsto tDisjoint
        filter_upwards [] with n
        have hGn : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Gt n) x)
            ∂Measure.pi mu) = 0 := by
          apply nonpos_iff_eq_zero.mp
          calc
            (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (Gt n) x)
                ∂Measure.pi mu) ≤ BG := by
              unfold BG
              apply lintegral_mono
              intro x
              apply ENNReal.ofReal_le_ofReal
              unfold piFunctionalFamilyMax
              apply Finset.sup'_mono_fun
              intro K _
              exact min_le_left _ _
            _ = 0 := hbadG.1
        simpa [hGn, BF, BG, hbadG.1, hbadG.2] using (hbounded n).1
      · have hmul := ENNReal.Tendsto.mul tMaxF
          (by by_cases h : BF = 0
              · exact Or.inr (fun ht => hbadF ⟨h, ht⟩)
              · exact Or.inl h)
          tMaxG
          (by by_cases h : BG = 0
              · exact Or.inr (fun ht => hbadG ⟨h, ht⟩)
              · exact Or.inl h)
        exact le_of_tendsto_of_tendsto tDisjoint hmul
          (Eventually.of_forall fun n => (hbounded n).1)
  · exact le_of_tendsto_of_tendsto tDual tSame
      (Eventually.of_forall fun n => (hbounded n).2)



theorem hasMeasurableFunctionalBKR
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)] :
    HasMeasurableFunctionalBKR mu := by
  intro F G hFm hGm hF0 hG0 hFdep hGdep
  exact (measurableFamilyBKR_and_dual mu F G hFm hGm hF0 hG0 hFdep hGdep).1



theorem hasMeasurableDualFunctionalBKR
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)] :
    HasMeasurableDualFunctionalBKR mu := by
  intro F G hFm hGm hF0 hG0 hFdep hGdep
  exact (measurableFamilyBKR_and_dual mu F G hFm hGm hF0 hG0 hFdep hGdep).2



theorem functionalBKR_generalProduct
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax mu f g x)
        ∂Measure.pi mu) ≤
      (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi mu :=
  functionalBKR_generalProduct_of_familyBKR mu
    (hasMeasurableFunctionalBKR mu) f g hf hg hf0 hg0



theorem dualFunctionalBKR_generalProduct
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (f g : (∀ e, S e) → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫⁻ p, ENNReal.ofReal
        (piFunctionalDisjointEssMaxAt mu f g p.1 p.2)
        ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
      ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi mu :=
  dualFunctionalBKR_generalProduct_of_familyBKR mu
    (hasMeasurableDualFunctionalBKR mu) f g hf hg hf0 hg0

end StatMech.FrontierA
