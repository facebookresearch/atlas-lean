/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FK.Ergodicity
import Code.Probability.InfiniteHarris
import Code.Universality.BXPAspectTransfer
import Code.Universality.RSWLowestCrossing

open MeasureTheory Set Filter
open scoped ENNReal NNReal symmDiff

namespace StatMech
namespace Universality

open StatMech.Lattice
open StatMech.Percolation
open StatMech.RSW.Box
open StatMech.RSW.Strip






def FiniteCylinderPositivelyAssociated {E : Type*}
    (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (A B : Set (ConfigSpace E)), IsIncreasing A → IsIncreasing B →
    ∀ (F G : Finset E),
      _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E) →
      _root_.DependsOn (B.indicator (fun _ => (1 : ℝ))) (G : Set E) →
      μ.real A * μ.real B ≤ μ.real (A ∩ B)



theorem bernoulli_finiteCylinderPositivelyAssociated
    {E : Type*} [Countable E]
    (p : ℝ≥0) (hp : p ≤ 1) :
    FiniteCylinderPositivelyAssociated
      (bernoulliProductMeasure (E := E) p hp) := by
  classical
  intro A B hA hB F G hAF hBG
  let K := F ∪ G
  apply ih_harris_of_finite_dependsOn hp K
  · apply ih_event_dependsOn_of_indicator
    exact hAF.mono (by simp [K])
  · apply ih_event_dependsOn_of_indicator
    exact hBG.mono (by simp [K])
  · exact hA
  · exact hB



theorem rba_selfDualMeasure_finiteCylinderPositivelyAssociated :
    FiniteCylinderPositivelyAssociated rba_selfDualMeasure := by
  simpa only [rba_selfDualMeasure] using
    (bernoulli_finiteCylinderPositivelyAssociated
      (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one)



theorem FiniteCylinderPositivelyAssociated.triple
    {E : Type*} {μ : Measure (ConfigSpace E)}
    (hpa : FiniteCylinderPositivelyAssociated μ)
    {A B C : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) (hC : IsIncreasing C)
    (F G K : Finset E)
    (hAF : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E))
    (hBG : _root_.DependsOn (B.indicator (fun _ => (1 : ℝ))) (G : Set E))
    (hCK : _root_.DependsOn (C.indicator (fun _ => (1 : ℝ))) (K : Set E)) :
    μ.real A * μ.real B * μ.real C ≤ μ.real (A ∩ B ∩ C) := by
  classical
  have hAB : μ.real A * μ.real B ≤ μ.real (A ∩ B) :=
    hpa A B hA hB F G hAF hBG
  have hABdep : _root_.DependsOn
      ((A ∩ B).indicator (fun _ => (1 : ℝ)))
      ((F ∪ G : Finset E) : Set E) := by
    simpa only [Finset.coe_union] using dependsOn_inter hAF hBG
  have hABC : μ.real (A ∩ B) * μ.real C ≤
      μ.real (A ∩ B ∩ C) :=
    hpa (A ∩ B) C (hA.inter hB) hC (F ∪ G) K hABdep hCK
  exact (mul_le_mul_of_nonneg_right hAB measureReal_nonneg).trans hABC







theorem rba_horizontal_strip_glue
    {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d) :
    rba_selfDualMeasure.real (horizontalCrossingEvent a m' c d)
        * rba_selfDualMeasure.real (verticalCrossingEvent m m' c d)
        * rba_selfDualMeasure.real (horizontalCrossingEvent m b c d)
      ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
  let A := horizontalCrossingEvent a m' c d
  let B := verticalCrossingEvent m m' c d
  let C := horizontalCrossingEvent m b c d
  let FA := edgesWithinFinset (rect_finite a m' c d).toFinset
  let FB := edgesWithinFinset (rect_finite m m' c d).toFinset
  let FC := edgesWithinFinset (rect_finite m b c d).toFinset
  have hfkg : rba_selfDualMeasure.real A * rba_selfDualMeasure.real B *
      rba_selfDualMeasure.real C ≤ rba_selfDualMeasure.real (A ∩ B ∩ C) :=
    rba_selfDualMeasure_finiteCylinderPositivelyAssociated.triple
      (horizontalCrossingEvent_isIncreasing a m' c d)
      (verticalCrossingEvent_isIncreasing m m' c d)
      (horizontalCrossingEvent_isIncreasing m b c d)
      FA FB FC
      (by simpa [A, FA] using rlc_horizontalCrossing_dependsOn a m' c d)
      (by simpa [B, FB] using rlc_verticalCrossing_dependsOn m m' c d)
      (by simpa [C, FC] using rlc_horizontalCrossing_dependsOn m b c d)
  have hsub : A ∩ B ∩ C ⊆ horizontalCrossingEvent a b c d := by
    rintro omega ⟨⟨hL, hV⟩, hR⟩
    exact vsFix_hvIntersection omega ham hmm' hm'b
      (vsFix_arc_sides_imp omega a m' m m' c d
        (jec_vsFix_arc_sides omega hamL hcd))
      (vsFix_arc_sides_imp omega m b m m' c d
        (jec_vsFix_arc_sides omega hmbR hcd))
      hL hV hR
  exact hfkg.trans (measureReal_mono hsub)



theorem rba_vertical_strip_glue
    {a b c m m' d : ℤ}
    (hab : a ≤ b) (hcm : c ≤ m) (hmm' : m ≤ m')
    (hm'd : m' ≤ d) (hcm' : c < m') (hmd : m < d) :
    rba_selfDualMeasure.real (verticalCrossingEvent a b c m')
        * rba_selfDualMeasure.real (horizontalCrossingEvent a b m m')
        * rba_selfDualMeasure.real (verticalCrossingEvent a b m d)
      ≤ rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
  let A := verticalCrossingEvent a b c m'
  let B := horizontalCrossingEvent a b m m'
  let C := verticalCrossingEvent a b m d
  let FA := edgesWithinFinset (rect_finite a b c m').toFinset
  let FB := edgesWithinFinset (rect_finite a b m m').toFinset
  let FC := edgesWithinFinset (rect_finite a b m d).toFinset
  have hfkg : rba_selfDualMeasure.real A * rba_selfDualMeasure.real B *
      rba_selfDualMeasure.real C ≤ rba_selfDualMeasure.real (A ∩ B ∩ C) :=
    rba_selfDualMeasure_finiteCylinderPositivelyAssociated.triple
      (verticalCrossingEvent_isIncreasing a b c m')
      (horizontalCrossingEvent_isIncreasing a b m m')
      (verticalCrossingEvent_isIncreasing a b m d)
      FA FB FC
      (by simpa [A, FA] using rlc_verticalCrossing_dependsOn a b c m')
      (by simpa [B, FB] using rlc_horizontalCrossing_dependsOn a b m m')
      (by simpa [C, FC] using rlc_verticalCrossing_dependsOn a b m d)
  have hsub : A ∩ B ∩ C ⊆ verticalCrossingEvent a b c d := by
    rintro omega ⟨⟨hV1, hH⟩, hV2⟩
    exact bat_verticalIntersection omega hab hcm hmm' hm'd hcm' hmd hV1 hH hV2
  exact hfkg.trans (measureReal_mono hsub)





def MeasurablyPositivelyAssociated {E : Type*}
    (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A B : Set (ConfigSpace E), MeasurableSet A → MeasurableSet B →
    IsIncreasing A → IsIncreasing B →
      μ.real A * μ.real B ≤ μ.real (A ∩ B)




def HasIncreasingCylinderApproximation {E : Type*}
    (μ : Measure (ConfigSpace E)) (A : Set (ConfigSpace E)) : Prop :=
  ∃ C : ℕ → Set (ConfigSpace E),
    (∀ n, MeasurableSet (C n)) ∧
    (∀ n, IsIncreasing (C n)) ∧
    (∀ n, ∃ F : Finset E,
      _root_.DependsOn ((C n).indicator (fun _ => (1 : ℝ))) (F : Set E)) ∧
    Tendsto (fun n => μ.real (C n ∆ A)) atTop (nhds 0)




theorem measurablyPositivelyAssociated_of_increasingCylinderApproximation
    {E : Type*} {μ : Measure (ConfigSpace E)} [IsFiniteMeasure μ]
    (hcyl : FiniteCylinderPositivelyAssociated μ)
    (happrox : ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A →
      HasIncreasingCylinderApproximation μ A) :
    MeasurablyPositivelyAssociated μ := by
  intro A B hAm hBm hA hB
  obtain ⟨C, hCm, hCi, hCdep, hCt⟩ := happrox A hAm hA
  obtain ⟨D, hDm, hDi, hDdep, hDt⟩ := happrox B hBm hB
  have hCprob : Tendsto (fun n => μ.real (C n)) atTop (nhds (μ.real A)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hCt
    intro n
    simpa only [Real.dist_eq] using
      (abs_measureReal_sub_le_measureReal_symmDiff
        (hCm n).nullMeasurableSet hAm.nullMeasurableSet)
  have hDprob : Tendsto (fun n => μ.real (D n)) atTop (nhds (μ.real B)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hDt
    intro n
    simpa only [Real.dist_eq] using
      (abs_measureReal_sub_le_measureReal_symmDiff
        (hDm n).nullMeasurableSet hBm.nullMeasurableSet)
  have hInterDiff : Tendsto
      (fun n => μ.real ((C n ∩ D n) ∆ (A ∩ B)))
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _
      (by simpa using hCt.add hDt)
    intro n
    calc
      μ.real ((C n ∩ D n) ∆ (A ∩ B))
          ≤ μ.real ((C n ∆ A) ∪ (D n ∆ B)) := by
            apply measureReal_mono _ (measure_ne_top _ _)
            intro omega homega
            simp only [mem_symmDiff, mem_inter_iff, mem_union] at homega ⊢
            tauto
      _ ≤ μ.real (C n ∆ A) + μ.real (D n ∆ B) :=
        measureReal_union_le _ _
  have hInterProb : Tendsto (fun n => μ.real (C n ∩ D n)) atTop
      (nhds (μ.real (A ∩ B))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hInterDiff
    intro n
    simpa only [Real.dist_eq] using
      (abs_measureReal_sub_le_measureReal_symmDiff
        ((hCm n).inter (hDm n)).nullMeasurableSet
        (hAm.inter hBm).nullMeasurableSet)
  have hstage : ∀ n,
      μ.real (C n) * μ.real (D n) ≤ μ.real (C n ∩ D n) := by
    intro n
    obtain ⟨F, hF⟩ := hCdep n
    obtain ⟨G, hG⟩ := hDdep n
    exact hcyl (C n) (D n) (hCi n) (hDi n) F G hF hG
  exact le_of_tendsto_of_tendsto (hCprob.mul hDprob) hInterProb
    (Eventually.of_forall hstage)





theorem positivelyAssociated_of_measurablyPositivelyAssociated
    {E : Type*} {μ : Measure (ConfigSpace E)}
    (hpa : MeasurablyPositivelyAssociated μ)
    (hmeas : ∀ A : Set (ConfigSpace E), IsIncreasing A → MeasurableSet A) :
    PositivelyAssociated μ := by
  intro A B hA hB
  exact hpa A B (hmeas A hA) (hmeas B hB) hA hB





theorem bernoulli_exists_cylinder_symmDiff_lt
    {E : Type*} [Countable E]
    (p : ℝ≥0) (hp : p ≤ 1) {A : Set (ConfigSpace E)}
    (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C ∈ measurableCylinders (fun _ : E => Bool),
      bernoulliProductMeasure (E := E) p hp (C ∆ A) < ε :=
  FK.exists_cylinder_symmDiff_lt p hp hA hε

end Universality
end StatMech
