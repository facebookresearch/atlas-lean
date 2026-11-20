/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Ising.InfiniteVolume
import Code.Ising.AeTailInvariantClose
import Code.FK.FKErgodicFull

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}







noncomputable def pst_plusShiftedFinite (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  (plusMeasure d n β h).map (continuous_shift g).measurable.aemeasurable


noncomputable def pst_minusShiftedFinite (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ) :
    ProbabilityMeasure (ConfigSpace (Site d)) :=
  (minusMeasure d n β h).map (continuous_shift g).measurable.aemeasurable










theorem pst_integral_plusShifted (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    (∫ x, f x ∂((pst_plusShiftedFinite β h g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((plusMeasure d n β h : ProbabilityMeasure _) : Measure _) := by
  unfold pst_plusShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]


theorem pst_integral_minusShifted (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    (∫ x, f x ∂((pst_minusShiftedFinite β h g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((minusMeasure d n β h : ProbabilityMeasure _) : Measure _) := by
  unfold pst_minusShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]














def pst_PlusIntegralShiftDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : ConfigSpace (Site d) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)



def pst_MinusIntegralShiftDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : ConfigSpace (Site d) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)










theorem pst_plusShifted_weakConverges_of_decay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hdecay : pst_PlusIntegralShiftDecay β h g φ) :
    WeakConvergesTo (fun n => pst_plusShiftedFinite β h g (φ n)) (plusState d β h) := by
  apply weakConvergesTo_of_forall_tendsto_integral
  intro f
  have hcentred := hconv.tendsto_integral f
  have key :
      Tendsto (fun n => ∫ x, f (shift g x)
          ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) atTop
        (𝓝 (∫ x, f x ∂((plusState d β h : ProbabilityMeasure _) : Measure _))) := by
    have hsub := hcentred.sub (hdecay f)
    simp only [sub_zero] at hsub
    exact hsub.congr (fun n => by ring)
  exact key.congr (fun n => (pst_integral_plusShifted β h g (φ n) f).symm)


theorem pst_minusShifted_weakConverges_of_decay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h))
    (hdecay : pst_MinusIntegralShiftDecay β h g φ) :
    WeakConvergesTo (fun n => pst_minusShiftedFinite β h g (φ n)) (minusState d β h) := by
  apply weakConvergesTo_of_forall_tendsto_integral
  intro f
  have hcentred := hconv.tendsto_integral f
  have key :
      Tendsto (fun n => ∫ x, f (shift g x)
          ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) atTop
        (𝓝 (∫ x, f x ∂((minusState d β h : ProbabilityMeasure _) : Measure _))) := by
    have hsub := hcentred.sub (hdecay f)
    simp only [sub_zero] at hsub
    exact hsub.congr (fun n => by ring)
  exact key.congr (fun n => (pst_integral_minusShifted β h g (φ n) f).symm)













theorem pst_plusState_map_shift_of_decay (β h : ℝ) (g : Multiplicative (Site d))
    (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pst_PlusIntegralShiftDecay β h g φ) :
    Measure.map (shift g) (plusState d β h : Measure (ConfigSpace (Site d)))
      = (plusState d β h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β h
  exact StatMech.FK.erg_measure_map_eq_of_translated_converges
    (fun n => plusMeasure d (φ n) β h) (plusState d β h) (continuous_shift g) hconv
    (pst_plusShifted_weakConverges_of_decay β h g φ hconv (hdecay φ hφ hconv))



theorem pst_minusState_map_shift_of_decay (β h : ℝ) (g : Multiplicative (Site d))
    (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pst_MinusIntegralShiftDecay β h g φ) :
    Measure.map (shift g) (minusState d β h : Measure (ConfigSpace (Site d)))
      = (minusState d β h : Measure (ConfigSpace (Site d))) := by
  obtain ⟨φ, hφ, hconv⟩ := minusState_isInfiniteVolumeState d β h
  exact StatMech.FK.erg_measure_map_eq_of_translated_converges
    (fun n => minusMeasure d (φ n) β h) (minusState d β h) (continuous_shift g) hconv
    (pst_minusShifted_weakConverges_of_decay β h g φ hconv (hdecay φ hφ hconv))













theorem pst_plusState_isTranslationInvariant_of_decay (β h : ℝ)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pst_PlusIntegralShiftDecay β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) := by
  intro g
  exact ⟨measurable_shift g, pst_plusState_map_shift_of_decay β h g (hdecay g)⟩




theorem pst_minusState_isTranslationInvariant_of_decay (β h : ℝ)
    (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pst_MinusIntegralShiftDecay β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) := by
  intro g
  exact ⟨measurable_shift g, pst_minusState_map_shift_of_decay β h g (hdecay g)⟩


























theorem pst_plusIntegralShiftDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    pst_PlusIntegralShiftDecay β h (1 : Multiplicative (Site d)) φ := by
  intro f
  have h0 : (fun n =>
      (∫ x, f x ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
        - (∫ x, f (shift (1 : Multiplicative (Site d)) x)
            ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))) = fun _ => 0 := by
    funext n
    simp only [shift_one, id]
    ring
  rw [h0]
  exact tendsto_const_nhds



theorem pst_minusIntegralShiftDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    pst_MinusIntegralShiftDecay β h (1 : Multiplicative (Site d)) φ := by
  intro f
  have h0 : (fun n =>
      (∫ x, f x ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
        - (∫ x, f (shift (1 : Multiplicative (Site d)) x)
            ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))) = fun _ => 0 := by
    funext n
    simp only [shift_one, id]
    ring
  rw [h0]
  exact tendsto_const_nhds

end Ising

end StatMech
