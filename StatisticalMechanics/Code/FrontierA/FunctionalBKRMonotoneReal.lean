/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.FunctionalBKRMonotoneNat
import Mathlib.Data.Finset.Sort

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]




private def layersFrom : ℝ -> List ℝ -> List (ℝ × ℝ)
  | _, [] => []
  | previous, a :: levels => (a, a - previous) :: layersFrom a levels

private theorem layersFrom_map_fst (previous : ℝ) (levels : List ℝ) :
    (layersFrom previous levels).map Prod.fst = levels := by
  induction levels generalizing previous with
  | nil => rfl
  | cons a levels ih => simp [layersFrom, ih]

private theorem fst_mem_of_mem_layersFrom {previous : ℝ} {levels : List ℝ}
    {layer : ℝ × ℝ} (hlayer : layer ∈ layersFrom previous levels) :
    layer.1 ∈ levels := by
  rw [<- layersFrom_map_fst previous levels]
  exact List.mem_map.mpr ⟨layer, hlayer, rfl⟩

private theorem layersFrom_increment_nonneg {previous : ℝ} {levels : List ℝ}
    (hsorted : levels.Pairwise (· < ·))
    (hprevious : ∀ a ∈ levels, previous ≤ a) {layer : ℝ × ℝ}
    (hlayer : layer ∈ layersFrom previous levels) : 0 ≤ layer.2 := by
  induction levels generalizing previous layer with
  | nil => simp [layersFrom] at hlayer
  | cons a levels ih =>
      have hsorted' := List.pairwise_cons.mp hsorted
      simp only [layersFrom, List.mem_cons] at hlayer
      rcases hlayer with rfl | hlayer
      · exact sub_nonneg.mpr (hprevious a (by simp))
      · exact ih hsorted'.2 (fun b hb => (hsorted'.1 b hb).le) hlayer

private theorem layersFrom_sum_eq_of_mem {previous target : ℝ} {levels : List ℝ}
    (hsorted : levels.Pairwise (· < ·))
    (hprevious : ∀ a ∈ levels, previous ≤ a) (hx : target ∈ levels) :
    previous +
        ((layersFrom previous levels).map fun layer =>
          if layer.1 ≤ target then layer.2 else 0).sum = target := by
  induction levels generalizing previous with
  | nil => simp at hx
  | cons a levels ih =>
      have hsorted' := List.pairwise_cons.mp hsorted
      rcases List.mem_cons.mp hx with htarget | hx
      · subst target
        have htail :
            ((layersFrom a levels).map fun layer =>
              if layer.1 ≤ a then layer.2 else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          obtain ⟨layer, hlayer, rfl⟩ := List.mem_map.mp hz
          have hlevel : layer.1 ∈ levels := fst_mem_of_mem_layersFrom hlayer
          simp [not_le_of_gt (hsorted'.1 layer.1 hlevel)]
        simp [layersFrom, htail]
      · have hax : a < target := hsorted'.1 target hx
        have htail := ih hsorted'.2 (fun b hb => (hsorted'.1 b hb).le) hx
        simp only [layersFrom, List.map_cons, List.sum_cons, if_pos hax.le]
        linarith


noncomputable def realValueSet (f : ConfigSpace E -> ℝ) : Finset ℝ :=
  Finset.univ.image f


noncomputable def realLevels (f : ConfigSpace E -> ℝ) : List ℝ :=
  (realValueSet f).sort (· ≤ ·)



noncomputable def realLayers (f : ConfigSpace E -> ℝ) : List (ℝ × ℝ) :=
  layersFrom 0 (realLevels f)


noncomputable def realLayerSet (f : ConfigSpace E -> ℝ) : Finset (ℝ × ℝ) :=
  (realLayers f).toFinset


def realUpperLevel (f : ConfigSpace E -> ℝ) (a : ℝ) : Set (ConfigSpace E) :=
  {omega | a ≤ f omega}

omit [Fintype E] [DecidableEq E] in

theorem realUpperLevel_isIncreasing {f : ConfigSpace E -> ℝ} (hf : Monotone f)
    (a : ℝ) : IsIncreasing (realUpperLevel f a) := by
  intro omega eta homega hlevel
  exact hlevel.trans (hf homega)

private theorem realLayers_nodup (f : ConfigSpace E -> ℝ) :
    (realLayers f).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [realLayers, layersFrom_map_fst]
  exact Finset.sort_nodup _ _

private theorem value_mem_realLevels (f : ConfigSpace E -> ℝ)
    (omega : ConfigSpace E) : f omega ∈ realLevels f := by
  simp [realLevels, realValueSet]

private theorem realLevels_nonneg {f : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) {a : ℝ} (ha : a ∈ realLevels f) : 0 ≤ a := by
  rw [realLevels, Finset.mem_sort] at ha
  obtain ⟨omega, _, rfl⟩ := Finset.mem_image.mp ha
  exact hf omega


theorem realLayer_increment_nonneg {f : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) {layer : ℝ × ℝ}
    (hlayer : layer ∈ realLayerSet f) : 0 ≤ layer.2 := by
  apply layersFrom_increment_nonneg (Finset.sortedLT_sort (realValueSet f)).pairwise
    (fun a ha => realLevels_nonneg hf ha)
  simpa [realLayerSet, realLayers] using hlayer

private theorem real_eq_layer_sum_of_mem {f : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) {x : ℝ} (hx : x ∈ realLevels f) :
    x = ∑ layer ∈ realLayerSet f,
      if layer.1 ≤ x then layer.2 else 0 := by
  have hsum := layersFrom_sum_eq_of_mem
    (Finset.sortedLT_sort (realValueSet f)).pairwise
    (fun a ha => realLevels_nonneg hf ha) hx
  rw [realLayerSet, List.sum_toFinset _ (realLayers_nodup f)]
  simpa [realLayers] using hsum.symm


theorem real_value_eq_layer_sum {f : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) (omega : ConfigSpace E) :
    f omega = ∑ layer ∈ realLayerSet f,
      layer.2 * eventIndicator (realUpperLevel f layer.1) omega := by
  rw [real_eq_layer_sum_of_mem hf (value_mem_realLevels f omega)]
  apply Finset.sum_congr rfl
  intro layer hlayer
  by_cases hlevel : layer.1 ≤ f omega <;>
    simp [realUpperLevel, eventIndicator, hlevel]


theorem cylinderMin_mem_realLevels (f : ConfigSpace E -> ℝ) (K : Set E)
    (omega : ConfigSpace E) : cylinderMin f K omega ∈ realLevels f := by
  obtain ⟨eta, heta, heq⟩ := Finset.exists_mem_eq_inf'
    (agreementFiber_nonempty K omega) f
  rw [cylinderMin, heq]
  simp [realLevels, realValueSet]



theorem occursOn_realUpperLevel_iff (f : ConfigSpace E -> ℝ) (a : ℝ)
    (K : Set E) (omega : ConfigSpace E) :
    OccursOn (realUpperLevel f a) K omega ↔ a ≤ cylinderMin f K omega := by
  unfold OccursOn realUpperLevel cylinderMin
  rw [Finset.le_inf'_iff]
  constructor
  · intro h eta heta
    exact h eta (mem_agreementFiber.mp heta)
  · intro h eta hagree
    exact h eta (mem_agreementFiber.mpr hagree)

theorem cylinderMin_eq_layer_sum {f : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) (K : Set E) (omega : ConfigSpace E) :
    cylinderMin f K omega = ∑ layer ∈ realLayerSet f,
      if layer.1 ≤ cylinderMin f K omega then layer.2 else 0 :=
  real_eq_layer_sum_of_mem hf (cylinderMin_mem_realLevels f K omega)

omit [Fintype E] [DecidableEq E] in
private theorem eventIndicator_nonneg (A : Set (ConfigSpace E))
    (omega : ConfigSpace E) : 0 ≤ eventIndicator A omega := by
  unfold eventIndicator
  exact Set.indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) omega





theorem cylinderMin_mul_le_realLevelBoxes {f g : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) (hg : ∀ omega, 0 ≤ g omega)
    (K L : Set E) (hKL : Disjoint K L) (omega : ConfigSpace E) :
    cylinderMin f K omega * cylinderMin g L omega ≤
      ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
        layerF.2 * layerG.2 *
          eventIndicator
            (disjointOccurrence (realUpperLevel f layerF.1)
              (realUpperLevel g layerG.1)) omega := by
  rw [cylinderMin_eq_layer_sum hf, cylinderMin_eq_layer_sum hg,
    Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro layerF hlayerF
  apply Finset.sum_le_sum
  intro layerG hlayerG
  by_cases hF : layerF.1 ≤ cylinderMin f K omega <;>
    by_cases hG : layerG.1 ≤ cylinderMin g L omega
  · have hoccF : OccursOn (realUpperLevel f layerF.1) K omega :=
      (occursOn_realUpperLevel_iff f layerF.1 K omega).mpr hF
    have hoccG : OccursOn (realUpperLevel g layerG.1) L omega :=
      (occursOn_realUpperLevel_iff g layerG.1 L omega).mpr hG
    have hbox : omega ∈ disjointOccurrence (realUpperLevel f layerF.1)
        (realUpperLevel g layerG.1) := ⟨K, L, hKL, hoccF, hoccG⟩
    simp [hF, hG, eventIndicator, hbox]
  · simp only [if_pos hF, if_neg hG, mul_zero]
    exact mul_nonneg
      (mul_nonneg (realLayer_increment_nonneg hf hlayerF)
        (realLayer_increment_nonneg hg hlayerG))
      (eventIndicator_nonneg _ omega)
  · simp only [if_neg hF, zero_mul]
    exact mul_nonneg
      (mul_nonneg (realLayer_increment_nonneg hf hlayerF)
        (realLayer_increment_nonneg hg hlayerG))
      (eventIndicator_nonneg _ omega)
  · simp only [if_neg hF, zero_mul]
    exact mul_nonneg
      (mul_nonneg (realLayer_increment_nonneg hf hlayerF)
        (realLayer_increment_nonneg hg hlayerG))
      (eventIndicator_nonneg _ omega)



theorem functionalDisjointMax_real_le_levelBoxes {f g : ConfigSpace E -> ℝ}
    (hf : ∀ omega, 0 ≤ f omega) (hg : ∀ omega, 0 ≤ g omega)
    (omega : ConfigSpace E) :
    functionalDisjointMax f g omega ≤
      ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
        layerF.2 * layerG.2 *
          eventIndicator
            (disjointOccurrence (realUpperLevel f layerF.1)
              (realUpperLevel g layerG.1)) omega := by
  unfold functionalDisjointMax functionalDisjointMaxAt
  apply Finset.sup'_le
  intro pair hpair
  exact cylinderMin_mul_le_realLevelBoxes hf hg pair.1 pair.2
    (mem_disjointCoordinatePairs.mp hpair) omega




theorem productExpectation_real_eq_levels (phi : E -> Bool -> ℝ)
    {f : ConfigSpace E -> ℝ} (hf : ∀ omega, 0 ≤ f omega) :
    productExpectation phi f =
      ∑ layer ∈ realLayerSet f,
        layer.2 * wprob phi (realUpperLevel f layer.1) := by
  unfold productExpectation wprob
  simp_rw [real_value_eq_layer_sum hf, Finset.mul_sum]
  simp only [eventIndicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro layer hlayer
  apply Finset.sum_congr rfl
  intro omega homega
  ring




theorem functionalBKR_monotone_real (phi : E -> Bool -> ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (f g : ConfigSpace E -> ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega)
    (hf : Monotone f) (hg : Monotone g) :
    productExpectation phi (functionalDisjointMax f g) ≤
      productExpectation phi f * productExpectation phi g := by
  calc
    productExpectation phi (functionalDisjointMax f g) ≤
        ∑ omega : ConfigSpace E, pweight phi omega *
          (∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
            layerF.2 * layerG.2 *
              eventIndicator
                (disjointOccurrence (realUpperLevel f layerF.1)
                  (realUpperLevel g layerG.1)) omega) := by
      unfold productExpectation
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (functionalDisjointMax_real_le_levelBoxes hf0 hg0 omega)
        (pweight_nonneg hphi0 omega)
    _ = ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            wprob phi
              (disjointOccurrence (realUpperLevel f layerF.1)
                (realUpperLevel g layerG.1)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro layerF hlayerF
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro layerG hlayerG
      unfold wprob eventIndicator
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g,
          layerF.2 * layerG.2 *
            (wprob phi (realUpperLevel f layerF.1) *
              wprob phi (realUpperLevel g layerG.1)) := by
      apply Finset.sum_le_sum
      intro layerF hlayerF
      apply Finset.sum_le_sum
      intro layerG hlayerG
      apply mul_le_mul_of_nonneg_left
      · exact bk_wprob_general phi hphi0 hphi1
          (realUpperLevel_isIncreasing hf layerF.1)
          (realUpperLevel_isIncreasing hg layerG.1)
      · exact mul_nonneg (realLayer_increment_nonneg hf0 hlayerF)
          (realLayer_increment_nonneg hg0 hlayerG)
    _ = productExpectation phi f * productExpectation phi g := by
      rw [productExpectation_real_eq_levels phi hf0,
        productExpectation_real_eq_levels phi hg0, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro layerF hlayerF
      apply Finset.sum_congr rfl
      intro layerG hlayerG
      ring

end StatMech.FrontierA
