/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierA.FunctionalBKRMonotoneReal
import Code.Walls.rb3reimerclose

open scoped BigOperators
open Finset

namespace StatMech.FrontierA

open StatMech.ConfigSpace
open StatMech.Walls.Reimer

variable {E : Type*} [Fintype E] [DecidableEq E]



theorem functionalBKR_real (phi : E → Bool → ℝ)
    (hphi0 : ∀ e b, 0 ≤ phi e b)
    (hphi1 : ∀ e, phi e false + phi e true = 1)
    (f g : ConfigSpace E → ℝ)
    (hf0 : ∀ omega, 0 ≤ f omega) (hg0 : ∀ omega, 0 ≤ g omega) :
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
      · exact reimer_wprob_general_of_core rb3_reimerWprobCore
          phi hphi0 hphi1 _ _
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
