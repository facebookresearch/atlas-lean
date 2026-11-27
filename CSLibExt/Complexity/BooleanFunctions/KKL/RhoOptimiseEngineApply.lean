/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Hypercontractivity.RhoOptimiseEngine
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLUniform

@[expose] public section

/-!
# The rho-optimisation engine discharged at exponent `2`

`roe_rhoOptimise_apply : bph_RhoOptimise 2`: the KKL inequality at `p = 1/2` in Fourier
form follows from the capped hypercontractive estimate with constant `2`. The supporting
cardinality identity is `roe_card_filter_eq_erase`.

## Main results

* `roe_rhoOptimise_apply`: the rho-optimisation engine at exponent `2`.
-/


open scoped BigOperators
open Finset
open Real Filter Topology

set_option linter.style.longLine false

namespace StatMech.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem roe_card_filter_eq_erase :
    (univ.filter (fun S : Finset ι => S.card ≠ 0)) = univ.erase (∅ : Finset ι) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  rw [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]

/-- The rho-optimisation engine discharged at exponent `2`: the KKL inequality at
`p = 1/2` in Fourier form. -/
theorem roe_rhoOptimise_apply : bph_RhoOptimise 2 := by
  intro E _ _ _ φ Hcap
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set c : Finset E → ℝ := fun S => (khc_fourierCoeff f S) ^ 2 with hc
  set δ := maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) f with hδ
  have hcnn : ∀ S : Finset E, 0 ≤ c S := fun S => by rw [hc]; positivity
  have hδnn : 0 ≤ δ := by
    rw [hδ]; exact kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (E := E) (by norm_num) (by norm_num)) f
  have Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
        ≤ δ ^ (u / (2 - u)) * (∑ S : Finset E, 4 * (S.card : ℝ) * c S) := by
    intro u hu0 hu1
    have h := cro2_master_sub φ Hcap u hu0 hu1
    calc (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1) * c S)
        = (∑ S : Finset E, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (khc_fourierCoeff f S) ^ 2) := by
          apply Finset.sum_congr rfl; intro S _; rw [hc]
      _ ≤ δ ^ (u / (2 - u)) * (∑ S : Finset E, 4 * (S.card : ℝ)
            * (khc_fourierCoeff f S) ^ 2) := by rw [hδ, hf] at *; exact h
      _ = δ ^ (u / (2 - u)) * (∑ S : Finset E, 4 * (S.card : ℝ) * c S) := by
          rw [hc]
  have hgain := roe_logGain_four (d := fun S : Finset E => S.card) hcnn hδnn Hmaster
  rw [roe_card_filter_eq_erase] at hgain
  rw [show (∑ S : Finset E, 4 * (S.card : ℝ) * (khc_fourierCoeff f S) ^ 2)
        = ∑ S : Finset E, 4 * (S.card : ℝ) * c S from by
      apply Finset.sum_congr rfl; intro S _; rw [hc]]
  exact hgain

end StatMech.Probability
