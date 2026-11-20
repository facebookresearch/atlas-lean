/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.PartialEquilibrium.PriceCeiling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Economics.PriceCeiling MathlibExt.Economics.Market

namespace MathlibExtTest.Economics.PartialEquilibrium.PriceCeiling

namespace PriceCeilingExamples

/-- Demand after the shift in the OpenStax §3.4 rent-control example. -/
def rentDemand (p : ℝ) : ℝ := 29000 - 20 * p

/-- Supply in the OpenStax §3.4 example, with equilibrium rent `600` and `17000` units. -/
def rentSupply (p : ℝ) : ℝ := 5000 + 20 * p

theorem rent_isEquilibriumPrice : IsEquilibrium rentDemand rentSupply 600 := by
  norm_num [rentDemand, rentSupply, IsEquilibrium]

theorem rent_excessDemand_500 : excessDemand rentDemand rentSupply 500 = 4000 := by
  norm_num [rentDemand, rentSupply, excessDemand]

theorem rent_shortage : 0 < excessDemand rentDemand rentSupply 500 := by
  have hb : IsBindingCeiling rentDemand rentSupply 500 600 := by
    refine ⟨rent_isEquilibriumPrice, fun p hp => ?_⟩
    have hp' : 29000 - 20 * p = 5000 + 20 * p := hp
    linarith
  have hD : StrictAntiOn rentDemand (Set.Icc 500 600) := by
    intro x _ y _ hxy
    show 29000 - 20 * y < 29000 - 20 * x
    linarith
  have hS : MonotoneOn rentSupply (Set.Icc 500 600) := by
    intro x _ y _ hxy
    show 5000 + 20 * x ≤ 5000 + 20 * y
    linarith
  exact excessDemand_pos_of_strictAntiOn rentDemand rentSupply hb hD hS

/-- Flat demand and supply: every price is an equilibrium. -/
def flat (_ : ℝ) : ℝ := 10

theorem flat_notBindingCeiling : ∀ pstar, ¬ IsBindingCeiling flat flat 3 pstar := by
  intro pstar hb
  obtain ⟨_, hbind⟩ := hb
  have h3 : IsEquilibrium flat flat 3 := rfl
  have hlt := hbind 3 h3
  exact lt_irrefl (3 : ℝ) hlt

theorem flat_excessDemand_zero : excessDemand flat flat 3 = 0 := by
  norm_num [flat, excessDemand]

/-- Demand is flat below the threshold and drops there. -/
noncomputable def plateauDemand (p : ℝ) : ℝ := if p < 1 then 2 else 1

/-- Supply stays constant across the demand threshold. -/
def plateauSupply (_ : ℝ) : ℝ := 1

/-- The ceiling binds even though neither schedule is strictly monotone. -/
theorem plateau_shortage : 0 < excessDemand plateauDemand plateauSupply 0 := by
  have hb : IsBindingCeiling plateauDemand plateauSupply 0 1 := by
    refine ⟨by norm_num [plateauDemand, plateauSupply, IsEquilibrium], ?_⟩
    intro p hp
    have hp1 : ¬ p < 1 := by
      intro h
      norm_num [IsEquilibrium, plateauDemand, plateauSupply, h] at hp
    exact lt_of_lt_of_le (by norm_num) (le_of_not_gt hp1)
  have hD : AntitoneOn plateauDemand (Set.Icc 0 1) := by
    intro x _ y _ hxy
    by_cases hy : y < 1
    · simp [plateauDemand, hy, lt_of_le_of_lt hxy hy]
    · by_cases hx : x < 1 <;> simp [plateauDemand, hy, hx]
  have hS : MonotoneOn plateauSupply (Set.Icc 0 1) := by
    intro x _ y _ _
    simp [plateauSupply]
  exact excessDemand_pos plateauDemand plateauSupply hb hD hS

/-- The new theorem applies where the strict-demand corollary cannot. -/
example : ¬ StrictAntiOn plateauDemand (Set.Icc 0 1) := by
  intro h
  have hlt := h (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num) (by norm_num)
  norm_num [plateauDemand] at hlt

/-- The same example also rules out strict supply monotonicity. -/
example : ¬ StrictMonoOn plateauSupply (Set.Icc 0 1) := by
  intro h
  have hlt := h (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num) (by norm_num)
  norm_num [plateauSupply] at hlt

end PriceCeilingExamples

end MathlibExtTest.Economics.PartialEquilibrium.PriceCeiling
