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

open MathlibExt.Economics.PriceCeiling

namespace MathlibExtTest.Economics.PartialEquilibrium.PriceCeiling

namespace PriceCeilingExamples

/-- Linear rent-control market matching the relevant OpenStax §3.4 rent-control rows after the
demand shift:
`D(p) = 29000 - 20 p`, `S(p) = 5000 + 20 p`, equilibrium rent `600` with `17000` units. -/
def rent : Market where
  demand p := 29000 - 20 * p
  supply p := 5000 + 20 * p

theorem rent_isEquilibriumPrice : rent.IsEquilibriumPrice 600 := by
  norm_num [rent, Market.IsEquilibriumPrice]

theorem rent_excessDemand_500 : rent.excessDemand 500 = 4000 := by
  norm_num [rent, Market.excessDemand]

theorem rent_shortage : 0 < rent.excessDemand 500 := by
  have hb : rent.IsBindingCeiling 500 600 := by
    refine ⟨rent_isEquilibriumPrice, fun p hp => ?_⟩
    have hp' : 29000 - 20 * p = 5000 + 20 * p := by
      simpa [rent, Market.IsEquilibriumPrice] using hp
    linarith
  have hD : StrictAntiOn rent.demand (Set.Icc 500 600) := by
    intro x _ y _ hxy
    show 29000 - 20 * y < 29000 - 20 * x
    linarith
  have hS : MonotoneOn rent.supply (Set.Icc 500 600) := by
    intro x _ y _ hxy
    show 5000 + 20 * x ≤ 5000 + 20 * y
    linarith
  exact Market.excessDemand_pos_of_strictAntiOn rent hb hD hS

/-- Flat (perfectly inelastic, equal) schedules: every price is an equilibrium, in particular the
ceiling itself, so no ceiling is binding under the strengthened definition (the old definition,
which only compared against one chosen equilibrium, would wrongly have counted `3` as binding
against `pstar = 5`). Excess demand at `3` is nevertheless `0`. -/
def flat : Market where
  demand _ := 10
  supply _ := 10

theorem flat_notBindingCeiling : ∀ pstar, ¬ flat.IsBindingCeiling 3 pstar := by
  intro pstar hb
  obtain ⟨_, hbind⟩ := hb
  have h3 : flat.IsEquilibriumPrice 3 := by
    norm_num [flat, Market.IsEquilibriumPrice]
  have hlt := hbind 3 h3
  exact lt_irrefl (3 : ℝ) hlt

theorem flat_excessDemand_zero : flat.excessDemand 3 = 0 := by
  norm_num [flat, Market.excessDemand]

/-- Demand is flat below the threshold; supply is flat everywhere. -/
noncomputable def plateau : Market where
  demand p := if p < 1 then 2 else 1
  supply _ := 1

/-- The ceiling binds even though neither schedule is strictly monotone. -/
theorem plateau_shortage : 0 < plateau.excessDemand 0 := by
  have hb : plateau.IsBindingCeiling 0 1 := by
    refine ⟨by norm_num [plateau, Market.IsEquilibriumPrice], ?_⟩
    intro p hp
    have hp1 : ¬ p < 1 := by
      intro h
      norm_num [Market.IsEquilibriumPrice, plateau, h] at hp
    exact lt_of_lt_of_le (by norm_num) (le_of_not_gt hp1)
  have hD : AntitoneOn plateau.demand (Set.Icc 0 1) := by
    intro x _ y _ hxy
    by_cases hy : y < 1
    · simp [plateau, hy, lt_of_le_of_lt hxy hy]
    · by_cases hx : x < 1 <;> simp [plateau, hy, hx]
  have hS : MonotoneOn plateau.supply (Set.Icc 0 1) := by
    intro x _ y _ _
    simp [plateau]
  exact plateau.excessDemand_pos hb hD hS

/-- The new theorem applies where the strict-demand corollary cannot. -/
example : ¬ StrictAntiOn plateau.demand (Set.Icc 0 1) := by
  intro h
  have hlt := h (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num) (by norm_num)
  norm_num [plateau] at hlt

/-- The same example also rules out strict supply monotonicity. -/
example : ¬ StrictMonoOn plateau.supply (Set.Icc 0 1) := by
  intro h
  have hlt := h (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num) (by norm_num)
  norm_num [plateau] at hlt

end PriceCeilingExamples

end MathlibExtTest.Economics.PartialEquilibrium.PriceCeiling
