/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A binding price ceiling creates excess demand (Atlas EC08.T04)

Source: OpenStax, *Principles of Economics 3e* (2022), §3.4 "Price Ceilings and Price Floors":
"A price ceiling keeps a price from rising above a certain level"; "when the market price is not
allowed to rise to the equilibrium level, quantity demanded exceeds quantity supplied, and thus a
shortage occurs" (rent-control example around Figure 3.21: at the controlled rent, 19,000 units are
demanded but 15,000 supplied, against 17,000 at the market rent of $600).

The market is given by primitive demand and supply schedules (no optimization model). The ceiling
`c` binds when it lies below every equilibrium price, so there is no equilibrium at or below `c`.
Weak monotonicity gives nonnegative excess demand at `c`; strict monotonicity of either schedule
makes it positive.
-/

namespace MathlibExt.Economics.PriceCeiling

/-- A single competitive market given by primitive schedules: `demand p` and `supply p` are the
quantities demanded and supplied at price `p`. -/
structure Market where
  /-- Quantity demanded at each price. -/
  demand : ℝ → ℝ
  /-- Quantity supplied at each price. -/
  supply : ℝ → ℝ

namespace Market

/-- Excess demand `D(p) - S(p)`; positive excess demand is a shortage. -/
def excessDemand (M : Market) (p : ℝ) : ℝ :=
  M.demand p - M.supply p

/-- `pstar` is an equilibrium price: quantity demanded equals quantity supplied. -/
def IsEquilibriumPrice (M : Market) (pstar : ℝ) : Prop :=
  M.demand pstar = M.supply pstar

/-- The ceiling `c` binds at the equilibrium price `pstar`: `pstar` is an equilibrium price, and
`c` lies strictly below every equilibrium price, so there is no equilibrium at or below `c` and
the price cannot rise to any equilibrium level. -/
def IsBindingCeiling (M : Market) (c pstar : ℝ) : Prop :=
  M.IsEquilibriumPrice pstar ∧ ∀ p, M.IsEquilibriumPrice p → c < p

/-- A ceiling at or below an equilibrium price leaves no excess supply when demand is weakly
decreasing and supply weakly increasing between the ceiling and the equilibrium price. -/
theorem excessDemand_nonneg_of_le (M : Market) {c pstar : ℝ} (heq : M.IsEquilibriumPrice pstar)
    (hc : c ≤ pstar) (hD : AntitoneOn M.demand (Set.Icc c pstar))
    (hS : MonotoneOn M.supply (Set.Icc c pstar)) : 0 ≤ M.excessDemand c := by
  have hcmem : c ∈ Set.Icc c pstar := Set.left_mem_Icc.mpr hc
  have hsmem : pstar ∈ Set.Icc c pstar := Set.right_mem_Icc.mpr hc
  have h1 : M.demand pstar ≤ M.demand c := hD hcmem hsmem hc
  have h2 : M.supply c ≤ M.supply pstar := hS hcmem hsmem hc
  have heq' : M.demand pstar = M.supply pstar := heq
  show 0 ≤ M.demand c - M.supply c
  linarith

/-- A binding ceiling creates a shortage when demand is strictly decreasing. -/
theorem excessDemand_pos_of_strictAntiOn (M : Market) {c pstar : ℝ}
    (hb : M.IsBindingCeiling c pstar) (hD : StrictAntiOn M.demand (Set.Icc c pstar))
    (hS : MonotoneOn M.supply (Set.Icc c pstar)) : 0 < M.excessDemand c := by
  obtain ⟨heq, hbind⟩ := hb
  have hlt : c < pstar := hbind pstar heq
  have hc : c ≤ pstar := le_of_lt hlt
  have hcmem : c ∈ Set.Icc c pstar := Set.left_mem_Icc.mpr hc
  have hsmem : pstar ∈ Set.Icc c pstar := Set.right_mem_Icc.mpr hc
  have h1 : M.demand pstar < M.demand c := hD hcmem hsmem hlt
  have h2 : M.supply c ≤ M.supply pstar := hS hcmem hsmem hc
  have heq' : M.demand pstar = M.supply pstar := heq
  show 0 < M.demand c - M.supply c
  linarith

/-- A binding ceiling creates a shortage when supply is strictly increasing. -/
theorem excessDemand_pos_of_strictMonoOn (M : Market) {c pstar : ℝ}
    (hb : M.IsBindingCeiling c pstar) (hD : AntitoneOn M.demand (Set.Icc c pstar))
    (hS : StrictMonoOn M.supply (Set.Icc c pstar)) : 0 < M.excessDemand c := by
  obtain ⟨heq, hbind⟩ := hb
  have hlt : c < pstar := hbind pstar heq
  have hc : c ≤ pstar := le_of_lt hlt
  have hcmem : c ∈ Set.Icc c pstar := Set.left_mem_Icc.mpr hc
  have hsmem : pstar ∈ Set.Icc c pstar := Set.right_mem_Icc.mpr hc
  have h1 : M.demand pstar ≤ M.demand c := hD hcmem hsmem hc
  have h2 : M.supply c < M.supply pstar := hS hcmem hsmem hlt
  have heq' : M.demand pstar = M.supply pstar := heq
  show 0 < M.demand c - M.supply c
  linarith

end Market

end MathlibExt.Economics.PriceCeiling
