/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.SupplyDemand
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
Weak monotonicity of both schedules gives positive excess demand at a binding ceiling: zero
excess demand would make the ceiling itself an equilibrium.
-/

namespace MathlibExt.Economics.PriceCeiling

open MathlibExt.Economics.Market

/-- The ceiling `c` binds at the equilibrium price `pstar`: `pstar` is an equilibrium price, and
`c` lies strictly below every equilibrium price, so there is no equilibrium at or below `c` and
the price cannot rise to any equilibrium level. -/
def IsBindingCeiling (D S : ℝ → ℝ) (c pstar : ℝ) : Prop :=
  IsEquilibrium D S pstar ∧ ∀ p, IsEquilibrium D S p → c < p

/-- A ceiling at or below an equilibrium price leaves no excess supply when demand is weakly
decreasing and supply weakly increasing between the ceiling and the equilibrium price. -/
theorem excessDemand_nonneg_of_le (D S : ℝ → ℝ) {c pstar : ℝ}
    (heq : IsEquilibrium D S pstar) (hc : c ≤ pstar)
    (hD : AntitoneOn D (Set.Icc c pstar)) (hS : MonotoneOn S (Set.Icc c pstar)) :
    0 ≤ excessDemand D S c := by
  have hcmem : c ∈ Set.Icc c pstar := Set.left_mem_Icc.mpr hc
  have hsmem : pstar ∈ Set.Icc c pstar := Set.right_mem_Icc.mpr hc
  have h1 : D pstar ≤ D c := hD hcmem hsmem hc
  have h2 : S c ≤ S pstar := hS hcmem hsmem hc
  have heq' : D pstar = S pstar := heq
  show 0 ≤ D c - S c
  linarith

/-- A binding ceiling creates a shortage under weak monotonicity of both schedules. -/
theorem excessDemand_pos (D S : ℝ → ℝ) {c pstar : ℝ}
    (hb : IsBindingCeiling D S c pstar) (hD : AntitoneOn D (Set.Icc c pstar))
    (hS : MonotoneOn S (Set.Icc c pstar)) : 0 < excessDemand D S c := by
  have hnonneg := excessDemand_nonneg_of_le D S hb.1 (hb.2 pstar hb.1).le hD hS
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have heq : IsEquilibrium D S c := sub_eq_zero.mp hzero.symm
  exact lt_irrefl c (hb.2 c heq)

/-- A binding ceiling creates a shortage when demand is strictly decreasing. -/
theorem excessDemand_pos_of_strictAntiOn (D S : ℝ → ℝ) {c pstar : ℝ}
    (hb : IsBindingCeiling D S c pstar) (hD : StrictAntiOn D (Set.Icc c pstar))
    (hS : MonotoneOn S (Set.Icc c pstar)) : 0 < excessDemand D S c := by
  exact excessDemand_pos D S hb hD.antitoneOn hS

/-- A binding ceiling creates a shortage when supply is strictly increasing. -/
theorem excessDemand_pos_of_strictMonoOn (D S : ℝ → ℝ) {c pstar : ℝ}
    (hb : IsBindingCeiling D S c pstar) (hD : AntitoneOn D (Set.Icc c pstar))
    (hS : StrictMonoOn S (Set.Icc c pstar)) : 0 < excessDemand D S c := by
  exact excessDemand_pos D S hb hD hS.monotoneOn

end MathlibExt.Economics.PriceCeiling
