/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two-type screening: an individually rational, incentive-compatible menu

A seller offers a menu of two contracts `(q_L, t_L)` and `(q_H, t_H)` (quantity or quality, and
payment) to a buyer whose type is `θ_L` with probability `p_L` or `θ_H > θ_L` with probability
`p_H`. A type-`θ` buyer taking `(q, t)` gets utility `θ q - t`. The menu below is the
second-best menu of the linear-quadratic model (seller cost `q² / 2`): no distortion at the
top, `q_H = θ_H`; downward distortion at the bottom, `q_L = θ_L - (p_H / p_L)(θ_H - θ_L)`; the
low type's participation constraint and the high type's incentive constraint bind. In the
regime `p_H (θ_H - θ_L) ≤ p_L θ_L` the low quantity is nonnegative and the menu satisfies all
four constraints. Optimality of the menu for the seller is not claimed.

## Main results

* `Screening.secondBestMenu_ir_ic`: the second-best menu is individually rational and incentive
  compatible in the regime `p_H (θ_H - θ_L) ≤ p_L θ_L`.
* `Screening.secondBestMenu_binding`: the low type's participation constraint and the high
  type's incentive constraint bind.

## References

* M. Mussa and S. Rosen, *Monopoly and product quality*, J. Econ. Theory 18(2) (1978),
  301–317.
* P. Bolton and M. Dewatripont, *Contract Theory*, MIT Press (2005), §2.1.
-/

@[expose] public section

namespace MathlibExt.Economics.Screening

/-- A menu of two contracts, one meant for each type. -/
structure Menu where
  /-- Quantity of the contract meant for the low type. -/
  qL : ℝ
  /-- Payment of the contract meant for the low type. -/
  tL : ℝ
  /-- Quantity of the contract meant for the high type. -/
  qH : ℝ
  /-- Payment of the contract meant for the high type. -/
  tH : ℝ

/-- The utility `θ q - t` of a type-`θ` buyer taking the contract `(q, t)`. -/
def utility (θ q t : ℝ) : ℝ := θ * q - t

/-- **Individual rationality**: each type weakly prefers its contract to not participating
(outside utility `0`). -/
def IndividuallyRational (θL θH : ℝ) (m : Menu) : Prop :=
  0 ≤ utility θL m.qL m.tL ∧ 0 ≤ utility θH m.qH m.tH

/-- **Incentive compatibility**: each type weakly prefers its own contract to the other
type's contract. -/
def IncentiveCompatible (θL θH : ℝ) (m : Menu) : Prop :=
  utility θH m.qL m.tL ≤ utility θH m.qH m.tH ∧ utility θL m.qH m.tH ≤ utility θL m.qL m.tL

/-- The second-best menu of the linear-quadratic two-type model:
`q_L = θ_L - (p_H / p_L)(θ_H - θ_L)`, `t_L = θ_L q_L`, `q_H = θ_H`,
`t_H = θ_H q_H - (θ_H - θ_L) q_L`. -/
noncomputable def secondBestMenu (θL θH pL pH : ℝ) : Menu where
  qL := θL - pH / pL * (θH - θL)
  tL := θL * (θL - pH / pL * (θH - θL))
  qH := θH
  tH := θH * θH - (θH - θL) * (θL - pH / pL * (θH - θL))

/-- The low type's own utility is zero (participation binds). -/
private theorem utility_low_own (θL θH pL pH : ℝ) :
    utility θL (secondBestMenu θL θH pL pH).qL (secondBestMenu θL θH pL pH).tL = 0 := by
  simp only [utility, secondBestMenu]
  ring

/-- The high type is indifferent between the two contracts (incentive binds). -/
private theorem utility_high_cross (θL θH pL pH : ℝ) :
    utility θH (secondBestMenu θL θH pL pH).qL (secondBestMenu θL θH pL pH).tL =
      utility θH (secondBestMenu θL θH pL pH).qH (secondBestMenu θL θH pL pH).tH := by
  simp only [utility, secondBestMenu]
  ring

/-- The high type's own utility equals the information rent `(θH - θL) * qL`. -/
private theorem utility_high_own (θL θH pL pH : ℝ) :
    utility θH (secondBestMenu θL θH pL pH).qH (secondBestMenu θL θH pL pH).tH =
      (θH - θL) * (θL - pH / pL * (θH - θL)) := by
  simp only [utility, secondBestMenu]
  ring

/-- The low type's utility from the high contract, factored. -/
private theorem utility_low_cross (θL θH pL pH : ℝ) :
    utility θL (secondBestMenu θL θH pL pH).qH (secondBestMenu θL θH pL pH).tH =
      (θH - θL) * (θL - pH / pL * (θH - θL) - θH) := by
  simp only [utility, secondBestMenu]
  ring

/-- **The second-best screening menu is individually rational and incentive compatible** in the
regime `p_H (θ_H - θ_L) ≤ p_L θ_L` (nonnegative low quantity), for types `θ_L < θ_H` and
probabilities `p_L > 0`, `p_H ≥ 0`. -/
theorem secondBestMenu_ir_ic {θL θH pL pH : ℝ} (hθ : θL < θH) (hpL : 0 < pL) (hpH : 0 ≤ pH)
    (hreg : pH * (θH - θL) ≤ pL * θL) :
    IndividuallyRational θL θH (secondBestMenu θL θH pL pH) ∧
      IncentiveCompatible θL θH (secondBestMenu θL θH pL pH) := by
  have hΔ : 0 < θH - θL := sub_pos.mpr hθ
  have hr : 0 ≤ pH / pL := div_nonneg hpH hpL.le
  have hq : pH / pL * (θH - θL) ≤ θL := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpL]
    linarith
  have hqL : 0 ≤ θL - pH / pL * (θH - θL) := sub_nonneg.mpr hq
  have hmul : 0 ≤ pH / pL * (θH - θL) := mul_nonneg hr hΔ.le
  have hle : θL - pH / pL * (θH - θL) - θH ≤ 0 := by
    have h : θL - pH / pL * (θH - θL) ≤ θH := by linarith
    linarith
  simp only [IndividuallyRational, IncentiveCompatible]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [utility_low_own θL θH pL pH]
  · rw [utility_high_own θL θH pL pH]
    exact mul_nonneg hΔ.le hqL
  · rw [utility_high_cross θL θH pL pH]
  · rw [utility_low_cross θL θH pL pH, utility_low_own θL θH pL pH]
    exact mul_nonpos_of_nonneg_of_nonpos hΔ.le hle

/-- The low type's participation constraint and the high type's incentive constraint bind at
the second-best menu (for any parameters). -/
theorem secondBestMenu_binding (θL θH pL pH : ℝ) :
    utility θL (secondBestMenu θL θH pL pH).qL (secondBestMenu θL θH pL pH).tL = 0 ∧
      utility θH (secondBestMenu θL θH pL pH).qL (secondBestMenu θL θH pL pH).tL =
        utility θH (secondBestMenu θL θH pL pH).qH (secondBestMenu θL θH pL pH).tH := by
  exact ⟨utility_low_own θL θH pL pH, utility_high_cross θL θH pL pH⟩

end MathlibExt.Economics.Screening
