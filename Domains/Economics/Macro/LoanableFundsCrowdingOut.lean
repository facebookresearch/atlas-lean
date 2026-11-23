/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic

/-!
# Crowding out in a specified loanable-funds model

Saving supplies funds, `S(r) = s0 + s1 * r` with `s1 > 0`; investment
demands funds, `I(r) = i0 - i1 * r` with `i1 > 0`; the government deficit
`D` adds to funds demanded, so the market clears at `S(r) = I(r) + D`, i.e.
at `r* = (i0 + D - s0) / (s1 + i1)`. A higher deficit raises the equilibrium
rate, raises equilibrium saving, and lowers equilibrium investment: government
borrowing crowds out private investment. These are discrete comparative
statics in `D` (difference forms of `dr*/dD = 1/(s1+i1) > 0` and
`dI*/dD = −i1/(s1+i1) < 0`). No claim is made about welfare, about a closed
vs open economy, or about nonlinear schedules.

## Main results

* `equilibriumRate_clears_market`: `r*` solves `S(r*) = I(r*) + D`.
* `equilibriumRate_strictMono`: a higher deficit raises `r*`.
* `crowdingOut`: a higher deficit lowers equilibrium investment.
* `savingAtEquilibrium_strictMono`: a higher deficit raises equilibrium saving.

## References

* N. G. Mankiw, *Macroeconomics*, Worth Publishers, chapter on the market
  for loanable funds.

Atlas roadmap target MA05.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Macro.LoanableFundsCrowdingOut

/-- Saving schedule: funds supplied at interest rate `r`, with intercept `s0`
and slope `s1 > 0` (source clause: "upward-sloping saving schedule"). -/
noncomputable def saving (s0 s1 r : ℝ) : ℝ :=
  s0 + s1 * r

/-- Investment schedule: funds demanded by private investors at rate `r`, with
intercept `i0` and slope magnitude `i1 > 0` (source clause: "downward-sloping
investment schedule"). -/
noncomputable def investment (i0 i1 r : ℝ) : ℝ :=
  i0 - i1 * r

/-- Equilibrium interest rate in the specified linear loanable-funds model:
the rate clearing `S(r) = I(r) + D`, i.e. `(i0 + D - s0) / (s1 + i1)`
(source clause: "market-clearing rate"). -/
noncomputable def equilibriumRate (s0 s1 i0 i1 D : ℝ) : ℝ :=
  (i0 + D - s0) / (s1 + i1)

/-- **Market clearing.** The equilibrium rate solves `S(r*) = I(r*) + D`
(Atlas roadmap MA05.T03). -/
theorem equilibriumRate_clears_market (s0 s1 i0 i1 D : ℝ) (h : s1 + i1 ≠ 0) :
    saving s0 s1 (equilibriumRate s0 s1 i0 i1 D) =
      investment i0 i1 (equilibriumRate s0 s1 i0 i1 D) + D := by
  unfold saving investment equilibriumRate
  field_simp
  ring

/-- **A higher deficit raises the equilibrium rate.** For `s1 > 0`, `i1 > 0`,
`D₁ < D₂` implies `r*(D₁) < r*(D₂)` (difference form of `dr*/dD = 1/(s1+i1) > 0`). -/
theorem equilibriumRate_strictMono (s0 s1 i0 i1 : ℝ) (hs1 : 0 < s1) (hi1 : 0 < i1)
    {D1 D2 : ℝ} (hD : D1 < D2) :
    equilibriumRate s0 s1 i0 i1 D1 < equilibriumRate s0 s1 i0 i1 D2 := by
  unfold equilibriumRate
  have hpos : 0 < s1 + i1 := add_pos hs1 hi1
  have hnum : i0 + D1 - s0 < i0 + D2 - s0 := by linarith
  exact div_lt_div_of_pos_right hnum hpos

/-- **Crowding out.** For `s1 > 0`, `i1 > 0`, a higher government deficit
lowers equilibrium investment: `D₁ < D₂` implies `I(r*(D₂)) < I(r*(D₁))`
(difference form of `dI*/dD = −i1/(s1+i1) < 0`). This is the stated
crowding-out comparative static (Atlas roadmap MA05.T03). -/
theorem crowdingOut (s0 s1 i0 i1 : ℝ) (hs1 : 0 < s1) (hi1 : 0 < i1)
    {D1 D2 : ℝ} (hD : D1 < D2) :
    investment i0 i1 (equilibriumRate s0 s1 i0 i1 D2) <
      investment i0 i1 (equilibriumRate s0 s1 i0 i1 D1) := by
  unfold investment
  have hrate := equilibriumRate_strictMono s0 s1 i0 i1 hs1 hi1 hD
  have hmul := mul_lt_mul_of_pos_left hrate hi1
  exact sub_lt_sub_left hmul i0

/-- **A higher deficit raises equilibrium saving.** For `s1 > 0`, `i1 > 0`,
`D₁ < D₂` implies `S(r*(D₁)) < S(r*(D₂))`: saving rises to fund the deficit
while investment is crowded out. -/
theorem savingAtEquilibrium_strictMono (s0 s1 i0 i1 : ℝ) (hs1 : 0 < s1)
    (hi1 : 0 < i1) {D1 D2 : ℝ} (hD : D1 < D2) :
    saving s0 s1 (equilibriumRate s0 s1 i0 i1 D1) <
      saving s0 s1 (equilibriumRate s0 s1 i0 i1 D2) := by
  unfold saving
  have hrate := equilibriumRate_strictMono s0 s1 i0 i1 hs1 hi1 hD
  have hmul := mul_lt_mul_of_pos_left hrate hs1
  exact add_lt_add_right hmul s0

end MathlibExt.Economics.Macro.LoanableFundsCrowdingOut
