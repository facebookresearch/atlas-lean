/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Screening
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Examples for `MathlibExt.Economics.Screening`: the second-best menu at `θ_L = 2`,
`θ_H = 3`, `p_L = p_H = 1/2`, and a parameter choice outside the regime where individual
rationality fails, and an exact check of individual rationality and incentive compatibility at
the regime menu. -/

@[expose] public section

namespace MathlibExtTest.Economics.Screening

open MathlibExt.Economics.Screening

/-- Concrete test: `θL = 2, θH = 3, pL = pH = 1/2` gives the menu `(1, 2, 3, 8)`. -/
example : secondBestMenu 2 3 (1/2) (1/2) = ⟨1, 2, 3, 8⟩ := by
  simp only [secondBestMenu, Menu.mk.injEq]
  norm_num

/-- Concrete test: the low type's utility from its contract is `0`. -/
example : utility 2 1 2 = 0 := by
  norm_num [utility]

/-- Concrete test: the high type's utility from its contract is `1`. -/
example : utility 3 3 8 = 1 := by
  norm_num [utility]

/-- Outside the regime (`θL = 1, θH = 3`), the low quantity is negative. -/
example : (secondBestMenu 1 3 (1/2) (1/2)).qL = -1 := by
  simp only [secondBestMenu]
  norm_num

/-- Outside the regime, individual rationality fails. -/
example : ¬ IndividuallyRational 1 3 (secondBestMenu 1 3 (1/2) (1/2)) := by
  intro h
  simp only [IndividuallyRational] at h
  obtain ⟨_, h2⟩ := h
  have hval : utility 3 (secondBestMenu 1 3 (1/2) (1/2)).qH
      (secondBestMenu 1 3 (1/2) (1/2)).tH = -2 := by
    simp only [utility, secondBestMenu]
    norm_num
  rw [hval] at h2
  linarith

/-- Concrete test: the full IR ∧ IC conclusion holds at `θL = 2, θH = 3, pL = pH = 1/2`. -/
example : IndividuallyRational 2 3 (secondBestMenu 2 3 (1/2) (1/2)) ∧
    IncentiveCompatible 2 3 (secondBestMenu 2 3 (1/2) (1/2)) := by
  apply secondBestMenu_ir_ic
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- Concrete test: the high type taking the low contract gets `1` (its IC binds). -/
example : utility 3 1 2 = 1 := by
  norm_num [utility]

/-- Concrete test: the low type taking the high contract gets `-2`. -/
example : utility 2 3 8 = -2 := by
  norm_num [utility]

/-- Concrete test: the low type strictly prefers its own contract (`-2 < 0`). -/
example : utility 2 3 8 < 0 := by
  norm_num [utility]

end MathlibExtTest.Economics.Screening
