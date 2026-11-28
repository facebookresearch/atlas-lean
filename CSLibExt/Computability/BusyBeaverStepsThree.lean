/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaverOnesThree

/-!
# Three-state Busy Beaver shift value

The three-state shift maximum is 21. The partial-table classification bounds each runtime,
and the machine below reaches the halt state on its twenty-first transition.
-/

namespace Cslib.BusyBeaverWanted

open Cslib.BusyBeaver

namespace busyBeaverSteps_three_wanted

private def champion : Machine 3
  | 0, 0 => (1, .right, some 1)
  | 0, _ => (1, .right, none)
  | 1, 0 => (1, .left, some 1)
  | 1, _ => (0, .right, some 2)
  | _, 0 => (1, .left, some 2)
  | _, _ => (1, .left, some 0)

private theorem lower : 21 ≤ busyBeaverSteps 3 := by
  have h₂₁ : HaltsWithin champion 21 := by
    change (run champion 21).state = none
    decide +kernel
  have h₂₀ : ¬ HaltsWithin champion 20 := by
    change (run champion 20).state ≠ none
    decide +kernel
  have h : Halts champion := ⟨21, h₂₁⟩
  have ht : 21 ≤ haltTime champion h := by
    by_contra! hlt
    exact h₂₀ (haltsWithin_mono (haltsWithin_haltTime _ h) (by omega))
  exact ht.trans (haltTime_le_busyBeaverSteps _ h)

end busyBeaverSteps_three_wanted

/-- **Three-state Busy Beaver shift value.** Rado's shift function $S$ satisfies $S(3) = 21$:
among the two-symbol Busy Beaver machines with $3$ working states that halt when started on the
blank tape, the largest halting time is $21$.

Source: Lin--Radó (1965), determination of `S(3) = 21`. -/
public theorem busyBeaverSteps_three_wanted :
    busyBeaverSteps 3 = 21 := by
  refine le_antisymm ?_ busyBeaverSteps_three_wanted.lower
  exact Finset.sup_le fun M _ => (busyBeaverSteps_three_wanted.machine_bounds M).2

end Cslib.BusyBeaverWanted
