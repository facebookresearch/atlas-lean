/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaverStepsFour.Checker
import CSLibExt.Computability.BusyBeaverStepsFour.Batch11.OneHigh
import CSLibExt.Computability.BusyBeaverStepsFour.Batch11.OneLow
import CSLibExt.Computability.BusyBeaverStepsFour.Batch11.ZeroHigh
import CSLibExt.Computability.BusyBeaverStepsFour.Batch11.ZeroLow

/-!
# Four-state Busy Beaver search, branch 11

The certificate batches for the second transition choice numbered 11 are checked in four parts.
-/

namespace Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted

public theorem checkedRow11 (w : Fin 2) (k : Fin 16) : BatchCertified w 11 k := by
  by_cases h : k.val < 8
  · let j : Fin 8 := ⟨k.val, h⟩
    have he : j.castAdd 8 = k := Fin.ext rfl
    rw [← he]
    fin_cases w
    · exact checkedRow11ZeroLow j
    · exact checkedRow11OneLow j
  · let j : Fin 8 := ⟨k.val - 8, by have := k.isLt; omega⟩
    have he : j.addNat 8 = k := Fin.ext (Nat.sub_add_cancel (Nat.le_of_not_lt h))
    rw [← he]
    fin_cases w
    · exact checkedRow11ZeroHigh j
    · exact checkedRow11OneHigh j

end Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted
