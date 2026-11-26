/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaverStepsFour.Checker
import all CSLibExt.Computability.BusyBeaverStepsFour.Batch11.Certify
import all CSLibExt.Computability.BusyBeaverStepsFour.Checker
meta import all CSLibExt.Computability.BusyBeaverStepsFour.Checker

/-! # Four-state search: row 11, initial write one, indices 8–15 -/

namespace Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks each of the 128 subtrees in this part.
public theorem checkedRow11OneHigh (k : Fin 8) : BatchCertified 1 11 (k.addNat 8) := by
  checkFourStateBatch11Part 1 8 k

end Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted
