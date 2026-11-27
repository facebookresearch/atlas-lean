/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaverStepsFour.Checker
import all CSLibExt.Computability.BusyBeaverStepsFour.Checker
meta import all CSLibExt.Computability.BusyBeaverStepsFour.Checker

/-!
# Four-state Busy Beaver search, branch 3

This module verifies the certificate batches for the second transition choice numbered 3.
-/

namespace Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the full certificate for each finite subtree.
public theorem checkedRow3 (w : Fin 2) (k : Fin 16) : BatchCertified w 3 k := by
  unfold BatchCertified isBatchCertified
  fin_cases w
  · checkFourStateBatches 0 3 k
  · checkFourStateBatches 1 3 k

end Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted
