/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaver
import all CSLibExt.Computability.BusyBeaverStepsFour.Checker
import CSLibExt.Computability.BusyBeaverStepsFour.Batch0
import CSLibExt.Computability.BusyBeaverStepsFour.Batch1
import CSLibExt.Computability.BusyBeaverStepsFour.Batch2
import CSLibExt.Computability.BusyBeaverStepsFour.Batch3
import CSLibExt.Computability.BusyBeaverStepsFour.Batch4
import CSLibExt.Computability.BusyBeaverStepsFour.Batch5
import CSLibExt.Computability.BusyBeaverStepsFour.Batch6
import CSLibExt.Computability.BusyBeaverStepsFour.Batch7
import CSLibExt.Computability.BusyBeaverStepsFour.Batch8
import CSLibExt.Computability.BusyBeaverStepsFour.Batch9
import CSLibExt.Computability.BusyBeaverStepsFour.Batch10
import CSLibExt.Computability.BusyBeaverStepsFour.Batch11

/-!
# Four-state Busy Beaver shift value

The four-state Busy Beaver shift maximum on a blank tape is 107.
-/

namespace Cslib.BusyBeaverWanted

open Cslib.BusyBeaver

namespace busyBeaverSteps_four_wanted

private theorem checkedBatches (w : Fin 2) (j k : Fin 16) : BatchCertified w j k := by
  fin_cases j
  · exact checkedRow0 w k
  · exact checkedRow1 w k
  · exact checkedRow2 w k
  · exact checkedRow3 w k
  · exact checkedRow4 w k
  · exact checkedRow5 w k
  · exact checkedRow6 w k
  · exact checkedRow7 w k
  · exact checkedRow8 w k
  · exact checkedRow9 w k
  · exact checkedRow10 w k
  · exact checkedRow11 w k
  all_goals
    apply certify_absent_row
    decide +revert +kernel

end busyBeaverSteps_four_wanted

/-- **Four-state Busy Beaver shift value.** Rado's shift function $S$ satisfies $S(4) = 107$:
among the two-symbol Busy Beaver machines with $4$ working states that halt when started on the
blank tape, the largest halting time is $107$.

Source: Brady (1983), determination of `S(4) = 107`. -/
public theorem busyBeaverSteps_four_wanted :
    busyBeaverSteps 4 = 107 :=
  busyBeaverSteps_four_wanted.value_of_batches busyBeaverSteps_four_wanted.checkedBatches

end Cslib.BusyBeaverWanted
