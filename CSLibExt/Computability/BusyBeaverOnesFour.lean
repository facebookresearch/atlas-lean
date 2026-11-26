/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaver
import all CSLibExt.Computability.BusyBeaverStepsFour.Checker
import all CSLibExt.Computability.BusyBeaverStepsFour

/-!
# Four-state Busy Beaver score value

The proof extends the certified search in `CSLibExt.Computability.BusyBeaverStepsFour.Checker`.
It checks the score of every possible halting transition. The machine that halts in 107 steps
attains this score of 13.

## References

* Allen H. Brady, *The Conjectured Highest Scoring Machines for Rado's $\Sigma(k)$ for the
  Value $k = 4$*, IEEE Transactions on Electronic Computers **EC-15** (1966), no. 5, 802–803.
  This is the original source of the 107-step machine used for the lower bound.
* Allen H. Brady, *The Determination of the Value of Rado's Noncomputable Function $\Sigma(k)$
  for Four-State Turing Machines*, Mathematics of Computation **40** (1983), no. 162, 647–665.
  Section 1, p. 649, states both exact values and explains the final-write convention: the
  halting transition writes a one and moves before entering the halt state.
-/

namespace Cslib.BusyBeaverWanted

open Cslib.BusyBeaver

/-- **Four-state Busy Beaver score value.** Rado's score function $\Sigma$ satisfies
$\Sigma(4) = 13$: among the two-symbol Busy Beaver machines with $4$ working states that halt when
started on the blank tape, the largest number of ones left on the tape at the halting time is $13$.

Source: Brady (1983), determination of `Σ(4) = 13`. -/
public theorem busyBeaverOnes_four_wanted :
    busyBeaverOnes 4 = 13 :=
  busyBeaverSteps_four_wanted.ones_value_of_batches busyBeaverSteps_four_wanted.checkedBatches

end Cslib.BusyBeaverWanted
