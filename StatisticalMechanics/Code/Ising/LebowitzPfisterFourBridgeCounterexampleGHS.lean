/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample











namespace StatMech.Ising

noncomputable section



theorem fourBridgeSecondMiddleCutCounterexample_violates_ghsZero :
    0 < fourBridgeSecondMiddleCutCounterexampleA ^ 3 -
        3 * fourBridgeSecondMiddleCutCounterexampleA *
          fourBridgeSecondMiddleCutCounterexampleB -
        fourBridgeSecondMiddleCutCounterexampleA +
        3 * fourBridgeSecondMiddleCutCounterexampleC := by
  norm_num [fourBridgeSecondMiddleCutCounterexampleA,
    fourBridgeSecondMiddleCutCounterexampleB,
    fourBridgeSecondMiddleCutCounterexampleC]



theorem fourBridgePointwiseCutCounterexample_violates_ghsZero :
    0 < fourBridgePointwiseCutCounterexampleA ^ 3 -
        3 * fourBridgePointwiseCutCounterexampleA *
          fourBridgePointwiseCutCounterexampleB -
        fourBridgePointwiseCutCounterexampleA +
        3 * fourBridgePointwiseCutCounterexampleC := by
  norm_num [fourBridgePointwiseCutCounterexampleA,
    fourBridgePointwiseCutCounterexampleB,
    fourBridgePointwiseCutCounterexampleC]

end

end StatMech.Ising
