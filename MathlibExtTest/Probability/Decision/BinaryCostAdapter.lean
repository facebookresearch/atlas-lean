/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.BinaryCostAdapter

@[expose] public section

open MathlibExt.Probability.Decision.BinaryCostAdapter

namespace MathlibExtTest.Probability.Decision.BinaryCostAdapter

/-- The asymmetric shifted-loss table values are `(2, 3, 0, 0)`. -/
example : binaryShiftedLoss 0 4 2 1 false true = 2 ∧
    binaryShiftedLoss 0 4 2 1 true false = 3 ∧
    binaryShiftedLoss 0 4 2 1 false false = 0 ∧
    binaryShiftedLoss 0 4 2 1 true true = 0 :=
  binaryShiftedLoss_asymmetric_example

/-- At the asymmetric point the rule decides `true`. -/
example (tie : Bool) :
    binaryCostRule (1 / 4) (3 / 4) 0 4 2 1 (fun _ : Unit => (2 : ℝ)) (fun _ => 1) tie () = true :=
  binaryCostRule_asymmetric_example tie

/-- Transposing the two error costs flips that decision to `false`. -/
example (tie : Bool) :
    binaryCostRule (1 / 4) (3 / 4) 0 2 4 1 (fun _ : Unit => (2 : ℝ)) (fun _ => 1) tie () = false :=
  binaryCostRule_transposed_costs_example tie

end MathlibExtTest.Probability.Decision.BinaryCostAdapter
