/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Sort.PermuteToUnimodal
meta import CSLibExt.Algorithms.Lean.Sort.PermuteToUnimodal

open MathlibExt.TheoryOfComputation.PermuteToUnimodalWanted.ProgramVerification

-- The empty path and a single position that can be placed at either end.
#guard minRearrange #[] == 0
#guard minRearrange #[1] == 0

-- Equal second coordinates must extend a chain. Both monotone orders are unimodal.
#guard minRearrange #[1, 2, 3, 4] == 0
#guard minRearrange #[4, 3, 2, 1] == 0

-- A swap suffices in the first example. The second can keep only one position.
#guard minRearrange #[1, 6, 4, 3, 2, 5] == 2
#guard minRearrange #[4, 3, 2, 1, 5] == 4

example : Unimodal #[5, 6, 4, 3, 2, 1] :=
  ⟨#[5, 6], #[4, 3, 2, 1], rfl, by decide, by decide⟩

example : differences #[5, 6, 4, 3, 2, 1].toVector #[1, 6, 4, 3, 2, 5].toVector = 2 := by
  decide
