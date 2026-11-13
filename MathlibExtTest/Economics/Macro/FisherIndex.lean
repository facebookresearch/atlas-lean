/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.Macro.FisherIndex
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.Macro.FisherIndex` -/

namespace MathlibExtTest.Economics.Macro.FisherIndex

open MathlibExt.Economics.Macro.FisherIndex

/-- Different two-good basket: base prices `(2, 1)`, current prices `(3, 2)`,
base basket `(2, 1)`, current basket `(1, 2)`. -/
example :
    fisherIndex ![3, 2] ![2, 1] ![1, 2] ![2, 1] (Finset.univ : Finset (Fin 2)) *
        fisherIndex ![2, 1] ![3, 2] ![2, 1] ![1, 2] (Finset.univ : Finset (Fin 2)) = 1 := by
  apply fisher_time_reversal <;> simp [Fin.sum_univ_two] <;> norm_num

end MathlibExtTest.Economics.Macro.FisherIndex
