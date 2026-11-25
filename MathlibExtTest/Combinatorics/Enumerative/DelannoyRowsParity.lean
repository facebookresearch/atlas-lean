/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.DelannoyRowsParity

namespace MetaMathlibExt.DelannoyConstructions

private def array (m n : ℕ) : ℤ := 2 ^ m * 3 ^ n

private theorem array_step (m n : ℕ) :
    array (m + 1) (n + 1) = array m (n + 1) + array (m + 1) n + array m n := by
  simp only [array, pow_succ]
  ring

-- Rows 0 and 1 start in different parity classes.
example : ¬ array 0 5 ≡ array 1 5 [ZMOD 2] :=
  (delannoyArray_rows_parity array array_step 0).2 (by decide) 5

-- Rows 1 and 2 start in the same parity class.
example : array 1 5 ≡ array 2 5 [ZMOD 2] :=
  (delannoyArray_rows_parity array array_step 1).1 (by decide) 5

end MetaMathlibExt.DelannoyConstructions
