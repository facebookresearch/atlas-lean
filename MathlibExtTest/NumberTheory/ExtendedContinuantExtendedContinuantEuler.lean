/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ExtendedContinuantExtendedContinuantEuler
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Euler's identity for extended continuants

These tests derive a determinant identity at an arbitrary start index and check negative
indices against the sequence `id`.
-/

namespace MathlibExtTest.NumberTheory.ExtendedContinuantExtendedContinuantEuler

open MetaMathlibExt

example (x : ℤ → ℤ) (h n : ℤ) :
    extendedContinuant x (n + 1) h * extendedContinuant x (n - 1) (h + 1) -
        extendedContinuant x n (h + 1) * extendedContinuant x n h = (n.negOnePow : ℤ) := by
  have he := extendedContinuant_euler x h n 0 (n + 1)
  ring_nf at he ⊢
  simpa [extendedContinuant_neg_one] using he

example :
    extendedContinuant id (-7) (-1) * extendedContinuant id (-4) (-2) -
        extendedContinuant id (-6) (-2) * extendedContinuant id (-5) (-1) = -6 := by
  have he := extendedContinuant_euler id (-1) (-3) (-2) (-5)
  norm_num at he
  exact he.trans (by decide)

example :
    extendedContinuant id 4 2 * extendedContinuant id (-3) 6 -
        extendedContinuant id 0 6 * extendedContinuant id 1 2 = 930 := by
  have he := extendedContinuant_euler id 2 (-2) 3 1
  norm_num at he
  exact he.trans (by decide)

end MathlibExtTest.NumberTheory.ExtendedContinuantExtendedContinuantEuler
