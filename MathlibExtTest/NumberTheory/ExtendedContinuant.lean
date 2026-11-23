/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ExtendedContinuant

/-! # Tests for extended continuants and the westbound matrix product -/

open MetaMathlibExt

-- A forward continuant at a nonzero start index uses both consecutive terms.
example : extendedContinuant id 1 2 = 7 := by decide

-- The smallest product consists of the single factor at index -1.
example (x : ℤ → ℤ) :
    !![extendedContinuant x (-2) 0, extendedContinuant x (-3) 1;
       extendedContinuant x (-3) 0, extendedContinuant x (-4) 1] =
      !![0, 1; 1, -x (-1)] := by
  simpa [List.ofFn_succ] using (extendedContinuant_westbound_matrix_prod x 1 (by decide)).symm

-- Distinct off-diagonal entries detect a reversal of the two factors.
example :
    !![extendedContinuant id (-3) 0, extendedContinuant id (-4) 1;
       extendedContinuant id (-4) 0, extendedContinuant id (-5) 1] =
      !![1, 1; 2, 3] :=
  (extendedContinuant_westbound_matrix_prod id 2 (by decide)).symm.trans (by decide)
