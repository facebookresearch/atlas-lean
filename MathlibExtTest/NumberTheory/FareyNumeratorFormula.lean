/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyNumeratorFormula

open MathlibExt.NumberTheory.FareyNumeratorWanted

-- The lower endpoint contributes 1/1.
example : fareyNumeratorCount 2 1 = 2 := by decide +kernel

example : (fareyNumeratorCount 2 1 : ℚ) = 2 := by
  rw [fareyNumeratorCount_formula 1 2 (by decide) (by decide)]
  decide +kernel

-- The denominators are 7, 11, and 13. The remainder sum is nonzero.
example : (fareyNumeratorCount 16 6 : ℚ) = 3 := by
  rw [fareyNumeratorCount_formula 6 16 (by decide) (by decide)]
  decide +kernel
