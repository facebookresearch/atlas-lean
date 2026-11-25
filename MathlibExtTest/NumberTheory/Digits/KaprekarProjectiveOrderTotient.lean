/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.KaprekarProjectiveOrderTotient

open MetaMathlibExt

-- At the smallest admissible base, the bound is attained when the power reaches -1.
example : projectiveOrderTwo 5 ≤ 2 :=
  projectiveOrderTwo_le_totient_div_two 5 (by decide) (by decide)

-- The bound also gives 4 for the composite base 15, where the fourth power reaches +1.
example : projectiveOrderTwo 15 ≤ 4 :=
  projectiveOrderTwo_le_totient_div_two 15 (by decide) (by decide)
