/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingSecondGy

open MetaMathlibExt

-- At k = n the right side vanishes and the left coefficient is negative.
example : (-1 : ℤ) < 0 :=
  mul_stirlingSecond_sub_gt (n := 1) (k := 1) (by decide) (by decide)

-- At n = 2k the left coefficient vanishes.
example : (0 : ℤ) < 2 :=
  mul_stirlingSecond_sub_gt (n := 2) (k := 1) (by decide) (by decide)

-- For n = 5 and k = 2 both weighted partition counts are positive.
example : (65 : ℤ) < 125 :=
  mul_stirlingSecond_sub_gt (n := 5) (k := 2) (by decide) (by decide)
