/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FareyNumeratorPeriod

open MathlibExt.NumberTheory.FareyNumeratorWanted

-- Two periods for numerator 6 add four denominators, starting at a nonzero remainder.
example : fareyNumeratorCount 28 6 = fareyNumeratorCount 16 6 + 4 :=
  fareyNumeratorCount_add_mul 6 16 2 (by decide) (by decide)

-- The numerator-one endpoint is included; the order increases by three.
example : fareyNumeratorCount 5 1 = 5 := by
  change fareyNumeratorCount (2 + 3 * 1) 1 = 5
  rw [fareyNumeratorCount_add_mul 1 2 3 (by decide) (by decide)]
  decide +kernel

example : fareyNumeratorCount (16 + 0 * 6) 6 = fareyNumeratorCount 16 6 :=
  fareyNumeratorCount_add_mul 6 16 0 (by decide) (by decide)
