/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LonelySinglesLowerBound

open MetaMathlibExt

-- The second sum is empty at the lower endpoint.
example : (1 : ℚ) ≤ lonelySinglesCount 2 := by
  convert lonelySinglesCount_ge_sum 2 (by decide) using 1
  decide +kernel

-- For five points, the one-singleton sum includes the three-block partitions.
example : (21 : ℚ) ≤ lonelySinglesCount 5 := by
  convert lonelySinglesCount_ge_sum 5 (by decide) using 1
  decide +kernel
