/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MeteredParkingDiagonalChoose

open MetaMathlibExt

-- The smallest allowed diagonal, computed directly from the parking rule.
example : meteredParkingCount 1 3 3 = 21 := by decide

-- Evaluate the binomial formula at the next diagonal, where the base is no longer one.
example : meteredParkingCount 1 4 4 = 209 := by
  rw [meteredParkingCount_one_diag (by decide)]
  decide
