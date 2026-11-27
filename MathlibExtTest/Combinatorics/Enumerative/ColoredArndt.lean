/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ColoredArndt

open MetaMathlibExt

-- The empty composition contributes the constant polynomial one.
example : PowerSeries.coeff 0 coloredArndtGF = 1 := by
  have h : coloredArndtCount 0 0 = 1 := by decide
  simp [coloredArndtGF, h]

-- Two descending pairs require weight at least six. At weight six both pairs are (2, 1).
example : coloredArndtCount 5 4 = 0 ∧ coloredArndtCount 6 4 = 4 := by
  decide
