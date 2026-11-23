/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleStrings

open MetaMathlibExt

-- At n = b, the input (3, 1) in base four has the maximal incoming carry.
example {x y : ℕ} (h : IsHoeySloaneStep 4 4 x y (3, 1)) : x = 3 ∧ y = 1 :=
  isHoeySloaneStep_unique 4 4 le_rfl h (by decide)

-- With n > b, one input can label two distinct loops.
example : IsHoeySloaneStep 3 1 0 0 (0, 0) ∧ IsHoeySloaneStep 3 1 1 1 (0, 0) := by
  decide
