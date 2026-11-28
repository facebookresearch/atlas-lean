/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperLeonardoHyperFibonacci

open MetaMathlibExt

-- The correction term is one at order zero and at index zero.
example : hyperLeonardo 0 4 = 9 := by
  rw [hyperLeonardo_eq_hyperFibonacci (r := 0) (n := 4)]
  decide

example : hyperLeonardo 3 0 = 1 := by
  rw [hyperLeonardo_eq_hyperFibonacci (r := 3) (n := 0)]
  decide

-- At positive order and index, the correction is not constant: 2 * 7 - 6 = 8.
example : hyperLeonardo 2 2 = 8 := by
  rw [hyperLeonardo_eq_hyperFibonacci (r := 2) (n := 2)]
  decide
