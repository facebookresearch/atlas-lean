/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.CRecursiveRemainderIncrement

open MetaMathlibExt

-- At modulus two, only remainder zero can be incremented without wrapping.
example : (0 + 1) % 2 = 0 % 2 + 1 :=
  add_one_mod_eq_mod_add_one_of_ne 0 2 (by decide) (by decide)

-- Consecutive dividends on either side of the cutoff modulo five.
example : (8 + 1) % 5 = 8 % 5 + 1 :=
  add_one_mod_eq_mod_add_one_of_ne 8 5 (by decide) (by decide)

example : (9 + 1) % 5 ≠ 9 % 5 + 1 := by decide
