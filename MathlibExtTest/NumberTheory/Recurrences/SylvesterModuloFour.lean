/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SylvesterModuloFour

open MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

example : sylvesterNumber 0 % 4 ≠ 3 := by decide

example : sylvesterNumber 1 % 4 = 3 :=
  sylvester_modEq_three_mod_four (n := 1) (hn := by decide)

example (k : ℕ) : sylvesterNumber (k + 2) % 4 = 3 :=
  sylvester_modEq_three_mod_four (k + 2) (by omega)
