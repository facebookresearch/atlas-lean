/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SylvesterSequence

open MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

example : sylvesterNumber 1 % 36 ≠ 7 := by decide

example : sylvesterNumber 2 = 7 := by decide

example (k : ℕ) : sylvesterNumber (k + 2) % 36 = 7 :=
  sylvester_modEq_seven_mod_thirty_six (k + 2) (by omega)
