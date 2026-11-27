/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SylvesterSequenceModTen

open MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

-- The first positive even index.
example : sylvesterNumber 2 % 10 = 7 :=
  sylvester_even_index_mod_ten 1 (by decide)

-- Two applications of the recurrence after S₂ give S₄ = 1807.
example : sylvesterNumber 4 % 10 = 7 := by decide +kernel

example : sylvesterNumber 6 % 10 = 7 :=
  sylvester_even_index_mod_ten 3 (by decide)
