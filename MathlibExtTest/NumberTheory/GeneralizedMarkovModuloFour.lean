/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedMarkovModuloFour
import Mathlib.Tactic.NormNum

open MetaMathlibExt

example : 2 % 4 = 2 := by
  have hb : IsGenMarkovNumber 2 4 := ⟨1, 1, by norm_num [IsGenMarkovTriple]⟩
  exact mod_four_eq_two_of_four_dvd_genMarkovNumber hb (by decide)

example : 6 % 4 = 2 := by
  have hb : IsGenMarkovNumber 6 8 := ⟨1, 1, by norm_num [IsGenMarkovTriple]⟩
  exact mod_four_eq_two_of_four_dvd_genMarkovNumber hb (by decide)
