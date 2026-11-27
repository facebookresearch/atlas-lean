/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CatalanDigammaNatSpecialization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- At the smallest allowed index the two harmonic sums are empty.
example :
    ∑' n : ℕ, (catalan n : ℝ) / (((n + 1).choose n : ℝ) * ((n + 1).centralBinom : ℝ)) =
      Real.log 2 := by
  rw [tsum_catalan_div_choose_mul_centralBinom (by decide : 0 < 1)]
  norm_num [harmonic, Nat.centralBinom]
  ring

-- At the next index each harmonic sum contributes its first term.
example :
    ∑' n : ℕ, (catalan n : ℝ) / (((n + 2).choose n : ℝ) * ((n + 2).centralBinom : ℝ)) =
      Real.log 2 - 1 / 2 := by
  rw [tsum_catalan_div_choose_mul_centralBinom (by decide : 0 < 2)]
  norm_num [harmonic, Nat.centralBinom, Nat.choose]
  ring
