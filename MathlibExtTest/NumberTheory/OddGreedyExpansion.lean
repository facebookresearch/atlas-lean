/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.OddGreedyExpansion

open MathlibExt.NumberTheory.OddGreedyExpansionWanted

-- The empty sum permits any nonzero integer denominator.
example (b : ℤ) (hb : b ≠ 0) : Even (0 : ℤ) :=
  even_num_of_even_sum_unit_fractions 0 Even.zero Fin.elim0 (fun i => i.elim0) 0 b hb (by simp)

-- Both odd unit denominators can coincide, and the representing fraction can be unreduced.
example : Even (-4 : ℤ) := by
  apply even_num_of_even_sum_unit_fractions 2 (by decide) (fun _ => 3)
    (fun _ => by decide) (-4) (-6) (by decide)
  norm_num [Fin.sum_univ_two]
