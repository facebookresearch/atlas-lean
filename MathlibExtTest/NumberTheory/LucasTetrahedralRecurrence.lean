/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasTetrahedralRecurrence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

private theorem ordinaryBracket (n : ℕ) : lucasBracketAux 2 (-1) n = (n : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [lucasBracketAux]
  | one => norm_num [lucasBracketAux]
  | more n ih0 ih1 =>
    rw [lucasBracketAux, ih0, ih1]
    push_cast
    ring

private noncomputable def ordinaryParameters : LucasParameters where
  s := 2
  t := -1
  s_ne_zero := by norm_num
  t_ne_zero := by norm_num
  bracket_ne_zero n hn := by
    rw [ordinaryBracket]
    exact_mod_cast hn

-- At n = 0 the out-of-range tetrahedral term drops out.
example (P : LucasParameters) :
    lucasnomial P 3 3 = lucasBracket P 1 * lucasnomial P 2 2 := by
  simpa [lucasnomial_eq_zero_of_lt P (by decide : 2 < 3)] using lucasTetrahedral_recurrence P 0

-- For s = 2 and t = -1, the recurrence gives the ordinary tetrahedral number at n = 3.
example : lucasnomial ordinaryParameters 5 3 = 10 := by
  rw [lucasTetrahedral_recurrence ordinaryParameters 2]
  norm_num [lucasnomial, lucasFactorial, Finset.prod_range_succ, lucasBracket,
    lucasBracketAux, ordinaryParameters]

#print axioms lucasTetrahedral_recurrence

end MetaMathlibExt
