/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasnomialSum
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.lucasnomial_succ_eq_sum_lucasPolytopic

-- The double root 1 removes all weights and recovers the usual column sum.
example (P : LucasParameters) (hs : P.s = 2) (ht : P.t = -1) (n d : ℕ) (hn : 1 ≤ n) :
    lucasnomial P (n + d) (d + 1) =
      ∑ k ∈ Finset.Icc 1 n, lucasnomial P (k + d - 1) d := by
  simpa using (lucasnomial_succ_eq_sum_lucasPolytopic P 1 1
    (by norm_num [hs]) (by norm_num [ht]) n d hn).1

-- At degree zero, reversing the roots gives the same quadratic for the third bracket.
example (P : LucasParameters) (x y : ℝ) (hs : x + y = P.s) (ht : x * y = -P.t) :
    lucasnomial P 3 1 = y ^ 2 + y * x + x ^ 2 := by
  have h := (lucasnomial_succ_eq_sum_lucasPolytopic P x y hs ht 3 0 (by decide)).2
  have hzero (n : ℕ) : lucasnomial P n 0 = 1 := by
    simp [lucasnomial, show lucasFactorial P 0 = 1 by rfl, lucasFactorial_ne_zero]
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide] at h
  simpa [Finset.sum_insert, hzero, add_assoc] using h

#print axioms MetaMathlibExt.lucasnomial_succ_eq_sum_lucasPolytopic

end MetaMathlibExt.lucasnomial_succ_eq_sum_lucasPolytopic
