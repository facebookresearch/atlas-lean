/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasPolytopicNumber
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Recurrence for Lucas tetrahedral numbers

Two steps of the Lucas bracket recurrence give a relation between consecutive
Lucas tetrahedral numbers and a Lucas triangular number.
-/

namespace MetaMathlibExt

private theorem bracket_succ_succ (P : LucasParameters) (n : ℕ) :
    lucasBracket P (n + 2) = P.s * lucasBracket P (n + 1) + P.t * lucasBracket P n := rfl

/-- **Recurrence for the Lucas tetrahedral numbers.** Let $(s, t)$ be nondegenerate Lucas
parameters, and write $\{n\}_{s,t}$ for the Lucas brackets and $\binom{n}{k}_{s,t}$ for the
Lucasnomial coefficients. For every natural number $n$,
$$\binom{n+3}{3}_{s,t} = st\binom{n+2}{3}_{s,t} + \{n+1\}_{s,t}\binom{n+2}{2}_{s,t}.$$

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 7
(`jis-2025-25.5.6-thm-7`). -/
public theorem lucasTetrahedral_recurrence (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 3) 3 =
      P.s * P.t * lucasnomial P (n + 2) 3 + lucasBracket P (n + 1) * lucasnomial P (n + 2) 2 := by
  cases n with
  | zero =>
    rw [lucasnomial_eq_zero_of_lt P (by decide : 2 < 3)]
    simp [lucasnomial, lucasBracket, lucasBracketAux, lucasFactorial_ne_zero]
  | succ n =>
    change lucasnomial P (n + 4) 3 =
      P.s * P.t * lucasnomial P (n + 3) 3 + lucasBracket P (n + 2) * lucasnomial P (n + 3) 2
    have hbracket : lucasBracket P (n + 4) =
        lucasBracket P 3 * lucasBracket P (n + 2) + P.s * P.t * lucasBracket P (n + 1) := by
      have hthree : lucasBracket P 3 = P.s ^ 2 + P.t := by
        simp [lucasBracket, lucasBracketAux, pow_two]
      rw [bracket_succ_succ P (n + 2), bracket_succ_succ P (n + 1), hthree]
      ring
    simp (disch := omega) only [lucasnomial, ite_eq_left, Nat.add_sub_cancel,
      show n + 4 - 3 = n + 1 by omega, show n + 3 - 2 = n + 1 by omega]
    rw [lucasFactorial_succ P (n + 3), lucasFactorial_succ P 2, lucasFactorial_succ P n, hbracket]
    field_simp [lucasFactorial_ne_zero, lucasBracket_ne_zero P (Nat.succ_ne_zero _)]
    ring

end MetaMathlibExt
