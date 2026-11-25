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
# Weighted difference of squared Lucas triangular numbers

The difference between two consecutive squared Lucas triangular numbers with weight
`t ^ 2` is a multiple of the cube of the intervening Lucas bracket.
-/

namespace MetaMathlibExt

namespace lucasTriangular_sq_sub_sq

private theorem lucasnomial_two (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 1) 2 = lucasBracket P n * lucasBracket P (n + 1) / P.s := by
  cases n with
  | zero => simp [lucasnomial, lucasBracket, lucasBracketAux]
  | succ n =>
    have htwo : lucasFactorial P 2 = P.s := by
      simp [lucasFactorial, Finset.prod_range_succ, lucasBracket, lucasBracketAux]
    have hsucc (k : ℕ) :
        lucasFactorial P (k + 1) = lucasFactorial P k * lucasBracket P (k + 1) :=
      Finset.prod_range_succ _ _
    rw [lucasnomial, ite_eq_left (by omega), show n.succ + 1 - 2 = n by omega, htwo,
      hsucc (n + 1), hsucc n]
    field_simp [lucasFactorial_ne_zero, P.s_ne_zero]

end lucasTriangular_sq_sub_sq

open lucasTriangular_sq_sub_sq in
/-- **Weighted difference of consecutive squared Lucas triangular numbers.** Let $(s, t)$ be
nondegenerate Lucas parameters, with Lucas brackets $\{n\}_{s,t}$ and Lucasnomial coefficients
$\binom{n}{k}_{s,t}$. For every natural number $n$,
$$\binom{n+2}{2}_{s,t}^{2} - t^2 \binom{n+1}{2}_{s,t}^{2} =
\frac{\{n+2\}_{s,t} + t \{n\}_{s,t}}{s} \{n+1\}_{s,t}^{3}.$$

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 4
(`jis-2025-25.5.6-thm-4`). -/
public theorem lucasTriangular_sq_sub_sq (P : LucasParameters) (n : ℕ) :
    lucasnomial P (n + 2) 2 ^ 2 - P.t ^ 2 * lucasnomial P (n + 1) 2 ^ 2 =
      (lucasBracket P (n + 2) + P.t * lucasBracket P n) / P.s * lucasBracket P (n + 1) ^ 3 := by
  rw [lucasnomial_two P (n + 1), lucasnomial_two P n]
  rw [show lucasBracket P (n + 2) = P.s * lucasBracket P (n + 1) + P.t * lucasBracket P n
    from rfl]
  field_simp [P.s_ne_zero]
  ring

end MetaMathlibExt
