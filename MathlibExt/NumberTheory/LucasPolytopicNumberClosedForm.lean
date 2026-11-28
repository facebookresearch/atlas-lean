/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasPolytopicNumber
import Mathlib.Tactic.LinearCombination

/-!
# Closed form for real Lucas brackets

For nondegenerate real Lucas parameters $(s, t)$ and real numbers $x, y$ with $x + y = s$ and
$xy = -t$, the bracket at each natural index $n$ satisfies $(x-y)\{n\}_{s,t} = x^n-y^n$.
Writing the formula without division makes it valid when the roots coincide, too.

## References

* Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
  Journal of Integer Sequences 28 (2025), Article 25.5.6, pp. 1–19, §2 (Lucas recurrence and roots).
* The identity was previously `bracket_closed` in
  `MathlibExt.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc`.
-/

namespace MetaMathlibExt

/-- **Closed form for the Lucas brackets.** Let $(s,t)$ be nondegenerate real Lucas parameters,
and let $x,y$ be real numbers satisfying $x+y=s$ and $xy=-t$. Then for every natural number $n$,
$(x-y)\{n\}_{s,t}=x^n-y^n$. If the roots coincide, both sides are zero. -/
public theorem lucasBracket_closed_form (P : LucasParameters) (x y : ℝ)
    (hsum : x + y = P.s) (hprod : x * y = -P.t) (n : ℕ) :
    (x - y) * lucasBracket P n = x ^ n - y ^ n := by
  have hx : x ^ 2 = P.s * x + P.t := by linear_combination x * hsum - hprod
  have hy : y ^ 2 = P.s * y + P.t := by linear_combination y * hsum - hprod
  induction n using Nat.twoStepInduction with
  | zero => simp [lucasBracket, lucasBracketAux]
  | one => simp [lucasBracket, lucasBracketAux]
  | more n ih₀ ih₁ =>
    change (x - y) * (P.s * lucasBracket P (n + 1) + P.t * lucasBracket P n) = _
    rw [pow_succ x n, pow_succ y n] at ih₁
    rw [pow_add x n 2, pow_add y n 2, hx, hy]
    linear_combination P.s * ih₁ + P.t * ih₀

end MetaMathlibExt
