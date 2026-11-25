/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Central
import MathlibExt.NumberTheory.CentralBinomProductEquationOne
import MathlibExt.NumberTheory.CentralBinomProductEquationSmall
import MathlibExt.NumberTheory.CentralBinomProductInequality

/-!
# Central binomial products with index sum at most ten

For positive indices with `a + b ≤ 10`, Allen's product equation holds exactly when
the shift `x` and the index `a` both equal one.
-/

namespace MetaMathlibExt

/-- **Central binomial products with $a + b \le 10$.** Let $x$, $a$, $b$ be positive integers
with $a + b \le 10$. Then $\binom{2(a+b)}{a+b} = \binom{2a}{a}\binom{x+2b}{b}$ if and only if
$x = 1$ and $a = 1$.

Source: Meaghan Allen, *Solvability of $\binom{2k}{k} = \binom{2a}{a}\binom{x+2b}{b}$*,
INTEGERS 26 (2026), Article A26, Lemma 1 (`integers-2026-A26-lem-1`). -/
public theorem centralBinom_add_eq_centralBinom_mul_choose_iff_of_le_ten (x a b : ℕ)
    (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hk : a + b ≤ 10) :
    (a + b).centralBinom = a.centralBinom * (x + 2 * b).choose b ↔ x = 1 ∧ a = 1 := by
  by_cases hax : a ≤ x
  · exact (centralBinom_add_le_centralBinom_mul_choose_of_le x a b hx hb hax).2
  obtain rfl | hx' := eq_or_lt_of_le (show 1 ≤ x from hx)
  · simpa using centralBinom_add_eq_centralBinom_mul_choose_one_iff a b ha hb
  exact iff_of_false (centralBinom_add_ne_of_two_le_of_small x a b hx' ha hb (by omega)
    (by omega)) (by omega)

end MetaMathlibExt
