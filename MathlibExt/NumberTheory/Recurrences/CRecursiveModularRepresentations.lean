/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Notation

/-!
# Mod-mod representations of C-recursive sequences: a floor-quotient lemma

M. Prunescu and J. M. Shunia derive mod-mod representations of C-recursive sequences, made of two
successive remainder computations, from div-mod representations, which reduce the floor of a
quotient of two exponential polynomials modulo a power of the base. Their principal tool is a
lemma on iterated remainders, whose proof rests on easy remarks of modular arithmetic. This module
proves the first of these remarks.

## Main results

* `MetaMathlibExt.neg_ediv_eq_ediv_add_one_of_not_dvd`: for integers `A ≥ 1` and `B ≥ 2` such
  that `B` does not divide `A`, `-((-A) / B) = A / B + 1`, that is,
  `-⌊-A / B⌋ = ⌊A / B⌋ + 1`.

## Implementation notes

The paper's floor quotient `⌊A / B⌋` is Lean's integer division `A / B`, namely `Int.ediv`,
which rounds down when the divisor is positive. The proof specializes the core lemma
`Int.neg_ediv`, `(-a) / b = -(a / b) - if b ∣ a then 0 else b.sign`. The paper's hypothesis
`1 ≤ A` is kept in the statement but is not needed, and `2 ≤ B` is used only through `0 < B`.
Since `-((-A) / B)` is the ceiling of `A / B` (compare `Rat.ceil_intCast_div_natCast`), the
lemma says that the ceiling of a quotient that is not an integer is its floor plus one.

## References

* M. Prunescu and J. M. Shunia, *On modular representations of C-recursive integer sequences*,
  arXiv:2502.16928 (2025), Lemma 2.2 (the preprint numbers its results by section).
-/

public section

namespace MetaMathlibExt

-- The paper's hypothesis `hA : 1 ≤ A` is kept for fidelity to the source; the proof does not
-- use it.
set_option linter.unusedVariables false in
/--
**Floor quotient of a negated non-multiple.** Let $A$ and $B$ be integers with $A \ge 1$ and
$B \ge 2$ such that $B$ does not divide $A$. Then
$-\lfloor -A/B \rfloor = \lfloor A/B \rfloor + 1$.

Source: M. Prunescu and J. M. Shunia, *On Modular Representations of C-Recursive Integer Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.3, Lemma 4.
-/
theorem neg_ediv_eq_ediv_add_one_of_not_dvd
    (A B : ℤ) (hA : 1 ≤ A) (hB : 2 ≤ B) (hndvd : ¬ B ∣ A) :
    -((-A) / B) = A / B + 1 := by
  rw [Int.neg_ediv, ite_eq_right hndvd, Int.sign_eq_one_of_pos (by omega)]
  omega

end MetaMathlibExt

end
