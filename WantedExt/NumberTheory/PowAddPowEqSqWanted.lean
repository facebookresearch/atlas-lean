/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On the Diophantine equation `n^x + (5p)^y = z^2`

Statements from Suton Tadee, "On the Diophantine
Equation `n^x + (5p)^y = z^2`", *INTEGERS* 24 (2024),
Article A68
(<https://math.colgate.edu/~integers/vol24.html>).

Equation (1) is `n^x + (5p)^y = z^2` in nonnegative
integers, with `p` an odd prime. All solution
classifications and non-existence claims below were
checked by brute-force search over small ranges; the
extraction's flattened `√` set-builders are read as
`z^2 = n + 1` resp. `z^2 = 5p + 1` side conditions.

Not stated (see the source audit table): Theorem 1
(the special case `u^2 - v^q = 1` of Mihăilescu's
theorem, already covered by
`MathlibExt.NumberTheory.MihailescuWanted.mihailescu`).

Proved in `MathlibExt.NumberTheory.PowAddPowEqSq`:
Lemma 1, case `n = 2`
(`MetaMathlibExt.two_pow_add_one_eq_sq`).

Proved in `MathlibExt.NumberTheory.ThreePowAddThirtyfivePow`,
which this module imports: the case `x = 0`
(`one_add_pow_eq_sq`) and the case `n = 3`,
`p = 7` (`three_pow_add_thirtyfive_pow`).

Proved in `MathlibExt.NumberTheory.PowAddPowEqSqModFourOne`,
which this module imports: the absence of
solutions when `n ≡ p ≡ 1 (mod 4)`
(`no_solution_mod_four_one`).

The parity restriction when `n ≡ p ≡ 3 (mod 4)` is proved in
`MathlibExt.NumberTheory.PowAddPowEqSqOppositeParity`.

Proved in `MathlibExt.NumberTheory.PowAddPowEqSqTwoPow`,
which this module imports: Theorem 3, the solutions
for `n = 2` and `p ≡ 3 (mod 4)` (`two_pow_solutions`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.PowAddPowEqSq
public import MathlibExt.NumberTheory.PowAddPowEqSqEvenExponent
public import MathlibExt.NumberTheory.PowAddPowEqSqModFourOne
public import MathlibExt.NumberTheory.PowAddPowEqSqModSixty
public import MathlibExt.NumberTheory.PowAddPowEqSqOppositeParity
public import MathlibExt.NumberTheory.PowAddPowEqSqTwoPow
public import MathlibExt.NumberTheory.ThreePowAddThirtyfivePow
public import MathlibExt.NumberTheory.TwoPowAddFifteenPow

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

/-- **Solutions of $n^x + 1 = z^2$ for $n \ne 2$.** Let $n \ge 1$ be a natural number with
$n \ne 2$. For natural numbers $x$ and $z$, $n^x + 1 = z^2$ holds if and only if $x = 1$ and
$z^2 = n + 1$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Lemma 1. -/
theorem_wanted pow_add_one_eq_sq (n x z : ℕ) (hn : 1 ≤ n)
    (hn2 : n ≠ 2) :
    n ^ x + 1 = z ^ 2 ↔ x = 1 ∧ z ^ 2 = n + 1

/-- **Corollary 2** (Moonchaisook et al.): the
Diophantine equation `(5^n)^x + (4^m p + 1)^y = z^2`
has no nonnegative integer solution for `m ≥ 1`.
The paper assumes `p` an odd prime and `n ≥ 1`;
neither is needed (both bases are `≡ 1 (mod 4)`), so
`p` and `n` are arbitrary naturals here. The
hypothesis `m ≥ 1` is needed: `5^1 + (4^0·3 + 1)^1 = 3^2`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 2. -/
theorem_wanted five_pow_add_four_pow_mul_add_one_ne_sq
    (p m n x y z : ℕ) (hm : 1 ≤ m) :
    (5 ^ n) ^ x + (4 ^ m * p + 1) ^ y ≠ z ^ 2

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
