/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

/-! # Composing a Pell-type solution with a norm-one unit
-/

/--
**Composing a Pell-type solution with a norm-one unit.** Let $a, b, c, T, U, x, y$ be integers
with $a T^2 - b U^2 = c$ and $x^2 - ab y^2 = 1$. Then the pair $(T x + b U y, a T y + U x)$ is
again a solution: $a (T x + b U y)^2 - b (a T y + U x)^2 = c$.

The source iterates this step, assuming that $ab > 1$ is not a square, to obtain infinitely many
solutions. That conclusion needs further nondegeneracy hypotheses (for $T = U = c = 0$ every
iterate is $(0, 0)$); the single step is the multiplicativity of the norm form and needs no
hypotheses beyond the two equations.

Proves `Wanted` entry `pellType_solution_mul_unit`.

Source: E. L. Roettger and H. C. Williams, "Some Remarks Concerning the
Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025),
Article 25.2.5, Theorem (label PellTheorem, an observation of Euler),
equation (label DioEq), lines 605–614,
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex>
-/
theorem pellType_solution_mul_unit
    (a b c T U x y : ℤ)
    (hsol : a * T ^ 2 - b * U ^ 2 = c)
    (hunit : x ^ 2 - a * b * y ^ 2 = 1) :
    a * (T * x + b * U * y) ^ 2 - b * (a * T * y + U * x) ^ 2 = c := by
  linear_combination (x ^ 2 - a * b * y ^ 2) * hsol + c * hunit

end MetaMathlibExt
