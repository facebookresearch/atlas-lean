/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Diophantine equation `Q_n^x + Q_{n+1}^x = y^2`

Statements from Sérgio Mendes, "The Diophantine
Equation `Q_n^x + Q_{n+1}^x = y^2`", *INTEGERS* 26
(2026), Article A72
(<https://math.colgate.edu/~integers/vol26.html>).

The Pell numbers `P_n` and Pell–Lucas numbers `Q_n`
are the existing `MetaMathlibExt.pellNumber`
(`0, 1, 2, 5, …`) and
`MetaMathlibExt.pellLucasSequence` (`1, 1, 3, 7, …`),
matching the paper's normalizations. All statements
were checked numerically on initial ranges (square
terms and gcds for `n < 200`; the two Diophantine
statements on bounded grids, where `(n, x, y) = (1, 1, 2)`
is the unique solution of Theorem 2).

Not stated (see the source audit table): Lemma 1,
whose exponents are lost in the extracted statement.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.PellLucasSequence
public import MathlibExt.NumberTheory.PellNumberSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PellLucasDiophantineWanted

/-- **Lemma 2**: the only square terms in the
Pell–Lucas sequence are `Q_0 = 1` and `Q_1 = 1`.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 2. -/
theorem_wanted pellLucasSequence_isSquare_iff (n : ℕ) :
    IsSquare (MetaMathlibExt.pellLucasSequence n) ↔
      n = 0 ∨ n = 1

/-- **Lemma 3**: for every nonnegative integer `n`,
`gcd(P_n, Q_n) = 1`, where `P_n` and `Q_n` are the Pell
and Pell–Lucas numbers.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 3. -/
theorem_wanted gcd_pellNumber_pellLucasSequence (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellNumber n)
      (MetaMathlibExt.pellLucasSequence n) = 1

/-- **Lemma 4**: for every nonnegative integer `n`,
`gcd(Q_n, Q_{n+1}) = 1`.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Lemma 4. -/
theorem_wanted gcd_pellLucasSequence_succ (n : ℕ) :
    Nat.gcd (MetaMathlibExt.pellLucasSequence n)
      (MetaMathlibExt.pellLucasSequence (n + 1)) = 1

/-- **Theorem 1**: the equation `x^n + y^n = z^2` has
no nontrivial primitive solutions for `n ≥ 4`.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Theorem 1. -/
theorem_wanted pow_add_pow_ne_sq (n x y z : ℕ)
    (hn : 4 ≤ n) (hx : 0 < x) (hy : 0 < y)
    (hxy : Nat.Coprime x y) :
    x ^ n + y ^ n ≠ z ^ 2

/-- **Theorem 2**: the Diophantine equation
`Q_n^x + Q_{n+1}^x = y^2`, where `Q_n` is the `n`-th
Pell–Lucas number, has as its only solution in
nonnegative integers `(n, x, y) = (1, 1, 2)`.

Source: Sérgio Mendes, "The Diophantine Equation
`Q_n^x + Q_{n+1}^x = y^2`", Theorem 2. -/
theorem_wanted pellLucasSequence_pow_add_pow_eq_sq
    (n x y : ℕ) :
    MetaMathlibExt.pellLucasSequence n ^ x +
        MetaMathlibExt.pellLucasSequence (n + 1) ^ x
        = y ^ 2 ↔
      n = 1 ∧ x = 1 ∧ y = 2

end MathlibExt.NumberTheory.PellLucasDiophantineWanted
