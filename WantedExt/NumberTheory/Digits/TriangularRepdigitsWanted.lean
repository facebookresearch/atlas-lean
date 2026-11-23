/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Triangular numbers with a single repeated digit

Statement from Christian Hercher and Karl Fegert, "Triangular Numbers
With a Single Repeated Digit", *Journal of Integer Sequences* 28
(2025), Article 25.2.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Hercher/hercher33.html>).

Triangular numbers are indexed from `1`, as in the source's list. The
digit condition says that every entry of `Nat.digits 10 m` is one digit
`d` that actually occurs in the list.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Digits.TriangularRepdigitsWanted

/-- **Triangular repdigits.** The positive triangular numbers $n(n+1)/2$ with $n \ge 1$ whose
decimal representation consists of a single repeated digit are exactly $1$, $3$, $6$, $55$, $66$
and $666$.

Source: Christian Hercher and Karl Fegert, "Triangular Numbers With a
Single Repeated Digit", Theorem 1 (TeX label `Thm:main`). -/
theorem_wanted triangular_numbers_single_repeated_digit :
    {m : ℕ |
      (∃ n : ℕ, 1 ≤ n ∧ 2 * m = n * (n + 1)) ∧
        ∃ d : ℕ, d < 10 ∧ d ∈ Nat.digits 10 m ∧
          ∀ a ∈ Nat.digits 10 m, a = d} =
      {1, 3, 6, 55, 66, 666}

end MathlibExt.NumberTheory.Digits.TriangularRepdigitsWanted
