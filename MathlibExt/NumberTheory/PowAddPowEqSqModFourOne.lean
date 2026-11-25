/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# No solutions of `n^x + (5p)^y = z^2` when `n ≡ p ≡ 1 (mod 4)`

The ATLAS wiki attributes this non-existence result to Suton Tadee's "On the Diophantine
Equation `n^x + (5p)^y = z^2`", *INTEGERS* 24 (2024), Article A68
(<https://math.colgate.edu/~integers/vol24.html>).

If `n ≡ 1 (mod 4)` and `p ≡ 1 (mod 4)`, then `5p ≡ 1 (mod 4)`, so every power of `n` and every
power of `5p`, the zeroth powers included, is `≡ 1 (mod 4)`. Their sum is then `≡ 2 (mod 4)`,
whereas every square is `≡ 0` or `1 (mod 4)`. The argument uses only the residues of `n` and `p`
modulo `4`, not the primality of `p`.
-/

public section

namespace MathlibExt.NumberTheory.PowAddPowEqSqWanted

-- The source assumes that `p` is prime; the argument modulo `4` does not use it.
set_option linter.unusedVariables false in
/-- **No solutions of $n^x + (5p)^y = z^2$ when $n \equiv p \equiv 1 \pmod 4$.** Let $p$ be a
prime and $n$ a natural number with $n \equiv 1 \pmod 4$ and $p \equiv 1 \pmod 4$. Then there
are no natural numbers $x$, $y$, $z$ with $n^x + (5p)^y = z^2$.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Theorem 2. -/
theorem no_solution_mod_four_one (n p : ℕ) (hp : p.Prime)
    (hn : n % 4 = 1) (hp4 : p % 4 = 1) :
    ¬ ∃ x y z : ℕ, n ^ x + (5 * p) ^ y = z ^ 2 := by
  rintro ⟨x, y, z, h⟩
  -- Both bases are `1` modulo `4`, hence so are all their powers.
  have h5p : 5 * p % 4 = 1 := by omega
  have hx : n ^ x % 4 = 1 := by rw [Nat.pow_mod, hn, Nat.one_pow]
  have hy : (5 * p) ^ y % 4 = 1 := by rw [Nat.pow_mod, h5p, Nat.one_pow]
  -- Every square is `0` or `1` modulo `4`.
  have hz : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
    have hz4 : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases hz4 with h4 | h4 | h4 | h4 <;> rw [Nat.pow_mod, h4] <;> decide
  omega

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
