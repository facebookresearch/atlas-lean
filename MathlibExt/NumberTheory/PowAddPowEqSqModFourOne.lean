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

private theorem sum_pow_ne_sq_of_mod_four_one {a b : ℕ} (ha : a % 4 = 1) (hb : b % 4 = 1)
    (x y z : ℕ) : a ^ x + b ^ y ≠ z ^ 2 := by
  intro h
  have hx : a ^ x % 4 = 1 := by rw [Nat.pow_mod, ha, Nat.one_pow]
  have hy : b ^ y % 4 = 1 := by rw [Nat.pow_mod, hb, Nat.one_pow]
  have hz : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
    have hz4 : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases hz4 with h4 | h4 | h4 | h4 <;> rw [Nat.pow_mod, h4] <;> decide
  omega

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
  exact sum_pow_ne_sq_of_mod_four_one hn (by omega) x y z h

/-- **Corollary 2** (Moonchaisook et al.): the
Diophantine equation `(5^n)^x + (4^m p + 1)^y = z^2`
has no nonnegative integer solution for `m ≥ 1`.
The paper assumes `p` an odd prime and `n ≥ 1`;
neither is needed (both bases are `≡ 1 (mod 4)`), so
`p` and `n` are arbitrary naturals here. The
hypothesis `m ≥ 1` is needed: `5^1 + (4^0·3 + 1)^1 = 3^2`.

Source: Suton Tadee, "On the Diophantine Equation
`n^x + (5p)^y = z^2`", Corollary 2. -/
theorem five_pow_add_four_pow_mul_add_one_ne_sq
    (p m n x y z : ℕ) (hm : 1 ≤ m) :
    (5 ^ n) ^ x + (4 ^ m * p + 1) ^ y ≠ z ^ 2 := by
  have h₁ : 5 ^ n % 4 = 1 := by
    rw [Nat.pow_mod, show 5 % 4 = 1 by decide, Nat.one_pow]
  have h₂ : (4 ^ m * p + 1) % 4 = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    change (4 ^ (k + 1) * p + 1) % 4 = 1
    have hmul : (4 ^ (k + 1) * p) % 4 = 0 := by
      rw [pow_succ, mul_right_comm, Nat.mul_mod]
      simp
    rw [Nat.add_mod, hmul]
  exact sum_pow_ne_sq_of_mod_four_one h₁ h₂ x y z

end MathlibExt.NumberTheory.PowAddPowEqSqWanted
