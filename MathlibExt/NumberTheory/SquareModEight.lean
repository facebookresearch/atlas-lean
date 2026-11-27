/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# Squares modulo 8 and 16

Squares are `0`, `1` or `4` modulo 8, so numbers that are `3` or `6` modulo 8 are not squares
and a number that is `6` modulo 8 is not a square plus a square. Odd squares are `1` or `9`
modulo 16 according to the residue modulo 8.
-/

@[expose] public section

namespace Nat

/-- **Squares of natural numbers modulo 8.** For every natural number $r$, the remainder of $r^2$
on division by $8$ is $0$, $1$ or $4$. -/
theorem sq_mod_eight (r : ℕ) :
    r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by
  have h8 : r % 8 = 0 ∨ r % 8 = 1 ∨ r % 8 = 2 ∨ r % 8 = 3 ∨
      r % 8 = 4 ∨ r % 8 = 5 ∨ r % 8 = 6 ∨ r % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;>
    rw [pow_two, Nat.mul_mod, h] <;> decide

/-- **Numbers congruent to 3 mod 8 are not squares.** If a natural number $n$ satisfies
$n \equiv 3 \pmod 8$, then $n$ is not the square of a natural number. -/
theorem not_isSquare_of_mod_eight_eq_three {n : ℕ} (h : n % 8 = 3) : ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr := sq_mod_eight r
  rw [pow_two] at hr
  omega

/-- **Numbers congruent to 6 mod 8 are not squares.** If a natural number $n$ satisfies
$n \equiv 6 \pmod 8$, then $n$ is not the square of a natural number. -/
theorem not_isSquare_of_mod_eight_eq_six {n : ℕ} (h : n % 8 = 6) : ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr := sq_mod_eight r
  rw [pow_two] at hr
  omega

/-- **A number that is 6 mod 8 minus a smaller square is not a square.** Let $N$ and $k$ be
natural numbers with $N \equiv 6 \pmod 8$ and $k^2 < N$. Then $N - k^2$ is not the square of a
natural number. -/
theorem not_isSquare_sub_sq_of_mod_eight_eq_six {N k : ℕ} (hN : N % 8 = 6)
    (hk : k ^ 2 < N) : ¬ IsSquare (N - k ^ 2) := by
  rintro ⟨j, hj⟩
  have hNN : N = k ^ 2 + j ^ 2 := by
    have hle : k ^ 2 ≤ N := Nat.le_of_lt hk
    have hsa := Nat.sub_add_cancel hle
    rw [hj, ← pow_two j] at hsa
    omega
  have hk8 := sq_mod_eight k
  have hj8 := sq_mod_eight j
  have hmod : (k ^ 2 + j ^ 2) % 8 = 6 := by
    rw [← hNN]
    exact hN
  rw [Nat.add_mod] at hmod
  rcases hk8 with hk8 | hk8 | hk8 <;> rcases hj8 with hj8 | hj8 | hj8 <;>
    rw [hk8, hj8] at hmod <;> norm_num at hmod

/-- **Odd squares modulo 16.** For every odd natural number $k$, either $k^2 \equiv 1 \pmod{16}$
and $k \equiv 1$ or $7 \pmod 8$, or $k^2 \equiv 9 \pmod{16}$ and $k \equiv 3$ or $5 \pmod 8$. -/
theorem sq_mod_sixteen_of_odd (k : ℕ) (hk : Odd k) :
    (k ^ 2 % 16 = 1 ∧ (k % 8 = 1 ∨ k % 8 = 7)) ∨
    (k ^ 2 % 16 = 9 ∧ (k % 8 = 3 ∨ k % 8 = 5)) := by
  have hlt : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hpow : k ^ 2 % 16 = (k % 16) ^ 2 % 16 := Nat.pow_mod k 2 16
  have h8 : k % 8 = (k % 16) % 8 := by omega
  have hodd16 : (k % 16) % 2 = 1 := by
    have hodd : k % 2 = 1 := Nat.odd_iff.mp hk
    omega
  revert hpow h8 hodd16 hlt
  generalize k % 16 = q
  intro hpow h8 hodd16 hlt
  interval_cases q <;> norm_num at hpow h8 hodd16 ⊢ <;> omega

end Nat

namespace Int

/-- **Squares of integers modulo 8.** For every integer $x$, the remainder of $x^2$ on division
by $8$, taken in $\{0, 1, \dots, 7\}$, is $0$, $1$ or $4$. -/
theorem sq_emod_eight (x : ℤ) :
    x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
  have h8 : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨
      x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨ x % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;>
    rw [pow_two, Int.mul_emod, h] <;> decide

end Int

end
