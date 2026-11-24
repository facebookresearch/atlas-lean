/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-! # Greatest common divisors of generalized Fermat numbers -/

namespace MetaMathlibExt

/-- **Greatest common divisors of generalized Fermat numbers.** For natural numbers $a$, $b$ and
$k$ write $F_k(a, b) = a^{b^k} + 1$, and let $a, b \ge 2$ and $m$, $n$ be natural numbers. If
$n < m$ and $a$ and $b$ are both even, then $\gcd(F_m(a, b), F_n(a, b)) = 1$. If $n < m$, $a$ is
odd and $b$ is even, then $\gcd(F_m(a, b), F_n(a, b)) = 2$. If $n \le m$ and $b$ is odd, then
$\gcd(F_m(a, b), F_n(a, b)) = F_n(a, b)$.

The source assumes $a, b > 2$ and $0 \le n \le m$; its proof uses only $a, b \ge 2$ and treats
$m > n$ ("Since $m > n$"), and the first two cases fail for $m = n$: for $a = b = 4$ and
$m = n = 0$ the gcd is $\gcd(5, 5) = 5$, and for $a = 3$, $b = 4$ and $m = n = 0$ it is
$\gcd(4, 4) = 4$.

Source: Klaška, *Several Notes on Jakóbczyk's Hypothesis on Fermat Numbers*,
INTEGERS 26 (2026), Article A77, Proposition 1 (`integers-2026-A77-prop-1`). -/
public theorem gcd_pow_pow_add_one {a b m n : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (n < m → Even a → Even b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = 1) ∧
      (n < m → Odd a → Even b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = 2) ∧
      (n ≤ m → Odd b → Nat.gcd (a ^ b ^ m + 1) (a ^ b ^ n + 1) = a ^ b ^ n + 1) := by
  let x := a ^ b ^ n
  have hgcd (hnm : n < m) (he : Even b) :
      Nat.gcd (a ^ b ^ m + 1) (x + 1) = Nat.gcd 2 (x + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm.le
    have hk : Even (b ^ k) := he.pow_of_ne_zero (by omega)
    obtain ⟨r, hr⟩ := hk.two_dvd
    -- Since (x + 1) divides (x² - 1), every even power of x is 1 modulo (x + 1).
    have hsq : 1 ≡ x ^ 2 [MOD x + 1] := by
      apply (Nat.modEq_iff_dvd' (Nat.one_le_pow 2 x (Nat.pow_pos (by omega)))).2
      simpa only [← Nat.sq_sub_sq, one_pow] using dvd_mul_right (x + 1) (x - 1)
    rw [pow_add, pow_mul, hr, pow_mul]
    simpa only [one_pow] using ((hsq.symm.pow r).add_right 1).gcd_eq
  refine ⟨?_, ?_, ?_⟩
  · intro hnm hae hbe
    rw [hgcd hnm hbe]
    exact (hae.pow_of_ne_zero (pow_ne_zero n (by omega))).add_one.coprime_two_left.gcd_eq_one
  · intro hnm hao hbe
    rw [hgcd hnm hbe]
    exact Nat.gcd_eq_left hao.pow.add_one.two_dvd
  · intro hnm hbo
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, pow_mul]
    apply Nat.gcd_eq_right
    simpa only [one_pow] using (hbo.pow (n := k)).nat_add_dvd_pow_add_pow x 1

end MetaMathlibExt
