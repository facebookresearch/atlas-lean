/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Ring

/-!
# Solutions of $2 + 7^y = z^2$

The main result, `MetaMathlibExt.two_add_seven_pow_eq_sq_iff`, says that $(y, z) = (1, 3)$ is the
only solution of $2 + 7^y = z^2$ in natural numbers. The statement comes from the paper of Zhang
and Li cited in its docstring; the proof here is a self-contained elementary argument.

Squares are $0$ or $1$ modulo $4$, so $y$ is odd, say $y = 2m + 1$, and $(z, 7^m)$ solves the
Pell-type equation $z^2 = 7w^2 + 2$. Descent by the unit $8 - 3\sqrt{7}$ shows that the solutions
in natural numbers are the pairs $(z_n, w_n)$ with
$z_n + w_n\sqrt{7} = (3 + \sqrt{7})(8 + 3\sqrt{7})^n$. Since $w_n \equiv 2n + 1 \pmod 7$, the
prime $7$ divides $w_n$ only when $n \equiv 3 \pmod 7$, and then $617$ divides $w_n$ too:
$w_3 = 4319 = 7 \cdot 617$, and $w_{n+7} \equiv 130576328\, w_n \pmod{617}$. So $w_n = 7^m$
forces $m = 0$.
-/

namespace MetaMathlibExt

namespace two_add_seven_pow_eq_sq_iff

/-- The solutions $(z_n, w_n)$ in natural numbers of $z^2 = 7w^2 + 2$, given by
$z_n + w_n\sqrt{7} = (3 + \sqrt{7})(8 + 3\sqrt{7})^n$. -/
private def sol : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | n + 1 => (8 * (sol n).1 + 21 * (sol n).2, 3 * (sol n).1 + 8 * (sol n).2)

private theorem sol_succ (n : ℕ) :
    sol (n + 1) = (8 * (sol n).1 + 21 * (sol n).2, 3 * (sol n).1 + 8 * (sol n).2) := rfl

private theorem sol_succ_fst (n : ℕ) : (sol (n + 1)).1 = 8 * (sol n).1 + 21 * (sol n).2 := rfl

private theorem sol_succ_snd (n : ℕ) : (sol (n + 1)).2 = 3 * (sol n).1 + 8 * (sol n).2 := rfl

/-- Every solution of $z^2 = 7w^2 + 2$ in natural numbers is one of the pairs `sol n`: for
$w \ge 5$, multiplying $z + w\sqrt{7}$ by $8 - 3\sqrt{7}$ gives a solution with smaller $w$. -/
private theorem exists_sol_eq (w : ℕ) :
    ∀ z : ℕ, z ^ 2 = 7 * w ^ 2 + 2 → ∃ n, sol n = (z, w) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro z h
    rcases (show w ≤ 4 ∨ 5 ≤ w by omega) with hw | hw
    · have hz : z ≤ 11 := by nlinarith
      interval_cases w <;> interval_cases z <;> first | exact ⟨0, rfl⟩ | (norm_num at h)
    · have h1 : 21 * w ≤ 8 * z := by
        by_contra hc
        have := Nat.pow_lt_pow_left (Nat.lt_of_not_le hc) two_ne_zero
        nlinarith
      have h2 : 3 * z ≤ 8 * w := by
        by_contra hc
        have := Nat.pow_lt_pow_left (Nat.lt_of_not_le hc) two_ne_zero
        nlinarith
      have h3 : 7 * w < 3 * z := by
        by_contra hc
        have := Nat.pow_le_pow_left (Nat.le_of_not_lt hc) 2
        nlinarith
      obtain ⟨z', hz'⟩ := Nat.exists_eq_add_of_le h1
      obtain ⟨w', hw'⟩ := Nat.exists_eq_add_of_le h2
      have hz : z = 8 * z' + 21 * w' := by omega
      have hw : w = 3 * z' + 8 * w' := by omega
      have hlt : w' < w := by omega
      have h' : z' ^ 2 = 7 * w' ^ 2 + 2 := by
        rw [hz, hw] at h
        nlinarith
      obtain ⟨n, hn⟩ := ih w' hlt z' h'
      exact ⟨n + 1, by rw [sol_succ, hn, hz, hw]⟩

/-- The pairs `sol n` satisfy $z_n \equiv 3$ and $w_n \equiv 2n + 1 \pmod 7$. -/
private theorem sol_mod_seven (n : ℕ) :
    (sol n).1 % 7 = 3 ∧ (sol n).2 % 7 = (2 * n + 1) % 7 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [sol_succ_fst, sol_succ_snd]
    omega

/-- Seven steps of the recursion: $w_{n+7} = 49353213\, z_n + 130576328\, w_n$. -/
private theorem sol_add_seven_snd (n : ℕ) :
    (sol (n + 7)).2 = 49353213 * (sol n).1 + 130576328 * (sol n).2 := by
  change (sol (n + 1 + 1 + 1 + 1 + 1 + 1 + 1)).2 = _
  simp only [sol_succ_fst, sol_succ_snd]
  ring

/-- $617$ divides $w_n$ whenever $n \equiv 3 \pmod 7$. -/
private theorem dvd_sol_snd (i : ℕ) : 617 ∣ (sol (7 * i + 3)).2 := by
  induction i with
  | zero => exact ⟨7, rfl⟩
  | succ i ih =>
    rw [show 7 * (i + 1) + 3 = 7 * i + 3 + 7 by ring, sol_add_seven_snd]
    exact dvd_add (dvd_mul_of_dvd_left ⟨79989, rfl⟩ _) (dvd_mul_of_dvd_right ih _)

end two_add_seven_pow_eq_sq_iff

open two_add_seven_pow_eq_sq_iff

/-- **Solutions of $2 + 7^y = z^2$.** For natural numbers $y, z$, we have $2 + 7^y = z^2$ if and
only if $(y, z) = (1, 3)$.

Source: Jing Zhang and Yuan Li, *On the Equation (-1)^α p^x + (-1)^β (2^k(2p - 1))^y = z^2 for
Prime Pairs (p, 2p - 1)*, INTEGERS 24 (2024), Article A64, Theorem 11. -/
public theorem two_add_seven_pow_eq_sq_iff (y z : ℕ) : 2 + 7 ^ y = z ^ 2 ↔ (y, z) = (1, 3) := by
  constructor
  · intro h
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' y
    · -- `y = 2m`: then `z ^ 2 ≡ 3 [MOD 4]`, impossible.
      exfalso
      have h49 : 7 ^ (2 * m) % 4 = 1 := by
        rw [pow_mul, Nat.pow_mod]
        norm_num
      have hsq : z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
        rcases Nat.even_or_odd' z with ⟨k, rfl | rfl⟩ <;> ring_nf <;> omega
      omega
    · -- `y = 2m + 1`: `(z, 7 ^ m)` solves `z ^ 2 = 7 * w ^ 2 + 2`.
      have hpell : z ^ 2 = 7 * (7 ^ m) ^ 2 + 2 := by
        rw [← h]
        ring
      obtain ⟨n, hn⟩ := exists_sol_eq (7 ^ m) z hpell
      rcases m with _ | m
      · have h9 : z ^ 2 = 3 ^ 2 := by simpa using hpell
        rw [Nat.pow_left_injective two_ne_zero h9]
      · exfalso
        have h2 : (sol n).2 = 7 ^ (m + 1) := by rw [hn]
        have h7 : 7 ∣ (sol n).2 := h2 ▸ dvd_pow_self 7 (Nat.succ_ne_zero m)
        have hn7 : n % 7 = 3 := by
          have := (sol_mod_seven n).2
          omega
        have h617 : 617 ∣ 7 ^ (m + 1) := by
          have := dvd_sol_snd (n / 7)
          rwa [show 7 * (n / 7) + 3 = n by omega, h2] at this
        have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right (m + 1)
          (by norm_num : Nat.Coprime 617 7)) h617
        omega
  · intro h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    norm_num

end MetaMathlibExt
