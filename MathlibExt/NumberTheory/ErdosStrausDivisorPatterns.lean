/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! # Divisor criteria for Erdős–Straus triples -/

namespace MetaMathlibExt

/-- **Type I Erdős–Straus triples from divisors of a square.** Let $p$ be a prime and let $x$ be a
natural number with $\lceil p/4 \rceil \le x \le \lceil p/2 \rceil$. If $d$ is a positive divisor
of $x^2$ with $d \equiv -px \pmod{4x - p}$, then there are natural numbers $y$ and $z$ with
$(4x - p)\,y = px + d$ and $(4x - p)\,d\,z = px(px + d)$ such that $x \le y \le z$ and $p \nmid y$.

Since $4x > p$, these equations say $y = (px + d)/(4x - p)$ and $z = p(x + px^2/d)/(4x - p)$.

Source: Kyle Bradford, *Elementary Patterns from the Erdős-Straus Conjecture*, INTEGERS 25 (2025),
Article A54, Proposition 1 (`integers-2025-A54-prop-1`). -/
public theorem erdosStraus_typeI_of_dvd_sq {p x d : ℕ} (hp : p.Prime)
    (hx₁ : (p + 3) / 4 ≤ x) (hx₂ : x ≤ (p + 1) / 2) (hd₀ : 0 < d) (hd : d ∣ x ^ 2)
    (hmod : (4 * x - p : ℤ) ∣ d + p * x) :
    ∃ y z : ℕ, (4 * x - p : ℤ) * y = p * x + d ∧ (4 * x - p : ℤ) * d * z = p * x * (p * x + d) ∧
      x ≤ y ∧ y ≤ z ∧ ¬ p ∣ y := by
  have hp₂ := hp.two_le
  have hp4x : p ≤ 4 * x := by omega
  have hx : 0 < x := by omega
  have hxp : x < p := by omega
  have hcast : ((4 * x - p : ℕ) : ℤ) = 4 * x - p := by
    simp [Nat.cast_sub hp4x]
  obtain ⟨y, hy⟩ : 4 * x - p ∣ p * x + d := by
    rw [← Int.ofNat_dvd, hcast]
    simpa [add_comm] using hmod
  have hsum : 4 * x * y = p * x + d + p * y := by
    rw [hy, ← Nat.add_mul, Nat.sub_add_cancel hp4x]
  -- Multiplying the equation for y by x shows that d also divides pxy.
  have hprod : p * x ^ 2 + d * x + p * x * y = x ^ 2 * (4 * y) := by
    linear_combination x * hsum.symm
  obtain ⟨z, hz⟩ : d ∣ p * x * y := by
    have hdiv : d ∣ p * x ^ 2 + d * x :=
      Nat.dvd_add (dvd_mul_of_dvd_right hd p) (dvd_mul_right d x)
    apply (Nat.dvd_add_right hdiv).mp
    rw [hprod]
    exact dvd_mul_of_dvd_left hd _
  refine ⟨y, z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcast]
    exact_mod_cast hy.symm
  · rw [← hcast]
    exact_mod_cast calc
      (4 * x - p) * d * z = p * x * ((4 * x - p) * y) := by rw [mul_assoc, ← hz]; ac_rfl
      _ = p * x * (p * x + d) := by rw [← hy]
  · by_contra! hlt
    have hx₂' : 2 * x ≤ p + 1 := by omega
    have hy₂ : 2 * y + 1 ≤ p := by omega
    nlinarith only [hsum, Nat.mul_le_mul_right y hx₂', Nat.mul_le_mul_right x hy₂, hlt]
  · apply Nat.le_of_mul_le_mul_left _ hd₀
    rw [← hz]
    apply Nat.mul_le_mul_right
    calc
      d ≤ x ^ 2 := Nat.le_of_dvd (pow_pos hx _) hd
      _ ≤ p * x := by rw [sq]; exact Nat.mul_le_mul_right x hxp.le
  · intro hpy
    have hpd : p ∣ d := (Nat.dvd_add_right (dvd_mul_right p x)).mp
      (hy ▸ dvd_mul_of_dvd_right hpy _)
    exact Nat.not_dvd_of_pos_of_lt hx hxp (hp.dvd_of_dvd_pow (hpd.trans hd))

end MetaMathlibExt
