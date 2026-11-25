/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Morgado's characterization of regular integers modulo a positive integer
-/

public section

/-- **Morgado's characterization of regular integers.** Let $n$ be a positive integer and $m$
an integer, and write $\gcd$ for the nonnegative greatest common divisor. The congruence
$m^2 x \equiv m \pmod{n}$ has a solution $x \in \mathbb{Z}$ if and only if
$\gcd(m^2, n) = \gcd(m, n)$, and $\gcd(m^2, n) = \gcd(m, n)$ holds if and only if $\gcd(m, n)$
and $n / \gcd(m, n)$ are coprime, that is, $\gcd(m, n)$ is a unitary divisor of $n$.

Source: Klaus Dohmen and Mandy Lange-Geisler, "On the Number of
Regular Integers Modulo `n` and Its Significance for Cryptography",
Journal of Integer Sequences 29 (2026), Article 26.2.4, Proposition
[Morgado 1972] (label `sec:regul-numb-unit-2`):
<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex>. -/
theorem isRegularMod_iff_gcd_sq_eq_gcd {n : ℕ} (hn : 0 < n) (m : ℤ) :
    ((∃ x : ℤ, m ^ 2 * x ≡ m [ZMOD (n : ℤ)])
      ↔ Nat.gcd (m.natAbs ^ 2) n = Nat.gcd m.natAbs n)
    ∧ (Nat.gcd (m.natAbs ^ 2) n = Nat.gcd m.natAbs n
      ↔ Nat.Coprime (Nat.gcd m.natAbs n) (n / Nat.gcd m.natAbs n)) := by
  constructor
  · -- Bézout identifies the possible right-hand sides with multiples of the gcd.
    simp_rw [Int.modEq_iff_add_fac]
    rw [← gcd_dvd_iff_exists, ← Int.coe_gcd, Int.natCast_dvd, Int.gcd_def,
      Int.natAbs_pow, Int.natAbs_natCast]
    constructor
    · intro h
      exact Nat.dvd_antisymm (Nat.dvd_gcd h (Nat.gcd_dvd_right _ _))
        (by simpa only [sq] using Nat.gcd_dvd_gcd_mul_right_left m.natAbs n m.natAbs)
    · intro h
      rw [h]
      exact Nat.gcd_dvd_left _ _
  · -- Write |m| = u * d and n = v * d with u and v coprime.
    generalize m.natAbs = a
    obtain ⟨d, u, v, hd, huv, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right a hn)
    rw [Nat.gcd_mul_right, huv.gcd_eq_one, one_mul, Nat.mul_div_cancel _ hd,
      mul_pow, sq d, ← mul_assoc, Nat.gcd_mul_right, (huv.pow_left 2).gcd_mul_left_cancel d,
      Nat.mul_eq_right hd.ne']
