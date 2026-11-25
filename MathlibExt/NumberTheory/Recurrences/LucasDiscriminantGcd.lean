/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Ring

/-! # Common divisors of a Lucas parameter and the discriminant -/

namespace MetaMathlibExt

/-- **Common divisors of $P$ and the discriminant.** Let $P$ and $Q$ be coprime integers and let
$D = P^2 - 4Q$. Then $\gcd(P, D)$ divides $4$, and $\gcd(P, D') = 1$ for every odd integer $D'$
dividing $D$.

Source: Lawrence Somer and Michal Křížek, *On Lucas and Frobenius Pseudoprimes*,
INTEGERS 25 (2025), Article A107, Lemma 4.9 (`integers-2025-A107-lem-4-9`). -/
public theorem gcd_p_discr_dvd_four
    (P Q : ℤ) (hcop : Int.gcd P Q = 1) :
    (Int.gcd P (P ^ 2 - 4 * Q) : ℤ) ∣ 4 ∧
      ∀ D' : ℤ, Odd D' → D' ∣ P ^ 2 - 4 * Q → Int.gcd P D' = 1 := by
  let g : ℤ := Int.gcd P (P ^ 2 - 4 * Q)
  have hgP : g ∣ P := Int.gcd_dvd_left _ _
  have hgD : g ∣ P ^ 2 - 4 * Q := Int.gcd_dvd_right _ _
  have hgQ : g ∣ 4 * Q := by
    have hgP2 : g ∣ P ^ 2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_left hgP P
    rw [show 4 * Q = P ^ 2 - (P ^ 2 - 4 * Q) by ring]
    exact dvd_sub hgP2 hgD
  have hg4 : g ∣ 4 := by
    -- Multiply the Bézout identity for P and Q by 4.
    calc
      g ∣ P * (4 * Int.gcdA P Q) + (4 * Q) * Int.gcdB P Q :=
        dvd_add (dvd_mul_of_dvd_left hgP _) (dvd_mul_of_dvd_left hgQ _)
      _ = 4 * (P * Int.gcdA P Q + Q * Int.gcdB P Q) := by ring
      _ = 4 := by rw [← Int.gcd_eq_gcd_ab, hcop]; simp
  refine ⟨hg4, ?_⟩
  intro D' hodd hD'
  have hkD' : (Int.gcd P D' : ℤ) ∣ D' := Int.gcd_dvd_right _ _
  have hk4 : (Int.gcd P D' : ℤ) ∣ 4 :=
    (Int.natCast_dvd_natCast.mpr (Int.gcd_dvd_gcd_of_dvd_right P hD')).trans hg4
  obtain ⟨j, hj⟩ := hodd
  -- An odd square is 1 modulo 4.
  have hk1 : (Int.gcd P D' : ℤ) ∣ 1 := by
    rw [show (1 : ℤ) = D' * D' - 4 * (j * (j + 1)) by rw [hj]; ring]
    exact dvd_sub (dvd_mul_of_dvd_left hkD' _) (dvd_mul_of_dvd_left hk4 _)
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hk1)

end MetaMathlibExt
