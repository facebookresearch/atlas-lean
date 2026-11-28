/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedTau
import Mathlib.Data.Int.GCD

/-!
# Generalized tau congruence at coprime indices

The weighted divisibility of generalized tau coefficients gives vanishing modulo `|k| / d`
when the shifted index has the form `|k| * m + d * r` and `r` is coprime to `|k| / d`.
-/

namespace MetaMathlibExt

/-- **Vanishing of the generalized tau function modulo $|k|/d$.** Let $\tau_k(n)$ be the
generalized tau function, the coefficient of $q^n$ in $q \prod_{j \ge 1} (1 - q^j)^k$. Let $k$ be
an integer with $|k| \ge 2$ and $d$ a natural number dividing $|k|$ with $d < |k|$. Then for all
natural numbers $m$ and $r$ with $\gcd(r, |k|/d) = 1$,
$\tau_k(|k| m + d r + 1) \equiv 0 \pmod{|k|/d}$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Proposition 3 (`integers-2024-A39-prop-3`). -/
public theorem generalizedTau_modEq_zero_of_coprime (m : ℕ) (k : ℤ) (hk : 2 ≤ |k|) (d : ℕ)
    (hd : d ∣ k.natAbs) (hdk : d < k.natAbs) (r : ℕ)
    (hr : Nat.gcd r (k.natAbs / d) = 1) :
    generalizedTau k (k.natAbs * m + d * r + 1) ≡ 0 [ZMOD ((k.natAbs / d : ℕ) : ℤ)] := by
  let q := k.natAbs / d
  let n := k.natAbs * m + d * r
  let t := generalizedTau k (n + 1)
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd ((Nat.zero_le d).trans_lt hdk)
  have hK : k.natAbs = d * q := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel hd).symm
  have hq : 1 < q := (Nat.mul_lt_mul_left hd_pos).mp (by
    simpa only [Nat.mul_one, ← hK] using hdk)
  have hr_pos : 0 < r := by
    refine Nat.pos_of_ne_zero ?_
    intro hr_zero
    have hq_one : q = 1 := by simpa only [hr_zero, Nat.gcd_zero_left] using hr
    exact hq.ne' hq_one
  have hn_pos : 0 < n := Nat.add_pos_right _ (Nat.mul_pos hd_pos hr_pos)
  have hn : n = d * (q * m + r) := by
    dsimp only [n]
    rw [hK, mul_assoc, ← mul_add]
  have h := mul_generalizedTau_succ_modEq_zero n hn_pos k hk
  rw [Int.modEq_zero_iff_dvd, ← Int.natCast_natAbs] at h
  change (k.natAbs : ℤ) ∣ (n : ℤ) * t at h
  have hmul : (d : ℤ) * q ∣ (d : ℤ) * (((q : ℤ) * m + r) * t) := by
    simpa only [hK, hn, Nat.cast_mul, Nat.cast_add, mul_assoc] using h
  have hsum := (mul_dvd_mul_iff_left (Int.natCast_ne_zero.mpr hd_pos.ne')).mp hmul
  have hqm : (q : ℤ) ∣ (q : ℤ) * m * t :=
    dvd_mul_of_dvd_left (dvd_mul_right (q : ℤ) (m : ℤ)) t
  have hrt : (q : ℤ) ∣ (r : ℤ) * t := by
    rw [add_mul] at hsum
    simpa only [add_sub_cancel_left] using Int.dvd_sub hsum hqm
  exact Int.modEq_zero_iff_dvd.mpr (Int.dvd_of_dvd_mul_right_of_gcd_one hrt (by
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm q r]
    exact hr))

end MetaMathlibExt
