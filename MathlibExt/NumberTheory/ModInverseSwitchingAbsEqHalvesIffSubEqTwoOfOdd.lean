/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModInverseSwitching
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-!
# Both first inverses extremal in the odd–odd case

The theorem `abs_eq_halves_iff_sub_eq_two_of_odd` proves Lemma 6 of Spiros Konstantogiannis,
"The Euclidean Algorithm as a Sequence of Modular Inverse Switching Formulas".
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

/-- **Both first inverses extremal, odd–odd case.** Let $(r_i)$, $(s_i)$ and $N$ be Euclidean
switching data with $r_0$ and $r_1$ both odd. Then $2|s_1| = r_0 - 1$ and $2|s_2| = r_1 - 1$
hold simultaneously if and only if $r_0 = r_1 + 2$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 6. -/
theorem abs_eq_halves_iff_sub_eq_two_of_odd
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (h0 : Odd (r 0)) (h1 : Odd (r 1)) :
    (2 * |s 1| = (r 0 : ℤ) - 1 ∧ 2 * |s 2| = (r 1 : ℤ) - 1) ↔
      r 0 = r 1 + 2 := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  obtain ⟨hN, hpos, hdesc, hlast, hquot, hs, hswitch⟩ := hseq
  have hlt : r 1 < r 0 := hdesc 0 (by omega)
  have hlt₂ : r 2 < r 1 := hdesc 1 hN
  have hpos₂ : 0 < r 2 := hpos 2 (by omega)
  have hn : (3 : ℤ) ≤ r 1 := by omega
  have hm : (5 : ℤ) ≤ r 0 := by omega
  have hbez : s 2 * (r 0 : ℤ) + s 1 * (r 1 : ℤ) = 1 := hswitch 1 le_rfl hN
  constructor
  · rintro ⟨habs₁, habs₂⟩
    have he₁ := congrArg (fun z : ℤ => z * (r 1 : ℤ)) habs₁
    have he₂ := congrArg (fun z : ℤ => z * (r 0 : ℤ)) habs₂
    rcases le_total 0 (s 1) with hsign₁ | hsign₁ <;>
      rcases le_total 0 (s 2) with hsign₂ | hsign₂
    · rw [abs_of_nonneg hsign₁] at he₁
      rw [abs_of_nonneg hsign₂] at he₂
      nlinarith
    · rw [abs_of_nonneg hsign₁] at he₁
      rw [abs_of_nonpos hsign₂] at he₂
      have : (r 0 : ℤ) = r 1 + 2 := by nlinarith only [he₁, he₂, hbez]
      omega
    · rw [abs_of_nonpos hsign₁] at he₁
      rw [abs_of_nonneg hsign₂] at he₂
      nlinarith
    · rw [abs_of_nonpos hsign₁] at he₁
      rw [abs_of_nonpos hsign₂] at he₂
      nlinarith
  · intro hgap
    obtain ⟨q, hq, hqeq⟩ := hquot 1 le_rfl hN
    have hqeq' : r 0 = q * r 1 + r 2 := hqeq
    have hq₁ : q = 1 := by
      by_contra h
      have hq₂ : 2 ≤ q := by omega
      have := Nat.mul_le_mul_right (r 1) hq₂
      omega
    have hr₂ : r 2 = 2 := by rw [hq₁] at hqeq'; omega
    have hN₂ : 2 ≤ N := by
      by_contra h
      have hN₁ : N = 1 := by omega
      have : r 2 = 1 := by simpa [hN₁] using hlast
      omega
    have hr₃ : r 3 = 1 := by
      have := hpos 3 (by omega)
      have : r 3 < r 2 := hdesc 2 hN₂
      omega
    have hN_eq : N = 2 := by
      by_contra h
      have hN₃ : 3 ≤ N := by omega
      have := hpos 4 (by omega)
      have : r 4 < r 3 := hdesc 3 hN₃
      omega
    have hs₃ : s 3 = 1 := by simpa [hN_eq] using hs
    have hbez₂ := hswitch 2 (by omega) hN₂
    have hs₂ : 2 * s 2 = 1 - (r 1 : ℤ) := by
      simpa [hr₂, hs₃, mul_comm, eq_sub_iff_add_eq, add_comm] using hbez₂
    have hs₂mul := congrArg (fun z : ℤ => z * (r 0 : ℤ)) hs₂
    have hs₁ : 2 * s 1 = (r 0 : ℤ) - 1 := by
      have hgap' : (r 0 : ℤ) = r 1 + 2 := by omega
      rw [hgap'] at hbez hs₂mul ⊢
      nlinarith only [hbez, hs₂mul, hn]
    rw [abs_of_nonneg (show 0 ≤ s 1 by omega), abs_of_nonpos (show s 2 ≤ 0 by omega)]
    constructor <;> omega

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
