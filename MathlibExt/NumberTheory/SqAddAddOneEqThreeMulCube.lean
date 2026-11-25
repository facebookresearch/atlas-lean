/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer solutions of $u^2 \pm u + 1 = 3v^3$

For integers `u` and `v`, `u ^ 2 + u + 1 = 3 * v ^ 3` holds only for
`(u, v) = (-2, 1)` and `(u, v) = (1, 1)`, and `u ^ 2 - u + 1 = 3 * v ^ 3` holds
only for `(u, v) = (2, 1)` and `(u, v) = (-1, 1)`
(`MetaMathlibExt.sq_add_add_one_eq_three_mul_cube_iff`).

## Proof outline

The paper reduces the equation to integral points on the Mordell curve
`y ^ 2 = x ^ 3 - 432`. The proof here instead uses Fermat's Last Theorem for
exponent three. Since `3` divides `u ^ 2 + u + 1`, working in `ZMod 3` gives
`u ≡ 1 (mod 3)`; writing `u = 3 * k + 1` yields `k ^ 3 + v ^ 3 = (k + 1) ^ 3`,
so Fermat's Last Theorem for exponent three forces `k = 0` or `k = -1`. The
second equation follows from the first by substituting `u ↦ -u`.

## References

* Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes with Prime-Square
  Factors*, INTEGERS 25 (2025), Article A103, Lemma 2.
-/

@[expose] public section

namespace MetaMathlibExt

namespace sq_add_add_one_eq_three_mul_cube_iff

/-- The forward direction of the `+` equation: if `u ^ 2 + u + 1 = 3 * v ^ 3`,
then `(u, v)` is one of the two listed pairs. -/
private theorem forward {u v : ℤ} (h : u ^ 2 + u + 1 = 3 * v ^ 3) :
    (u, v) = (-2, 1) ∨ (u, v) = (1, 1) := by
  have hpos : 0 < u ^ 2 + u + 1 := by nlinarith [sq_nonneg (2 * u + 1)]
  have hvpos : 0 < v := by
    by_contra hc
    have hc : v ≤ 0 := not_lt.mp hc
    have hcube : v ^ 3 ≤ 0 := by
      have h1 : v * v ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg v)
      rwa [← pow_succ'] at h1
    linarith
  have hdvd : (3 : ℤ) ∣ u ^ 2 + u + 1 := ⟨v ^ 3, h⟩
  have hmod : (u : ZMod 3) = 1 := by
    have key : ∀ x : ZMod 3, x ^ 2 + x + 1 = 0 → x = 1 := by decide
    apply key
    have hcast : ((u ^ 2 + u + 1 : ℤ) : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hdvd
    push_cast at hcast
    exact hcast
  have hdvd1 : (3 : ℤ) ∣ u - 1 := by
    have h2 : (u : ZMod 3) = ((1 : ℤ) : ZMod 3) := by rw [hmod]; norm_num
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub u 1 3).mp h2
    have h4 : (3 : ℤ) ∣ -(u - 1) := by convert h3 using 1; ring
    exact dvd_neg.mp h4
  obtain ⟨k, hk⟩ := hdvd1
  have hu : u = 3 * k + 1 := by omega
  have hv3 : v ^ 3 = 3 * k ^ 2 + 3 * k + 1 := by
    rw [hu] at h
    have hv3' : 3 * v ^ 3 = 3 * (3 * k ^ 2 + 3 * k + 1) := by linear_combination -h
    exact mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0) hv3'
  have hcube_eq : k ^ 3 + v ^ 3 = (k + 1) ^ 3 := by linear_combination hv3
  have hveq : v ^ 3 = 1 → v = 1 := by
    intro hv1
    have h2 : v ^ 3 = (1 : ℤ) ^ 3 := by rw [hv1]; norm_num
    exact (pow_left_inj₀ hvpos.le (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp h2
  rcases (by omega : k = 0 ∨ k = -1 ∨ 1 ≤ k ∨ k ≤ -2) with rfl | rfl | hk1 | hk2
  · have hv1 : v = 1 := hveq (by linear_combination hv3)
    right
    rw [Prod.mk.injEq]
    exact ⟨by omega, hv1⟩
  · have hv1 : v = 1 := hveq (by linear_combination hv3)
    left
    rw [Prod.mk.injEq]
    exact ⟨by omega, hv1⟩
  · exfalso
    have hNat : k.toNat ^ 3 + v.toNat ^ 3 = (k + 1).toNat ^ 3 := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k),
        Int.toNat_of_nonneg hvpos.le, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k + 1)]
      exact hcube_eq
    exact fermatLastTheoremThree k.toNat v.toNat (k + 1).toNat
      (by omega) (by omega) (by omega) hNat
  · exfalso
    set m : ℤ := -(k + 1) with hm_def
    have hmpos : 0 < m := by omega
    have hEq : v ^ 3 + m ^ 3 = (m + 1) ^ 3 := by
      rw [hm_def]
      linear_combination hcube_eq
    have hNat : v.toNat ^ 3 + m.toNat ^ 3 = (m + 1).toNat ^ 3 := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Int.toNat_of_nonneg hvpos.le, Int.toNat_of_nonneg hmpos.le,
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m + 1)]
      exact hEq
    exact fermatLastTheoremThree v.toNat m.toNat (m + 1).toNat
      (by omega) (by omega) (by omega) hNat

end sq_add_add_one_eq_three_mul_cube_iff

/-- **Integer solutions of $u^2 \pm u + 1 = 3v^3$.** For all integers $u$ and $v$,
$u^2 + u + 1 = 3v^3$ if and only if $(u, v) = (-2, 1)$ or $(u, v) = (1, 1)$, and
$u^2 - u + 1 = 3v^3$ if and only if $(u, v) = (2, 1)$ or $(u, v) = (-1, 1)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 2
(`integers-2025-A103-lem-2`). -/
theorem sq_add_add_one_eq_three_mul_cube_iff (u v : ℤ) :
    (u ^ 2 + u + 1 = 3 * v ^ 3 ↔ (u, v) = (-2, 1) ∨ (u, v) = (1, 1)) ∧
      (u ^ 2 - u + 1 = 3 * v ^ 3 ↔ (u, v) = (2, 1) ∨ (u, v) = (-1, 1)) := by
  refine ⟨⟨fun h => sq_add_add_one_eq_three_mul_cube_iff.forward h, ?_⟩,
    ⟨?_, ?_⟩⟩
  · rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> norm_num
  · intro h
    have h2 := sq_add_add_one_eq_three_mul_cube_iff.forward (u := -u) (v := v)
      (by linear_combination h)
    rcases h2 with h2 | h2 <;> simp only [Prod.mk.injEq] at h2 <;>
      obtain ⟨hu, hv⟩ := h2
    · left
      rw [Prod.mk.injEq]
      exact ⟨by omega, hv⟩
    · right
      rw [Prod.mk.injEq]
      exact ⟨by omega, hv⟩
  · rintro (h | h) <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> norm_num

end MetaMathlibExt
