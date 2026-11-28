/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HurwitzGeometricProgressionFreeQuaternionGreedyNeNormPreimage
import MathlibExt.NumberTheory.HurwitzQuaternionGreedy
import MathlibExt.NumberTheory.QuadraticForms.LegendreThreeSquareConverse
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The scalar quaternion `7` separates the two greedy sets -/

namespace MetaMathlibExt.quaternionGreedy_mem_of_not_unit_mul_sq

set_option quotPrecheck false in
/-- The Hurwitz order: quaternions with all coordinates in `ℤ` or all in `ℤ + 1/2`. -/
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)

set_option quotPrecheck false in
/-- `S(G)`: Hurwitz quaternions whose norm lies in `G ⊆ ℕ`. -/
local notation "𝐒ᴳ" G:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ ∃ n ∈ G, Quaternion.normSq q = ((n : ℕ) : ℚ)

set_option quotPrecheck false in
/-- Rankin's greedy set `G₃*(ℕ₊)`: positive integers whose prime valuations have no
ternary digit `2`. -/
local notation "𝐆ʳ" => Set.ofPred fun n : ℕ =>
  0 < n ∧ ∀ p : ℕ, p.Prime → 2 ∉ Nat.digits 3 (n.factorization p)

set_option quotPrecheck false in
/-- `Gq` is the quaternion greedy set `G₃*(Q_Hur ∖ {0})`, pinned by its defining recursion. -/
local notation "IsQuaternionGreedy" Gq:max => ∀ q : Quaternion ℚ, q ∈ Gq ↔
  (q ∈ 𝐇 ∧ q ≠ 0 ∧ ¬ ∃ a ∈ Gq, ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r ≠ 1 ∧
    a * r ∈ Gq ∧ q = a * r ^ 2)

set_option quotPrecheck false in
/-- `Q = U R²` for a unit `U ∈ Q_Hur` and some `R ∈ Q_Hur` of norm `r`. -/
local notation "IsUnitMulSq" Q:max r:max => ∃ U ∈ 𝐇, Quaternion.normSq U = 1 ∧
  ∃ R ∈ 𝐇, Quaternion.normSq R = ((r : ℕ) : ℚ) ∧ Q = U * R ^ 2


private theorem twice_re_eq_int {q : Quaternion ℚ} (hq : q ∈ 𝐇) :
    ∃ a : ℤ, 2 * q.re = (a : ℚ) := by
  rcases hq with ⟨a, _, _, _, ha, _⟩ | ⟨a, _, _, _, ha, _⟩
  · exact ⟨2 * a, by simp [ha]⟩
  · refine ⟨2 * a + 1, ?_⟩
    push_cast
    rw [ha]
    ring

private theorem scalar_seven_not_unit_mul_sq : ¬ IsUnitMulSq ((7 : ℚ) : Quaternion ℚ) 7 := by
  rintro ⟨U, hU, hUn, R, hR, hRn, hprod⟩
  have hRn' : R.re ^ 2 + R.imI ^ 2 + R.imJ ^ 2 + R.imK ^ 2 = 7 := by
    simpa [Quaternion.normSq_def'] using hRn
  obtain ⟨A, hA⟩ := twice_re_eq_int hR
  obtain ⟨B, hB⟩ := twice_re_eq_int hU
  -- Multiplying by the conjugate of the unit determines the real part of the square.
  have hre := congrArg (fun q : Quaternion ℚ => (star U * q).re) hprod
  change (star U * ((7 : ℚ) : Quaternion ℚ)).re = (star U * (U * R ^ 2)).re at hre
  have hscalar : (star U * ((7 : ℚ) : Quaternion ℚ)).re = U.re * 7 := by
    rw [Quaternion.re_mul, Quaternion.re_star]
    change U.re * 7 - (star U).imI * 0 - (star U).imJ * 0 - (star U).imK * 0 = _
    simp
  rw [hscalar, ← mul_assoc, Quaternion.star_mul_self, hUn] at hre
  simp only [Quaternion.coe_one, one_mul, pow_two, Quaternion.re_mul] at hre
  have hAB : A ^ 2 = 14 + 7 * B := by
    exact_mod_cast (show (A : ℚ) ^ 2 = 14 + 7 * (B : ℚ) by
      rw [← hA, ← hB]
      nlinarith)
  have hA2 : A ^ 2 ≤ 28 := by
    exact_mod_cast (show (A : ℚ) ^ 2 ≤ 28 by
      rw [← hA]
      nlinarith [sq_nonneg R.imI, sq_nonneg R.imJ, sq_nonneg R.imK])
  have hAlo : -5 ≤ A := by
    by_contra! hl
    have : A ≤ -6 := by omega
    nlinarith [sq_nonneg (A + 6)]
  have hAhi : A ≤ 5 := by
    by_contra! hu
    have : 6 ≤ A := by omega
    nlinarith [sq_nonneg (A - 6)]
  have hAmod : A ^ 2 % 7 = 0 := by omega
  have hA0 : A = 0 := by
    interval_cases A <;> norm_num at hAmod
    rfl
  have hRre : R.re = 0 := by rw [hA0, Int.cast_zero] at hA; linarith
  rcases hR with ⟨a, b, c, d, _, hb, hc, hd⟩ | ⟨a, _, _, _, ha, _⟩
  · have hsq : b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 = 7 := by
      rw [hRre, hb, hc, hd, zero_pow (by decide : 2 ≠ 0), zero_add] at hRn'
      have hInt : b ^ 2 + c ^ 2 + d ^ 2 = 7 := by exact_mod_cast hRn'
      exact_mod_cast (show
        ((b.natAbs : ℕ) : ℤ) ^ 2 + ((c.natAbs : ℕ) : ℤ) ^ 2 + ((d.natAbs : ℕ) : ℤ) ^ 2 = 7 by
          simpa only [Int.natCast_natAbs, sq_abs] using hInt)
    exact Nat.not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares 7
      ⟨b.natAbs, c.natAbs, d.natAbs, hsq⟩ ⟨0, 0, by decide⟩
  · have h : (2 * a + 1 : ℤ) = 0 := by
      exact_mod_cast (show (2 * (a : ℚ) + 1 : ℚ) = 0 by rw [ha] at hRre; linarith)
    omega

example (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    ((7 : ℚ) : Quaternion ℚ) ∈ Gq \ 𝐒ᴳ 𝐆ʳ ∧
      (((7 : ℚ) : Quaternion ℚ) ^ 2) ∈ 𝐒ᴳ 𝐆ʳ \ Gq := by
  apply quaternionGreedy_mem_of_not_unit_mul_sq Gq hGq 7 Nat.prime_seven
  · exact Or.inl ⟨7, 0, 0, 0, rfl, rfl, rfl, rfl⟩
  · exact Quaternion.normSq_coe (x := (7 : ℚ))
  · exact scalar_seven_not_unit_mul_sq

-- Check Rankin membership directly, using the ternary digits of 2 and 4.
example : ((7 : ℕ) : Quaternion ℚ) ∉ 𝐒ᴳ 𝐆ʳ ∧ ((49 : ℕ) : Quaternion ℚ) ∈ 𝐒ᴳ 𝐆ʳ := by
  constructor
  · rintro ⟨_, n, hn, hnorm⟩
    rw [Quaternion.normSq_natCast, ← Nat.cast_pow] at hnorm
    have hn49 : n = 7 ^ 2 := by exact_mod_cast hnorm.symm
    have hdigits := hn.2 7 Nat.prime_seven
    rw [hn49, Nat.prime_seven.factorization_pow, Finsupp.single_eq_same] at hdigits
    exact hdigits (by decide)
  · refine ⟨Or.inl ⟨49, 0, 0, 0, rfl, rfl, rfl, rfl⟩, 7 ^ 4, ⟨by decide, ?_⟩, ?_⟩
    · intro p _
      rw [Nat.prime_seven.factorization_pow, Finsupp.single_apply]
      split <;> decide
    · rw [Quaternion.normSq_natCast]
      norm_num

-- Check the progression that excludes 49 once the greedy set contains 1 and 7.
example : ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r = 49 ∧
    (1 : Quaternion ℚ) * r = ((7 : ℕ) : Quaternion ℚ) ∧
    (1 : Quaternion ℚ) * r ^ 2 = ((49 : ℕ) : Quaternion ℚ) := by
  refine ⟨((7 : ℕ) : Quaternion ℚ), Or.inl ⟨7, 0, 0, 0, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply Quaternion.normSq_ne_zero.mp
    rw [Quaternion.normSq_natCast]
    norm_num
  · rw [Quaternion.normSq_natCast]
    norm_num
  · simp
  · rw [one_mul, ← Nat.cast_pow]
    rfl

-- The first two primes in this congruence class give distinct scalars and distinct squares.
example : Nat.Prime 7 ∧ 7 % 8 = 7 ∧ Nat.Prime 23 ∧ 23 % 8 = 7 ∧
    ((7 : ℕ) : Quaternion ℚ) ≠ ((23 : ℕ) : Quaternion ℚ) ∧
    (((7 : ℕ) : Quaternion ℚ) ^ 2) ≠ (((23 : ℕ) : Quaternion ℚ) ^ 2) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro h
    have hre := congrArg (fun q : Quaternion ℚ => q.re) h
    simp only [Quaternion.re_natCast] at hre
    norm_num at hre
  · rw [← Nat.cast_pow, ← Nat.cast_pow]
    intro h
    have hre := congrArg (fun q : Quaternion ℚ => q.re) h
    simp only [Quaternion.re_natCast] at hre
    norm_num at hre

-- The two differences remain nonempty after removing the initial witnesses.
example (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    (∃ q ∈ Gq \ 𝐒ᴳ 𝐆ʳ, q ≠ ((7 : ℚ) : Quaternion ℚ)) ∧
      (∃ q ∈ 𝐒ᴳ 𝐆ʳ \ Gq, q ≠ ((49 : ℚ) : Quaternion ℚ)) := by
  obtain ⟨hleft, hright⟩ := quaternionGreedy_diff_rankin_infinite Gq hGq
  exact ⟨by simpa using hleft.exists_notMem_finite (Set.finite_singleton ((7 : ℚ) : Quaternion ℚ)),
    by simpa using hright.exists_notMem_finite (Set.finite_singleton ((49 : ℚ) : Quaternion ℚ))⟩

end MetaMathlibExt.quaternionGreedy_mem_of_not_unit_mul_sq
