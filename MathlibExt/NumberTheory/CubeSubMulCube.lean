/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.SqAddAddOneEqThreeMulCube

/-! # Integer solutions of $u^3 - d v^3 = 1$ for $d \in \{4,18,36\}$ -/

namespace MetaMathlibExt

private theorem three_dvd_sub_one_of_cube_sub_mul_cube_eq_one {d u v : ℤ}
    (hd : d = 4 ∨ d = 18 ∨ d = 36) (h : u ^ 3 - d * v ^ 3 = 1) : (3 : ℤ) ∣ u - 1 := by
  have residue : ∀ c x y : ZMod 9,
      c = 4 ∨ c = 0 → x ^ 3 - c * y ^ 3 = 1 → 3 * (x - 1) = 0 := by decide
  have hd9 : (d : ZMod 9) = 4 ∨ (d : ZMod 9) = 0 := by
    rcases hd with rfl | rfl | rfl <;> decide
  have h9 : (u : ZMod 9) ^ 3 - (d : ZMod 9) * (v : ZMod 9) ^ 3 = 1 := by
    simpa using congrArg (fun z : ℤ ↦ (z : ZMod 9)) h
  have hdiv : (9 : ℤ) ∣ 3 * (u - 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp (by
      push_cast
      exact residue _ _ _ hd9 h9)
  omega

private theorem quadratic_factor_is_cube {d k v : ℤ} (hd0 : d ≠ 0) (hd36 : d ∣ 36)
    (h : (9 * k) * (3 * k ^ 2 + 3 * k + 1) = d * v ^ 3) :
    ∃ w : ℤ, 3 * k ^ 2 + 3 * k + 1 = w ^ 3 := by
  set b := 3 * k ^ 2 + 3 * k + 1
  have hb2 : IsCoprime b 2 := by
    obtain ⟨t, ht⟩ := Int.even_mul_succ_self k
    refine ⟨1, -(3 * t), ?_⟩
    dsimp [b]
    linear_combination 3 * ht
  have hb3 : IsCoprime b 3 := ⟨1, -(k ^ 2 + k), by dsimp [b]; ring⟩
  have hbk : IsCoprime b k := ⟨1, -(3 * k + 3), by dsimp [b]; ring⟩
  have hb9k : IsCoprime b (9 * k) := (hb3.mul_right hb3).mul_right hbk
  have hb36 : IsCoprime b 36 := (hb2.mul_right hb2).mul_right (hb3.mul_right hb3)
  -- Since `b` is coprime to `d`, the entire coefficient can be removed from `9 * k`.
  have hbd := hb36.of_isCoprime_of_dvd_right hd36
  obtain ⟨m, hm⟩ := hbd.symm.dvd_of_dvd_mul_right (show d ∣ (9 * k) * b from ⟨v ^ 3, h⟩)
  have hmb : m * b = v ^ 3 := by
    apply mul_left_cancel₀ hd0
    rwa [← mul_assoc, ← hm]
  rw [hm] at hb9k
  -- The integer odd-power splitting lemma handles both signs of `m` and `v`.
  exact Int.eq_pow_of_mul_eq_pow_odd_right hb9k.of_mul_right_right.symm (by decide) hmb

/-- **Integer solutions of $u^3 - d v^3 = 1$ for $d \in \{4, 18, 36\}$.** Let $d$ be one of the
integers $4$, $18$, $36$. For all integers $u$ and $v$, $u^3 - d v^3 = 1$ if and only if
$(u, v) = (1, 0)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 8
(`integers-2025-A103-lem-8`). -/
public theorem cube_sub_mul_cube_eq_one_iff_of_mem {d : ℤ}
    (hd : d = 4 ∨ d = 18 ∨ d = 36) (u v : ℤ) :
    u ^ 3 - d * v ^ 3 = 1 ↔ (u, v) = (1, 0) := by
  rw [Prod.mk.injEq]
  constructor
  · intro h
    have hd0 : d ≠ 0 := by rcases hd with rfl | rfl | rfl <;> decide
    have hd36 : d ∣ 36 := by rcases hd with rfl | rfl | rfl <;> decide
    obtain ⟨k, hk⟩ := three_dvd_sub_one_of_cube_sub_mul_cube_eq_one hd h
    have hu : u = 3 * k + 1 := by omega
    have hfac : (9 * k) * (3 * k ^ 2 + 3 * k + 1) = d * v ^ 3 := by
      rw [hu] at h
      linear_combination h
    obtain ⟨w, hw⟩ := quadratic_factor_is_cube hd0 hd36 hfac
    have hquadratic : u ^ 2 + u + 1 = 3 * w ^ 3 := by
      rw [hu, ← hw]
      ring
    rcases (sq_add_add_one_eq_three_mul_cube_iff u w).1.mp hquadratic with hneg | hone
    · have hu' : u = -2 := congrArg Prod.fst hneg
      -- At `u = -2`, the even number `d * v ^ 3` would have to equal `-9`.
      rw [hu'] at h
      rcases hd with rfl | rfl | rfl <;> norm_num at h <;> omega
    · have hu' : u = 1 := congrArg Prod.fst hone
      have hzero : d * v ^ 3 = 0 := by rw [hu'] at h; linear_combination -h
      exact ⟨hu', eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hzero).resolve_left hd0)⟩
  · rintro ⟨rfl, rfl⟩
    simp

end MetaMathlibExt
