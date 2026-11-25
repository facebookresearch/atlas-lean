/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularSmallSquares
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.Basic

/-!
# Odd powers of two under square–triangular additivity

Adding a power-of-two square to the triangular number at that square's index gives two
factorizations with the same power-of-two factor. Their odd cofactors differ by two.
-/

namespace MetaMathlibExt

open ArithmeticFunction

/-- **Square–triangular additivity fixes odd powers of two.** Let $t_v = v(v + 1)/2$ denote the
$v$-th triangular number, and let $f$ be a complex-valued multiplicative arithmetic function
with $f(u^2 + t_v) = f(u^2) + f(t_v)$ for all positive integers $u$ and $v$. Let $N \ge 4$ be an
integer such that $f(n) = n$ for every integer $n$ with $1 \le n \le N - 1$. Then
$f(2^{2k-1}) = 2^{2k-1}$ for every positive integer $k$ with $2k \le N - 2$.

Source: Mingyu Kim and Poo-Sung Park, *An Additive Uniqueness Pair of Sets for
Multiplicative Functions: Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A103,
Lemma 3 (`integers-2026-A103-lem-3`). -/
public theorem multiplicative_sq_triangular_additive_two_pow_odd
    (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
      f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))
    (N : ℕ) (hN : 4 ≤ N) (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ N - 1 → f n = n)
    (k : ℕ) (hk : 0 < k) (hkN : 2 * k ≤ N - 2) :
    f (2 ^ (2 * k - 1)) = 2 ^ (2 * k - 1) := by
  let a : ℕ := 2 ^ (2 * k - 1)
  let s : ℕ := 2 * a
  have hkpos : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  have hsq : s = (2 ^ k) ^ 2 := by
    change 2 * 2 ^ (2 * k - 1) = (2 ^ k) ^ 2
    have hexp : 2 * k - 1 + 1 = k * 2 := by omega
    rw [← pow_mul, ← hexp, pow_succ, mul_comm]
  have hspos : 0 < s := hsq ▸ pow_pos hkpos _
  have h3 : f 3 = 3 := hlt 3 (by decide) (by omega)
  have hfs : f s = (s : ℂ) := by
    by_cases hsmall : 2 ^ k ≤ N - 2
    · rw [hsq, Nat.cast_pow]
      exact multiplicative_sq_triangular_additive_sq f hf hadd N (by omega) hlt (2 ^ k)
        hkpos hsmall
    -- The stated bound is on 2 * k, not on the square root 2 ^ k. In the remaining case,
    -- start with Lemma 2 at 2 and propagate to larger squares using t₈ = 36.
    have h4 : f 4 = 4 := by
      have h := multiplicative_sq_triangular_additive_sq f hf hadd N (by omega) hlt 2
        (by decide) (by omega)
      norm_num at h
      exact h
    have h9 : f 9 = 9 := by
      have h := hadd 3 2 (by decide) (by decide)
      change f (4 * 3) = f 9 + f 3 at h
      rw [hf.map_mul_of_coprime (by decide : Nat.Coprime 4 3), h4, h3] at h
      linear_combination -h
    have h36 : f 36 = 36 := by
      change f (9 * 4) = 36
      rw [hf.map_mul_of_coprime (by decide : Nat.Coprime 9 4), h9, h4]
      norm_num
    have hfour (j : ℕ) : f (4 ^ (j + 1)) = ((4 ^ (j + 1) : ℕ) : ℂ) := by
      induction j with
      | zero => norm_num; exact h4
      | succ j ih =>
        let r : ℕ := 2 ^ (j + 1)
        let b : ℕ := 4 ^ (j + 1)
        have hb : b = r ^ 2 := by
          change ((2 : ℕ) ^ 2) ^ (j + 1) = (2 ^ (j + 1)) ^ 2
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        have hb2 : b % 2 = 0 := by
          dsimp [b]
          rw [Nat.pow_mod]
          simp
        have hb3 : b % 3 = 1 := by
          dsimp [b]
          rw [Nat.pow_mod]
          simp
        have hcop2 : Nat.Coprime 2 (b + 1) := Nat.coprime_two_left.mpr ⟨b / 2, by omega⟩
        have hcop3 : Nat.Coprime 3 (b + 1) :=
          (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr (by omega)
        have hcop36 : Nat.Coprime 36 (b + 1) := (hcop3.pow_left 2).mul_left (hcop2.pow_left 2)
        have hcop9 : Nat.Coprime 9 (b * 4) := by
          change Nat.Coprime (3 ^ 2) (4 ^ (j + 1 + 1))
          exact ((show Nat.Coprime 3 4 by decide).pow_right _).pow_left _
        have hr : 0 < r := pow_pos (by decide) _
        have hb1 : f (b + 1) = (b : ℂ) + 1 := by
          have h := hadd r 1 hr (by decide)
          rw [← hb] at h
          norm_num at h
          simpa only [hf.map_one, show f b = (b : ℂ) from ih] using h
        -- Compare additivity at (6r)² + t₈ with multiplicativity at 36(b + 1).
        have hstep : (6 * r) ^ 2 = 9 * (b * 4) := by rw [hb]; ring
        have hstep' : (6 * r) ^ 2 + 36 = 36 * (b + 1) := by rw [hb]; ring
        have h := hadd (6 * r) 8 (Nat.mul_pos (by decide) hr) (by decide)
        change f ((6 * r) ^ 2 + 36) = f ((6 * r) ^ 2) + f 36 at h
        rw [hstep', hstep, hf.map_mul_of_coprime hcop36, hf.map_mul_of_coprime hcop9,
          h36, h9, hb1] at h
        change f (b * 4) = ((b * 4 : ℕ) : ℂ)
        rw [Nat.cast_mul]
        norm_num
        linear_combination -h / 9
    rw [hsq, ← pow_mul, Nat.mul_comm k 2, pow_mul]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact hfour j
  have hfs1 : f (s + 1) = (s : ℂ) + 1 := by
    have h := hadd (2 ^ k) 1 hkpos (by decide)
    rw [← hsq] at h
    norm_num at h
    simpa only [hfs, hf.map_one] using h
  have hfs3 : f (s + 3) = (s : ℂ) + 3 := by
    have h := hadd (2 ^ k) 2 hkpos (by decide)
    rw [← hsq] at h
    norm_num at h
    simpa only [hfs, h3] using h
  have hcop1 : a.Coprime (s + 1) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by dsimp [s]; omega)).pow_left _
  have hcop3 : a.Coprime (s + 3) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by dsimp [s]; omega)).pow_left _
  -- Factor the triangular summand, then factor the whole sum.
  have htri : s * (s + 1) / 2 = a * (s + 1) := by
    rw [show s * (s + 1) = 2 * (a * (s + 1)) by dsimp [s]; ring]
    omega
  have hsum : s + a * (s + 1) = a * (s + 3) := by
    dsimp [s]
    ring
  have h := hadd (2 ^ k) s hkpos hspos
  rw [← hsq, htri, hsum, hf.map_mul_of_coprime hcop3, hf.map_mul_of_coprime hcop1,
    hfs, hfs3, hfs1] at h
  have hsCast : (s : ℂ) = 2 * (a : ℂ) := by simp [s]
  rw [hsCast] at h
  change f a = (2 : ℂ) ^ (2 * k - 1)
  rw [← Nat.cast_ofNat (R := ℂ) (n := 2), ← Nat.cast_pow]
  exact (show f a = (a : ℂ) by linear_combination h / 2)

end MetaMathlibExt
