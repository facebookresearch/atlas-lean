/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensor

/-! # Re-spaced compact tensor columns and cross comparison of packed tensors

Kernel-feasible copies of dense packed tensors: a column is stored compactly with `k`-bit fields
and re-spaced to field width `w` by `respace` (a balanced split, so the kernel work is
`O(n log n)` bits per column); `respace_spec` keeps the fields.  Two packed tensors with bounded
fields have the same rational tensor when the cross sums `x.1 + y.2` and `y.1 + x.2` of all
columns agree (`tensorRat_eq_of_cross`): one big-number addition per column instead of one
field extraction per entry. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Re-space `2 ^ d` fields of `k` bits into fields of `w` bits. -/
def respace (k w : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | d + 1, x => respace k w d (x % 2 ^ (k * 2 ^ d)) |||
      (respace k w d (x >>> (k * 2 ^ d)) <<< (w * 2 ^ d))

/-- High fields of a number below `2 ^ (w * m)` vanish. -/
theorem fld_eq_zero_of_lt {w m P i : ℕ} (hP : P < 2 ^ (w * m)) (hi : m ≤ i) : fld w P i = 0 := by
  unfold fld
  have : P / 2 ^ (w * i) = 0 :=
    Nat.div_eq_of_lt (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left w hi)))
  rw [this, Nat.zero_mod]

/-- Low fields survive a reduction modulo a whole number of fields. -/
theorem fld_mod_pow {k m x i : ℕ} (hi : i < m) : fld k (x % 2 ^ (k * m)) i = fld k x i := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, testBit_fld, Nat.testBit_mod_two_pow]
  by_cases hb : b < k
  · have : k * i + b < k * m := by
      have : k * (i + 1) ≤ k * m := Nat.mul_le_mul_left k hi
      rw [Nat.mul_succ] at this; omega
    simp [hb, this]
  · simp [hb]

/-- Bounds and fields of a re-spaced number. -/
theorem respace_spec (k w : ℕ) (hkw : k ≤ w) : ∀ (d x : ℕ), x < 2 ^ (k * 2 ^ d) →
    respace k w d x < 2 ^ (w * 2 ^ d) ∧
      ∀ i, fld w (respace k w d x) i = if i < 2 ^ d then fld k x i else 0
  | 0, x, hx => by
    simp only [respace, pow_zero, mul_one] at hx ⊢
    have hxw : x < 2 ^ w := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hkw)
    refine ⟨hxw, fun i => ?_⟩
    split_ifs with hi
    · have : i = 0 := by omega
      subst this
      simp only [fld, mul_zero, pow_zero, Nat.div_one]
      rw [Nat.mod_eq_of_lt hxw, Nat.mod_eq_of_lt hx]
    · exact fld_eq_zero_of_lt (m := 1) (by simpa using hxw) (by omega)
  | d + 1, x, hx => by
    have hM : 0 < 2 ^ d := by positivity
    have hlo : x % 2 ^ (k * 2 ^ d) < 2 ^ (k * 2 ^ d) := Nat.mod_lt _ (by positivity)
    have hhi : x >>> (k * 2 ^ d) < 2 ^ (k * 2 ^ d) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      calc x < 2 ^ (k * 2 ^ (d + 1)) := hx
        _ = 2 ^ (k * 2 ^ d + k * 2 ^ d) := by rw [pow_succ]; ring_nf
    obtain ⟨a1, a2⟩ := respace_spec k w hkw d _ hlo
    obtain ⟨b1, b2⟩ := respace_spec k w hkw d _ hhi
    simp only [respace]
    constructor
    · apply Nat.or_lt_two_pow
      · calc _ < 2 ^ (w * 2 ^ d) := a1
          _ ≤ 2 ^ (w * 2 ^ (d + 1)) := Nat.pow_le_pow_right (by norm_num)
              (Nat.mul_le_mul_left w (Nat.pow_le_pow_right (by norm_num) (by omega)))
      · rw [Nat.shiftLeft_eq]
        calc _ < 2 ^ (w * 2 ^ d) * 2 ^ (w * 2 ^ d) :=
              Nat.mul_lt_mul_of_pos_right b1 (by positivity)
          _ = 2 ^ (w * 2 ^ (d + 1)) := by rw [← pow_add, pow_succ]; ring_nf
    · intro i
      rw [fld_lor, fld_shiftLeft, a2, b2]
      by_cases h1 : i < 2 ^ d
      · have h2 : i < 2 ^ (d + 1) := by rw [pow_succ]; omega
        simp only [h1, h2, ↓reduceIte, show ¬ (2 ^ d ≤ i) by omega, Nat.or_zero]
        exact fld_mod_pow h1
      · simp only [h1, ↓reduceIte, show 2 ^ d ≤ i by omega, Nat.zero_or]
        by_cases h3 : i - 2 ^ d < 2 ^ d
        · have h2 : i < 2 ^ (d + 1) := by rw [pow_succ]; omega
          simp only [h3, h2, ↓reduceIte]
          rw [fld_shiftRight]
          congr 1
          omega
        · have h2 : ¬ i < 2 ^ (d + 1) := by rw [pow_succ]; omega
          simp only [h3, h2, ↓reduceIte]

/-- A column re-spaced from compact `k`-bit fields: bounds and values. -/
theorem respace_col {k w : ℕ} (hkw : k ≤ w) {P N : ℕ} (hP : P < 2 ^ (k * 2 ^ 12))
    (hN : N < 2 ^ (k * 2 ^ 12)) :
    SBnd w (2 ^ 12) (2 ^ k - 1) (respace k w 12 P, respace k w 12 N) ∧
      ∀ t < 2 ^ 12,
        sval w (respace k w 12 P, respace k w 12 N) t = (fld k P t : ℤ) - fld k N t := by
  obtain ⟨p1, p2⟩ := respace_spec k w hkw 12 _ hP
  obtain ⟨n1, n2⟩ := respace_spec k w hkw 12 _ hN
  refine ⟨⟨p1, n1, fun t ht => ?_⟩, fun t ht => ?_⟩
  · simp only [p2, n2, ht, ↓reduceIte]
    have a := fld_lt k P t
    have b := fld_lt k N t
    constructor <;> omega
  · simp only [sval, p2, n2, ht, ↓reduceIte]

/-- Equal cross sums of two bounded signed packed vectors give equal values. -/
theorem sval_eq_of_cross {w n B : ℕ} {x y : SVec} (hx : SBnd w n B x) (hy : SBnd w n B y)
    (hB : 2 * B < 2 ^ w) (h : x.1 + y.2 = y.1 + x.2) : ∀ k < n, sval w x k = sval w y k := by
  have a := fld_add w n x.1 y.2 hx.1 hy.2.1 (fun i hi => by
    have := (hx.2.2 i hi).1; have := (hy.2.2 i hi).2; omega)
  have b := fld_add w n y.1 x.2 hy.1 hx.2.1 (fun i hi => by
    have := (hy.2.2 i hi).1; have := (hx.2.2 i hi).2; omega)
  intro k hk
  have e : fld w (x.1 + y.2) k = fld w (y.1 + x.2) k := by rw [h]
  rw [a.2 k hk, b.2 k hk] at e
  simp only [sval]
  omega

/-- Packed tensors with bounded fields and equal cross sums have the same rational tensor. -/
theorem tensorRat_eq_of_cross {w B : ℕ} {X Y : List SVec} (hX : TBnd w B X) (hY : TBnd w B Y)
    (hB : 2 * B < 2 ^ w)
    (h : (List.range 24).all (fun j =>
      (tcol X j).1 + (tcol Y j).2 == (tcol Y j).1 + (tcol X j).2) = true) (D : ℚ) :
    tensorRat w X D = tensorRat w Y D := by
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  funext k i
  simp only [tensorRat]
  rw [sval_eq_of_cross (hX i.val i.isLt) (hY i.val i.isLt) hB (h i.val i.isLt) k.val
    (lt_of_lt_of_le k.isLt (by norm_num))]

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
