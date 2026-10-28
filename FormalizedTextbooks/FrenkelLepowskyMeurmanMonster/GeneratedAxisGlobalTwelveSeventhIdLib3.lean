/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveSeventhIdLib2

/-! # Normalized packed tensors from compact literals

The packed tensors of word images carry positive and negative parts that do not cancel, and
computing them in the kernel is the dominant memory cost of an identification part.  A packed
tensor with the same rational tensor and cancelled parts can be given as a compact literal
(`k`-bit fields) and widened to `w`-bit fields by halving (`widenH`, logarithmic depth); one
packed cross-sum check per column (`tensorRat_eq_of_cross`) certifies it against the computed
tensor.  Nothing here assumes any identification. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- Widen `2^m` fields of `k` bits to `2^m` fields of `w` bits, by halving. -/
def widenH (k w : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | m + 1, x => widenH k w m (x % 2 ^ (k * 2 ^ m)) +
      widenH k w m (x >>> (k * 2 ^ m)) <<< (w * 2 ^ m)

/-- Fields of a residue modulo a whole number of fields. -/
theorem fld_mod_pow (k x n t : ℕ) (ht : t < n) : fld k (x % 2 ^ (k * n)) t = fld k x t := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld, testBit_fld]
  by_cases hb : b < k
  · simp only [hb, decide_true, Bool.true_and, Nat.testBit_mod_two_pow]
    have : k * t + b < k * n := by
      have : k * (t + 1) ≤ k * n := Nat.mul_le_mul_left k ht
      rw [Nat.mul_succ] at this; omega
    simp [this]
  · simp [hb]

/-- Fields above a bound vanish. -/
theorem fld_zero_of_lt (w x n t : ℕ) (hx : x < 2 ^ (w * n)) (ht : n ≤ t) : fld w x t = 0 := by
  unfold fld
  have : x / 2 ^ (w * t) = 0 := by
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w ht))
  rw [this, Nat.zero_mod]

/-- Widening zero gives zero. -/
theorem widenH_zero (k w : ℕ) : ∀ m : ℕ, widenH k w m 0 = 0
  | 0 => rfl
  | m + 1 => by
    change widenH k w m (0 % 2 ^ (k * 2 ^ m)) + widenH k w m (0 >>> (k * 2 ^ m)) <<< (w * 2 ^ m) = 0
    rw [Nat.zero_mod, Nat.zero_shiftRight, widenH_zero k w m, Nat.zero_shiftLeft]

/-- Widening is exact: the widened number has the same fields. -/
theorem widenH_spec (k w : ℕ) (hk : k ≤ w) : ∀ (m x : ℕ), x < 2 ^ (k * 2 ^ m) →
    widenH k w m x < 2 ^ (w * 2 ^ m) ∧ ∀ t < 2 ^ m, fld w (widenH k w m x) t = fld k x t
  | 0, x, hx => by
    have hw : widenH k w 0 x = x := rfl
    rw [hw]
    simp only [pow_zero, mul_one] at hx ⊢
    have hxw : x < 2 ^ w := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hk)
    refine ⟨hxw, fun t ht => ?_⟩
    have ht0 : t = 0 := by omega
    subst ht0
    rw [fld_zero_right, fld_zero_right, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hxw]
  | m + 1, x, hx => by
    have h2 : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    change widenH k w m (x % 2 ^ (k * 2 ^ m)) + widenH k w m (x >>> (k * 2 ^ m)) <<< (w * 2 ^ m) <
        2 ^ (w * 2 ^ (m + 1)) ∧ ∀ t < 2 ^ (m + 1), fld w (widenH k w m (x % 2 ^ (k * 2 ^ m)) +
          widenH k w m (x >>> (k * 2 ^ m)) <<< (w * 2 ^ m)) t = fld k x t
    rw [h2] at hx ⊢
    have hlo : x % 2 ^ (k * 2 ^ m) < 2 ^ (k * 2 ^ m) := Nat.mod_lt _ (by positivity)
    have hhi : x >>> (k * 2 ^ m) < 2 ^ (k * 2 ^ m) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
        ← Nat.mul_add]
      exact hx
    obtain ⟨a1, a2⟩ := widenH_spec k w hk m _ hlo
    obtain ⟨b1, b2⟩ := widenH_spec k w hk m _ hhi
    generalize widenH k w m (x % 2 ^ (k * 2 ^ m)) = A at a1 a2 ⊢
    generalize widenH k w m (x >>> (k * 2 ^ m)) = B at b1 b2 ⊢
    have hBs : B <<< (w * 2 ^ m) < 2 ^ (w * (2 ^ m + 2 ^ m)) := by
      rw [Nat.shiftLeft_eq, Nat.mul_add, pow_add, Nat.mul_comm (2 ^ (w * 2 ^ m))]
      exact Nat.mul_lt_mul_of_pos_right b1 (by positivity)
    have hA : A < 2 ^ (w * (2 ^ m + 2 ^ m)) :=
      lt_of_lt_of_le a1 (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left w (Nat.le_add_right _ _)))
    have hsum := fld_add w (2 ^ m + 2 ^ m) A (B <<< (w * 2 ^ m)) hA hBs (fun i _ => by
      rw [fld_shiftLeft]
      split_ifs with hm
      · rw [fld_zero_of_lt w A (2 ^ m) i a1 hm, zero_add]
        exact fld_lt _ _ _
      · rw [add_zero]
        exact fld_lt _ _ _)
    refine ⟨hsum.1, fun t ht => ?_⟩
    rw [hsum.2 t ht, fld_shiftLeft]
    have hs := fld_shiftRight k x (2 ^ m) (t - 2 ^ m)
    generalize hh : 2 ^ m = h at *
    split_ifs with hm
    · rw [fld_zero_of_lt w A h t a1 hm, zero_add, b2 (t - h) (by omega), hs,
        Nat.sub_add_cancel hm]
    · rw [add_zero, a2 t (by omega), fld_mod_pow k x h t (by omega)]

/-- A packed tensor widened from compact literal columns (positive and negative parts). -/
def widenT (k w : ℕ) (cols : List (ℕ × ℕ)) : List SVec :=
  cols.map (fun c => (widenH k w 12 c.1, widenH k w 12 c.2))

/-- Bounds of a widened packed tensor. -/
theorem widenT_bnd (k w : ℕ) (hk : k ≤ w) (cols : List (ℕ × ℕ))
    (hc : cols.all (fun c => decide (c.1 < 2 ^ (k * 2 ^ 12)) && decide (c.2 < 2 ^ (k * 2 ^ 12))) =
      true) : TBnd w (2 ^ k - 1) (widenT k w cols) := by
  intro i _
  have hd : tcol (widenT k w cols) i = (widenH k w 12 (cols.getD i (0, 0)).1,
      widenH k w 12 (cols.getD i (0, 0)).2) := by
    unfold tcol widenT
    have h0 : (szero : SVec) = (fun c : ℕ × ℕ => (widenH k w 12 c.1, widenH k w 12 c.2)) (0, 0) := by
      simp only [szero, widenH_zero]
    rw [h0, List.getD_map]
  rw [hd]
  have hm : ∀ c ∈ cols, c.1 < 2 ^ (k * 2 ^ 12) ∧ c.2 < 2 ^ (k * 2 ^ 12) := by
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc
  have hci : (cols.getD i (0, 0)).1 < 2 ^ (k * 2 ^ 12) ∧ (cols.getD i (0, 0)).2 < 2 ^ (k * 2 ^ 12) := by
    by_cases hi : i < cols.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hm _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨by positivity, by positivity⟩
  obtain ⟨p1, p2⟩ := widenH_spec k w hk 12 _ hci.1
  obtain ⟨q1, q2⟩ := widenH_spec k w hk 12 _ hci.2
  refine ⟨p1, q1, fun t ht => ⟨?_, ?_⟩⟩
  · rw [p2 t ht]; have := fld_lt k (cols.getD i (0, 0)).1 t; omega
  · rw [q2 t ht]; have := fld_lt k (cols.getD i (0, 0)).2 t; omega

/-- Two packed tensors with equal cross sums in every column have the same rational tensor. -/
theorem tensorRat_eq_of_cross (w : ℕ) {X Y : List SVec} {B C : ℕ} (hX : TBnd w B X)
    (hY : TBnd w C Y) (hBC : B + C < 2 ^ w)
    (h : ∀ j < 24, (tcol X j).1 + (tcol Y j).2 = (tcol Y j).1 + (tcol X j).2) (D : ℚ) :
    tensorRat w X D = tensorRat w Y D := by
  funext k i
  unfold tensorRat
  rw [sval_eq_of_cross (hX i.val i.isLt) (hY i.val i.isLt) hBC (h i.val i.isLt) k.val k.isLt]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
