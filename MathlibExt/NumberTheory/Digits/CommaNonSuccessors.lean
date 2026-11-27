/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.CommaParent

/-!
# Numbers that are not comma successors

`MetaMathlibExt.not_commaSucc_iff` shows that in every base `b ≥ 3`, a number `n ≥ b ^ 2 - 1`
is not the comma successor of any positive integer if and only if `n = c * b ^ i` with `i ≥ 2`
and `2 ≤ c ≤ b - 1`.

The proof follows the argument of the paper (arXiv:2401.14346, Theorem 5.4). A number
`n ≥ b ^ 2` is a comma-child of a positive integer `k` (`exists_commaParent_of_sq_le`), and `n` is
the comma successor of `k` unless a digit `y` smaller than the leading digit `f` of `n` is also a
comma candidate for `k`, that is, unless `n - f + y` has leading digit `y`. This happens exactly
when `f ≥ 2`, `y = f - 1` and `n = f * b ^ i`: then `k` has the smaller child `n - 1`. The
threshold number `b ^ 2 - 1` is the comma successor of `(b - 1) * b`.
-/

namespace MetaMathlibExt

namespace not_commaSucc_iff

/-- The leading digit of `m` is `m / b ^ L` when `b ^ L ≤ m < b ^ (L + 1)`. -/
private theorem commaMsd_eq_div {b m L : ℕ} (h₁ : b ^ L ≤ m) (h₂ : m < b ^ (L + 1)) :
    commaMsd b m = m / b ^ L := by
  unfold commaMsd
  rw [Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂]

/-- In base `b ≥ 2`, a positive number has a positive leading digit. -/
private theorem commaMsd_pos {b m : ℕ} (hb : 2 ≤ b) (hm : 0 < m) : 0 < commaMsd b m :=
  Nat.div_pos (Nat.pow_log_le_self b hm.ne') (Nat.pow_pos (by omega))

/-- In base `b ≥ 2`, the leading digit is a digit. -/
private theorem commaMsd_lt {b : ℕ} (hb : 2 ≤ b) (m : ℕ) : commaMsd b m < b :=
  (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).2 <| by
    simpa only [Nat.pow_succ'] using Nat.lt_pow_succ_log_self hb m

/-- The leading digit of `c * b ^ i + r` is `c` when `1 ≤ c < b` and `r < b ^ i`. -/
private theorem commaMsd_mul_pow_add {b c r : ℕ} (i : ℕ) (hc : 0 < c) (hcb : c < b)
    (hr : r < b ^ i) : commaMsd b (c * b ^ i + r) = c := by
  have hlo : c * b ^ i ≤ c * b ^ i + r := Nat.le_add_right _ _
  have hhi : c * b ^ i + r < (c + 1) * b ^ i := by rw [Nat.succ_mul]; omega
  rw [commaMsd_eq_div (L := i), Nat.div_eq_of_lt_le hlo hhi]
  · calc b ^ i ≤ c * b ^ i := Nat.le_mul_of_pos_left _ hc
      _ ≤ _ := hlo
  · calc c * b ^ i + r < (c + 1) * b ^ i := hhi
      _ ≤ b * b ^ i := Nat.mul_le_mul_right _ hcb
      _ = b ^ (i + 1) := (pow_succ' b i).symm

/-- If `b ≤ n` and a digit `y` below the leading digit `f` of `n` is the leading digit of
`n - f + y`, then `f ≥ 2` and `n = f * b ^ L`, where `L` is the base-`b` logarithm of `n`. -/
private theorem eq_mul_pow_of_commaMsd_eq {b n y : ℕ} (hb : 2 ≤ b) (hn : b ≤ n)
    (hy : y < commaMsd b n) (hm : 0 < n - commaMsd b n + y)
    (hmsd : commaMsd b (n - commaMsd b n + y) = y) :
    2 ≤ commaMsd b n ∧ n = commaMsd b n * b ^ Nat.log b n := by
  have hf : commaMsd b n = n / b ^ Nat.log b n := rfl
  generalize hf' : commaMsd b n = f at hy hm hmsd hf ⊢
  generalize hL : Nat.log b n = L at hf
  have hL1 : 1 ≤ L := hL ▸ Nat.le_log_of_pow_le hb (by simpa using hn)
  have hPn : b ^ L ≤ n := hL ▸ Nat.pow_log_le_self b (by omega)
  have hnP : n < b ^ (L + 1) := hL ▸ Nat.lt_pow_succ_log_self hb n
  have hfb : f < b := hf' ▸ commaMsd_lt hb n
  have hbP : b ≤ b ^ L := by
    calc b = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ L := Nat.pow_le_pow_right (by omega) hL1
  generalize hP : b ^ L = P at hPn hnP hbP hf
  have hfPn : f * P ≤ n := hf ▸ Nat.div_mul_le_self n P
  -- the smaller candidate `y` is a nonzero digit, so `f ≥ 2` and `n ≥ 2 * P`
  have hy1 : 1 ≤ y := hmsd ▸ commaMsd_pos hb hm
  have h2P : 2 * P ≤ f * P := Nat.mul_le_mul_right _ (by omega)
  -- so `n - f + y` has the same number of digits as `n`
  have hm₁ : P ≤ n - f + y := by omega
  rw [commaMsd_eq_div (hP ▸ hm₁) (by omega), hP] at hmsd
  -- its leading digit is at least `f - 1`, so `y = f - 1`
  have hge : (n - P * 1) / P ≤ y := hmsd ▸ Nat.div_le_div_right (by omega)
  rw [Nat.sub_mul_div, ← hf] at hge
  have hyf : y = f - 1 := by omega
  -- and `n - 1` has a smaller leading digit than `n`, so `b ^ L` divides `n`
  have hdvd : P ∣ n := by
    by_contra hnd
    have hsucc := Nat.succ_div_of_not_dvd (a := n - 1) (b := P)
      (by rwa [Nat.sub_add_cancel (by omega)])
    rw [Nat.sub_add_cancel (by omega), ← hf] at hsucc
    have h' : n - f + y = n - 1 := by omega
    rw [h'] at hmsd
    omega
  exact ⟨by omega, by rw [hf, Nat.div_mul_cancel hdvd]⟩

end not_commaSucc_iff

open not_commaSucc_iff in
/-- **Numbers that are not comma successors.** Let $b \ge 3$ and $n \ge b^2 - 1$. Then $n$ is not
the comma successor in base $b$ of any positive integer if and only if $n = c\, b^i$ for some
$i \ge 2$ and some $c$ with $2 \le c \le b - 1$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.4 (`fq-2024-sloane05302024-thm-5.4`). -/
public theorem not_commaSucc_iff (b n : ℕ) (hb : 3 ≤ b) (hn : b ^ 2 - 1 ≤ n) :
    (¬ ∃ k : ℕ, 0 < k ∧ IsCommaSucc b k n) ↔
      ∃ c i : ℕ, 2 ≤ i ∧ 2 ≤ c ∧ c ≤ b - 1 ∧ n = c * b ^ i := by
  have hbb : (b - 1) * b = b ^ 2 - b := by rw [Nat.sub_one_mul, sq]
  have hbsq : b + 1 ≤ b ^ 2 := by
    have : 3 * b ≤ b * b := Nat.mul_le_mul_right b hb
    rw [sq]; omega
  constructor
  · intro h
    rcases Nat.lt_or_ge n (b ^ 2) with hlt | hge
    · -- `n = b ^ 2 - 1` is the comma successor of `(b - 1) * b`
      exfalso
      have hmod : (b - 1) * b % b = 0 := Nat.mul_mod_left _ _
      have hdig (y : ℕ) (hy : y < b) :
          commaMsd b ((b - 1) * b + b * ((b - 1) * b % b) + y) = b - 1 := by
        rw [hmod, Nat.mul_zero, Nat.add_zero]
        simpa only [Nat.pow_one] using
          commaMsd_mul_pow_add (b := b) (c := b - 1) (r := y) 1 (by omega) (by omega)
            (by simpa only [Nat.pow_one] using hy)
      refine h ⟨(b - 1) * b, Nat.mul_pos (by omega) (by omega), ⟨b - 1, by omega⟩,
        ⟨by omega, hdig _ (by omega)⟩, ?_, ?_⟩
      · change n = (b - 1) * b + b * ((b - 1) * b % b) + (b - 1)
        rw [hmod]
        omega
      · intro y' hy' hcand
        have h2 := hcand.2
        rw [hdig _ y'.isLt] at h2
        omega
    · -- `n ≥ b ^ 2` has a positive parent `k`, which has a smaller comma candidate
      obtain ⟨k, hk, y, hy, hny⟩ := exists_commaParent_of_sq_le b n (by omega) hge
      obtain ⟨y', hy'y, hy'⟩ : ∃ y' : Fin b, y'.val < y.val ∧ IsCommaCandidate b k y' := by
        by_contra hcon
        exact h ⟨k, hk, y, hy, hny, fun y' hy'y hy' => hcon ⟨y', hy'y, hy'⟩⟩
      have hyf : commaMsd b n = y.val := by
        have h2 := hy.2
        rwa [← hny] at h2
      have harg : k + b * (k % b) + y'.val = n - commaMsd b n + y'.val := by omega
      obtain ⟨hf2, hnf⟩ := eq_mul_pow_of_commaMsd_eq (by omega) (by omega) (hyf ▸ hy'y)
        (harg ▸ hy'.1) (harg ▸ hy'.2)
      refine ⟨commaMsd b n, Nat.log b n, Nat.le_log_of_pow_le (by omega) hge, hf2, ?_, hnf⟩
      have := commaMsd_lt (by omega : 2 ≤ b) n
      omega
  · -- the parent of `c * b ^ i` also has the smaller child `c * b ^ i - 1`
    rintro ⟨c, i, hi, hc2, hcb, rfl⟩ ⟨k, hk, y, hy, hny, hmin⟩
    have hyc : y.val = c := by
      have h2 := hy.2
      rw [← hny, ← Nat.add_zero (c * b ^ i), commaMsd_mul_pow_add i (by omega) (by omega)
        (Nat.pow_pos (by omega))] at h2
      exact h2.symm
    refine hmin ⟨c - 1, by omega⟩ (by simp only; omega) ⟨by simp only; omega, ?_⟩
    have hpow : 0 < b ^ i := Nat.pow_pos (by omega)
    have hsub : (c - 1) * b ^ i = c * b ^ i - b ^ i := Nat.sub_one_mul _ _
    have harg : k + b * (k % b) + (c - 1) = (c - 1) * b ^ i + (b ^ i - 1) := by
      have : b ^ i ≤ c * b ^ i := Nat.le_mul_of_pos_left _ (by omega)
      omega
    simp only
    rw [harg]
    exact commaMsd_mul_pow_add i (by omega) (by omega) (by omega)

end MetaMathlibExt
