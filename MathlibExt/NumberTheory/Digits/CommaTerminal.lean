/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.NumberTheory.CommaSequence

/-!
# Terminal numbers of the comma sequence

The possible children of `n` lie in a window of `b` consecutive integers starting at
`n + b * (n % b)`. Unless the window crosses a power of `b`, one of the at most two
leading digits in it gives a child. At a power of `b`, the leading digit goes from
`b - 1` to `1`; both choices fail exactly when the power is at least two steps into
the window.
-/

namespace MetaMathlibExt

private theorem commaMsd_eq_div_pow {b m k : ℕ} (hlo : b ^ k ≤ m) (hhi : m < b ^ (k + 1)) :
    commaMsd b m = m / b ^ k := by
  rw [commaMsd, Nat.log_eq_of_pow_le_of_lt_pow hlo hhi]

-- A window of `b` consecutive integers, starting at `a` of place value `b ^ k`,
-- has no fixed leading digit precisely at a rollover that occurs after the first step.
private theorem no_fixed_digit_iff {b a k : ℕ} (hb : 2 ≤ b) (hbp : b ≤ b ^ k)
    (hlo : b ^ k ≤ a) (hhi : a < b * b ^ k) :
    (∀ y < b, commaMsd b (a + y) ≠ y) ↔ a + 1 < b * b ^ k ∧ b * b ^ k ≤ a + (b - 1) := by
  let p := b ^ k
  let t := b * p
  change b ≤ p at hbp
  change p ≤ a at hlo
  change a < t at hhi
  change _ ↔ a + 1 < t ∧ t ≤ a + (b - 1)
  have ht : b ^ (k + 1) = t := pow_succ' b k
  have hp : 0 < p := by omega
  have hbt : b ≤ t := hbp.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hbelow (y : ℕ) (hy : a + y < t) : commaMsd b (a + y) = (a + y) / p :=
    commaMsd_eq_div_pow (by change p ≤ a + y; omega) (ht ▸ hy)
  have habove (y : ℕ) (hy : y < b) (h : t ≤ a + y) : commaMsd b (a + y) = 1 := by
    have hnext : 2 * t ≤ b * t := Nat.mul_le_mul_right _ hb
    have hlt : a + y < 2 * t := by omega
    have h' : a + y < b ^ (k + 1 + 1) := by
      rw [pow_succ', ht]
      exact hlt.trans_le hnext
    rw [commaMsd_eq_div_pow (ht ▸ h) h', ht]
    exact Nat.div_eq_of_lt_le (by simpa only [one_mul] using h) (by simpa using hlt)
  by_cases hcross : t ≤ a + (b - 1)
  · have hlast : (b - 1) * p ≤ a := by
      rw [Nat.sub_one_mul]
      change t - p ≤ a
      omega
    have hd (y : ℕ) (hy : a + y < t) : commaMsd b (a + y) = b - 1 := by
      rw [hbelow y hy]
      exact Nat.div_eq_of_lt_le (by omega : (b - 1) * p ≤ a + y) (by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ b)]
        exact hy)
    constructor
    · intro h
      refine ⟨?_, hcross⟩
      by_contra! h1
      exact h 1 (by omega) (habove 1 (by omega) h1)
    · rintro ⟨h1, -⟩ y hy h
      by_cases hyt : a + y < t
      · rw [hd y hyt] at h
        omega
      · rw [habove y hy (by omega)] at h
        omega
  · have hwindow (y : ℕ) (hy : y < b) : a + y < t := by omega
    let q := a / p
    have hqa : q * p ≤ a := Nat.div_mul_le_self a p
    have haq : a < (q + 1) * p := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self q)
    have hqb : q < b := (Nat.div_lt_iff_lt_mul hp).mpr hhi
    refine iff_of_false ?_ (fun h ↦ hcross h.2)
    intro h
    by_cases hq : a + q < (q + 1) * p
    · exact h q hqb ((hbelow q (hwindow q hqb)).trans
        (Nat.div_eq_of_lt_le (hqa.trans (Nat.le_add_right _ _)) hq))
    · have hsucc : q + 1 < b := by
        by_contra! hsucc
        have heq : q + 1 = b := by omega
        rw [heq] at hq
        exact hq (hwindow q hqb)
      have hupper : a + (q + 1) < (q + 1 + 1) * p := by
        rw [Nat.add_mul, one_mul]
        exact add_lt_add_of_lt_of_le haq (hsucc.le.trans hbp)
      exact h (q + 1) hsucc ((hbelow _ (hwindow _ hsucc)).trans
        (Nat.div_eq_of_lt_le (by omega : (q + 1) * p ≤ a + (q + 1)) hupper))

-- Express the rollover in terms of the quotient and remainder of `n`.
private theorem terminal_iff_carry {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    IsCommaTerminal b n ↔ ∃ k, 1 ≤ k ∧ n / b + n % b + 1 = b ^ k ∧
      1 ≤ n % b ∧ n % b ≤ b - 2 := by
  let r := n % b
  let q := n / b + r
  let a := n + b * r
  have hr : r < b := Nat.mod_lt _ (by omega)
  have ha : a = q * b + r := calc
    a = (r + b * (n / b)) + b * r := by rw [Nat.mod_add_div]
    _ = q * b + r := by dsimp [q]; ring
  have hdiv : a / b = q := by
    rw [ha]
    apply Nat.div_eq_of_lt_le (Nat.le_add_right _ _)
    rw [Nat.add_mul q 1 b, one_mul]
    exact Nat.add_lt_add_left hr _
  have hba : b ≤ a := by
    by_cases hnb : n < b
    · have hrn : r = n := Nat.mod_eq_of_lt hnb
      have : b ≤ b * r := Nat.le_mul_of_pos_right _ (by omega)
      change b ≤ n + b * r
      omega
    · change b ≤ n + b * r
      omega
  have hterm : IsCommaTerminal b n ↔ ∀ y < b, commaMsd b (a + y) ≠ y := by
    constructor
    · intro h y hy hfix
      exact h ⟨y, hy⟩ ⟨by change 0 < a + y; omega, hfix⟩
    · intro h y hy
      exact h y.val y.isLt hy.2
  have hbp (k : ℕ) (hk : 1 ≤ k) : b ≤ b ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < b) hk
  rw [hterm]
  change _ ↔ ∃ k, 1 ≤ k ∧ q + 1 = b ^ k ∧ 1 ≤ r ∧ r ≤ b - 2
  constructor
  · intro h
    let k := Nat.log b a
    have hk : 1 ≤ k := Nat.le_log_of_pow_le hb (by simpa only [pow_one] using hba)
    have hlt : a < b * b ^ k := by
      rw [← pow_succ']
      exact Nat.lt_pow_succ_log_self hb a
    obtain ⟨h1, hroll⟩ := (no_fixed_digit_iff hb (hbp k hk)
      (Nat.pow_log_le_self b (by omega)) hlt).mp h
    have hpk : 1 ≤ b ^ k := (by omega : 1 ≤ b).trans (hbp k hk)
    have hdiv' : a / b = b ^ k - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.sub_one_mul, Nat.mul_comm (b ^ k) b]
        omega
      · rw [Nat.sub_add_cancel hpk, Nat.mul_comm (b ^ k) b]
        exact hlt
    have hq : q + 1 = b ^ k := by
      rw [hdiv] at hdiv'
      rw [hdiv', Nat.sub_add_cancel hpk]
    have hsum : b * b ^ k = q * b + b := by rw [← hq, Nat.mul_comm b, Nat.add_mul, one_mul]
    rw [hsum, ha] at h1 hroll
    exact ⟨k, hk, hq, by omega, by omega⟩
  · rintro ⟨k, hk, hq, hr₁, hr₂⟩
    have hsum : b * b ^ k = q * b + b := by rw [← hq, Nat.mul_comm b, Nat.add_mul, one_mul]
    have hpow : b ^ k ≤ a := by
      have htwo := Nat.mul_le_mul_right (b ^ k) hb
      have := hbp k hk
      omega
    exact (no_fixed_digit_iff hb (hbp k hk) hpow (by omega)).mpr ⟨by omega, by omega⟩

private theorem digits_pow_sub_one {b : ℕ} (hb : 2 ≤ b) (i : ℕ) :
    Nat.digits b (b ^ i - 1) = List.replicate i (b - 1) := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hm : b ≤ b * b ^ i := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
      have h : b ^ (i + 1) - 1 = (b - 1) + b * (b ^ i - 1) := by
        rw [pow_succ', Nat.mul_sub, Nat.mul_one]
        omega
      rw [h, Nat.digits_add b hb _ _ (by omega) (Or.inl (by omega)), ih, List.replicate_succ]

/-- **Landmines of the comma sequence.** Let $b \ge 2$ and let $n$ be a positive integer. Then no
digit $y < b$ is a comma candidate for $n$ in base $b$ (so $n$ has no comma successor) if and
only if the base-$b$ representation of $n$, most significant digit first, is
$(b-1) \cdots (b-1)\, x\, (b-1-x)$ with some number $i \ge 0$ of leading digits $b - 1$ and
$1 \le x \le b - 2$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.1 (`fq-2024-sloane05302024-thm-5.1`). -/
public theorem isCommaTerminal_iff_digits (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) :
    IsCommaTerminal b n ↔ ∃ i x : ℕ, 1 ≤ x ∧ x ≤ b - 2 ∧
      Nat.digits b n = [b - 1 - x, x] ++ List.replicate i (b - 1) := by
  have hd (i x : ℕ) (hx₁ : 1 ≤ x) (hx₂ : x ≤ b - 2) :
      Nat.digits b ((b - 1 - x) + b * (x + b * (b ^ i - 1))) =
        [b - 1 - x, x] ++ List.replicate i (b - 1) := by
    rw [Nat.digits_add b hb _ _ (by omega) (Or.inl (by omega)),
      Nat.digits_add b hb _ _ (by omega) (Or.inl (by omega)), digits_pow_sub_one hb]
    rfl
  have hpow (i : ℕ) : b * (b ^ i - 1) + b = b ^ (i + 1) := by
    have hm : b ≤ b * b ^ i := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
    rw [pow_succ', Nat.mul_sub, Nat.mul_one, Nat.sub_add_cancel hm]
  rw [terminal_iff_carry hb hn]
  constructor
  · rintro ⟨k, hk, hcarry, hr₁, hr₂⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    let x := b - 1 - n % b
    have hx₁ : 1 ≤ x := by dsimp [x]; omega
    have hx₂ : x ≤ b - 2 := by dsimp [x]; omega
    have hr : b - 1 - x = n % b := by dsimp [x]; omega
    have hq : n / b = x + b * (b ^ i - 1) := by
      rw [← hpow] at hcarry
      dsimp [x]
      omega
    have hval : (b - 1 - x) + b * (x + b * (b ^ i - 1)) = n := by
      rw [hr, ← hq, Nat.mod_add_div]
    exact ⟨i, x, hx₁, hx₂, hval ▸ hd i x hx₁ hx₂⟩
  · rintro ⟨i, x, hx₁, hx₂, hdigits⟩
    have hval := Nat.digits.injective b (hdigits.trans (hd i x hx₁ hx₂).symm)
    have hr : n % b = b - 1 - x := by
      rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : b - 1 - x < b)]
    have hq : n / b = x + b * (b ^ i - 1) := by
      rw [hval, Nat.add_mul_div_left _ _ (by omega : 0 < b),
        Nat.div_eq_of_lt (by omega : b - 1 - x < b), zero_add]
    refine ⟨i + 1, by omega, ?_, by omega, by omega⟩
    rw [hq, hr, ← hpow]
    omega

end MetaMathlibExt
