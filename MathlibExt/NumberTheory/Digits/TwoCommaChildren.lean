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
# Numbers with two comma-children

`MetaMathlibExt.two_commaChildren_iff` classifies the positive integers with two comma-children
by their base-`b` digits.
-/

namespace MetaMathlibExt
namespace two_commaChildren_iff

private abbrev HasTwo (b n : ℕ) :=
  ∃ y z : Fin b, y ≠ z ∧ IsCommaCandidate b n y ∧ IsCommaCandidate b n z

/-- At a fixed place value, the leading digit is determined by two consecutive multiples. -/
private theorem msd_eq_iff {b m L : ℕ} (hb : 2 ≤ b) (hlo : b ^ L ≤ m)
    (hhi : m < b ^ (L + 1)) (y : ℕ) :
    commaMsd b m = y ↔ y * b ^ L ≤ m ∧ m < (y + 1) * b ^ L := by
  rw [commaMsd, Nat.log_eq_of_pow_le_of_lt_pow hlo hhi,
    Nat.div_eq_iff (Nat.pow_pos (by omega : 0 < b)), Nat.succ_mul]
  have := Nat.pow_pos (n := L) (by omega : 0 < b)
  omega

/-- Two ordered candidate digits force the larger child to be a digit times a power of `b`. -/
private theorem boundary_of_candidates {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) {y z : Fin b}
    (hyz : y < z) (hy : IsCommaCandidate b n y) (hz : IsCommaCandidate b n z) :
    ∃ k : ℕ, 2 ≤ z.val ∧ n + b * (n % b) + z.val = z.val * b ^ (k + 1) := by
  let q := n + b * (n % b)
  change 0 < q + y.val ∧ commaMsd b (q + y.val) = y.val at hy
  change 0 < q + z.val ∧ commaMsd b (q + z.val) = z.val at hz
  change y.val < z.val at hyz
  have hzb := z.isLt
  have hypos : 0 < y.val := hy.2 ▸ Nat.div_pos
    (Nat.pow_log_le_self b hy.1.ne') (Nat.pow_pos (by omega))
  have hbq : b ≤ q := by
    dsimp [q]
    by_cases h : n < b
    · rw [Nat.mod_eq_of_lt h]
      have := Nat.le_mul_of_pos_right b hn
      omega
    · omega
  let L := Nat.log b (q + z.val)
  have hL : 1 ≤ L := Nat.le_log_of_pow_le hb (by simpa using (by omega : b ≤ q + z.val))
  let P := b ^ L
  have hbP : b ≤ P := Nat.le_self_pow (by omega : L ≠ 0) b
  have hhi : q + z.val < b ^ (L + 1) := Nat.lt_pow_succ_log_self hb _
  have hzlo : z.val * P ≤ q + z.val :=
    ((msd_eq_iff hb (Nat.pow_log_le_self b hz.1.ne') hhi _).mp hz.2).1
  have htwo : 2 * P ≤ z.val * P := Nat.mul_le_mul_right P (by omega)
  have hylo : P ≤ q + y.val := by omega
  have hyhi : q + y.val < (y.val + 1) * P :=
    ((msd_eq_iff (L := L) hb hylo (by omega) _).mp hy.2).2
  -- The distance between the children is exactly the difference of their leading digits.
  -- Moving one more whole place value would exceed that distance.
  have hsucc : y.val + 1 = z.val := by
    by_contra h
    have hgap : (y.val + 2) * P ≤ z.val * P := Nat.mul_le_mul_right P (by omega)
    rw [show y.val + 2 = (y.val + 1) + 1 by omega, Nat.succ_mul] at hgap
    omega
  rw [hsucc] at hyhi
  refine ⟨L - 1, by omega, ?_⟩
  rw [Nat.sub_add_cancel hL]
  change q + z.val = z.val * P
  omega

/-- The children at a change of leading digit are `c * b^(k+1) - 1` and `c * b^(k+1)`. -/
private theorem hasTwo_iff_boundary {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    HasTwo b n ↔ ∃ c k : ℕ, 2 ≤ c ∧ c < b ∧ n + b * (n % b) + c = c * b ^ (k + 1) := by
  constructor
  · rintro ⟨y, z, hne, hy, hz⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · obtain ⟨k, hc, he⟩ := boundary_of_candidates hb hn h hy hz
      exact ⟨z, k, hc, z.isLt, he⟩
    · obtain ⟨k, hc, he⟩ := boundary_of_candidates hb hn h hz hy
      exact ⟨y, k, hc, y.isLt, he⟩
  · rintro ⟨c, k, hc, hcb, he⟩
    let P := b ^ (k + 1)
    let q := n + b * (n % b)
    change q + c = c * P at he
    have hP : 0 < P := Nat.pow_pos (by omega)
    have hprev : (c - 1) * P + P = c * P := by
      rw [← Nat.succ_mul, show (c - 1).succ = c by omega]
    have hstart : P ≤ (c - 1) * P := Nat.le_mul_of_pos_left _ (by omega)
    have hend : (c + 1) * P ≤ b ^ (k + 1 + 1) := by
      rw [pow_succ' b (k + 1)]
      exact Nat.mul_le_mul_right P hcb
    have hnext : (c + 1) * P = c * P + P := Nat.succ_mul _ _
    refine ⟨⟨c - 1, by omega⟩, ⟨c, hcb⟩, fun h => ?_, ?_, ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · change 0 < q + (c - 1) ∧ commaMsd b (q + (c - 1)) = c - 1
      refine ⟨by omega, (msd_eq_iff (L := k + 1) hb (by change P ≤ _; omega) (by omega) _).2 ?_⟩
      change (c - 1) * P ≤ _ ∧ _ < (c - 1 + 1) * P
      rw [Nat.sub_add_cancel (by omega)]
      omega
    · change 0 < q + c ∧ commaMsd b (q + c) = c
      refine ⟨by omega, (msd_eq_iff (L := k + 1) hb (by change P ≤ _; omega) (by omega) _).2 ?_⟩
      change c * P ≤ _ ∧ _ < (c + 1) * P
      omega

/-- Separate the units digit and the higher digits in the larger child's equation. -/
private theorem boundary_iff_div_mod {b n c k : ℕ} (hc : 2 ≤ c) (hcb : c < b) :
    n + b * (n % b) + c = c * b ^ (k + 1) ↔
      n % b + c = b ∧ n / b + n % b + 1 = c * b ^ k := by
  have hdecomp := Nat.mod_add_div n b
  have hmod := Nat.mod_lt n (by omega : 0 < b)
  have he : n + b * (n % b) + c = (n % b + c) + b * (n / b + n % b) := by
    rw [Nat.mul_add]
    omega
  rw [he, pow_succ, ← Nat.mul_assoc, Nat.mul_comm (c * b ^ k) b]
  constructor
  · intro h
    have hm := congrArg (· % b) h
    simp only [Nat.add_mul_mod_self_left, Nat.mul_mod_right] at hm
    have hx : n % b + c = b := Nat.eq_of_dvd_of_lt_two_mul (by omega)
      (Nat.dvd_of_mod_eq_zero hm) (by omega)
    rw [hx, Nat.add_comm b, ← Nat.mul_add_one] at h
    exact ⟨hx, Nat.mul_left_cancel (by omega) h⟩
  · rintro ⟨hx, hq⟩
    rw [hx, Nat.add_comm b, ← Nat.mul_add_one, hq]

private theorem hasTwo_iff_div_mod {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    HasTwo b n ↔ ∃ c k : ℕ, 2 ≤ c ∧ c < b ∧
      n % b + c = b ∧ n / b + n % b + 1 = c * b ^ k := by
  rw [hasTwo_iff_boundary hb hn]
  exact exists_congr fun c => exists_congr fun k => and_congr_right fun hc =>
    and_congr_right fun hcb => boundary_iff_div_mod hc hcb

/-- Adding one carries through every trailing digit `b - 1`. -/
private theorem replicate_value {b : ℕ} (hb : 2 ≤ b) (d i : ℕ) :
    Nat.ofDigits b (List.replicate i (b - 1) ++ [d]) + 1 = (d + 1) * b ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons, pow_succ, ← Nat.mul_assoc, ← ih,
      Nat.add_mul, Nat.one_mul, Nat.mul_comm _ b]
    omega

/-- Evaluate the proposed string of digits, splitting off its units digit. -/
private theorem digits_pattern_iff {b n d : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d) (hdb : d ≤ b - 2)
    (i : ℕ) :
    Nat.digits b n = [b - 1 - d, d] ++ List.replicate i (b - 1) ++ [d] ↔
      n % b + (d + 1) = b ∧ n / b + n % b + 1 = (d + 1) * b ^ (i + 1) := by
  let x := b - 1 - d
  let A := Nat.ofDigits b (List.replicate i (b - 1) ++ [d])
  have hx : x + (d + 1) = b := by dsimp [x]; omega
  have hxlt : x < b := by omega
  have hval : (d + 1) * b ^ (i + 1) = b * A + b := by
    rw [pow_succ, ← Nat.mul_assoc, ← replicate_value hb d i, Nat.add_mul, Nat.one_mul,
      Nat.mul_comm _ b]
  have hdigits := Nat.digits_ofDigits b hb ([x, d] ++ List.replicate i (b - 1) ++ [d])
    (by
      intro a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_replicate] at ha
      omega)
    (by intro h; rw [List.getLast_concat]; omega)
  change Nat.digits b (x + b * (d + b * A)) = _ at hdigits
  constructor
  · intro h
    have he := congrArg (Nat.ofDigits b) h
    rw [Nat.ofDigits_digits] at he
    change n = x + b * (d + b * A) at he
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxlt, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt hxlt, hval]
    omega
  · rintro ⟨hm, hq⟩
    rw [hval] at hq
    have hx' : n % b = x := by omega
    have hq' : n / b = d + b * A := by omega
    have he := Nat.mod_add_div n b
    rw [hx', hq'] at he
    exact he ▸ hdigits

end two_commaChildren_iff

open two_commaChildren_iff in
/-- **Numbers with two comma-children.** Fix a base $b \ge 2$, and say that $n$ has at least two
comma-children if there are distinct digits $y_1 \ne y_2$ below $b$ that are both comma
candidates for $n$ in base $b$ (distinct candidates $y$ give distinct children
$n + b\,(n \bmod b) + y$). Then a positive integer $n < b^2$ has at least two comma-children if
and only if $n = (b - 1 - 2x)\, b + x$ for some $x$ with $1 \le x$ and $2x \le b - 1$; and an
integer $n \ge b^2$ has at least two comma-children if and only if its base-$b$ representation,
most significant digit first, is $d\,(b-1) \cdots (b-1)\, d\,(b-1-d)$ with some number $i \ge 0$
of middle digits $b - 1$ and $1 \le d \le b - 2$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.2 (`fq-2024-sloane05302024-thm-5.2`). -/
public theorem two_commaChildren_iff (b : ℕ) (hb : 2 ≤ b) :
    (∀ n : ℕ, 0 < n → n < b ^ 2 →
      ((∃ y₁ y₂ : Fin b, y₁ ≠ y₂ ∧ IsCommaCandidate b n y₁ ∧ IsCommaCandidate b n y₂) ↔
        ∃ x : ℕ, 1 ≤ x ∧ 2 * x ≤ b - 1 ∧ n = (b - 1 - 2 * x) * b + x)) ∧
    ∀ n : ℕ, b ^ 2 ≤ n →
      ((∃ y₁ y₂ : Fin b, y₁ ≠ y₂ ∧ IsCommaCandidate b n y₁ ∧ IsCommaCandidate b n y₂) ↔
        ∃ d i : ℕ, 1 ≤ d ∧ d ≤ b - 2 ∧
          Nat.digits b n = [b - 1 - d, d] ++ List.replicate i (b - 1) ++ [d]) := by
  constructor
  · intro n hn hsmall
    have hq : n / b < b := (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [sq] using hsmall)
    have hx := Nat.mod_lt n (by omega : 0 < b)
    change HasTwo b n ↔ _
    rw [hasTwo_iff_div_mod hb hn]
    constructor
    · rintro ⟨c, k, hc, hcb, hsum, he⟩
      have hk : k = 0 := by
        by_contra h
        have hbig : 2 * b ≤ c * b ^ k := Nat.mul_le_mul hc (Nat.le_self_pow h b)
        omega
      simp only [hk, pow_zero, Nat.mul_one] at he
      have hd : n / b + 2 * (n % b) + 1 = b := by omega
      have hplace : b - 1 = n / b + 2 * (n % b) := Nat.sub_eq_of_eq_add hd.symm
      refine ⟨n % b, by omega, hplace ▸ Nat.le_add_left _ _, ?_⟩
      rw [hplace, Nat.add_sub_cancel, Nat.mul_comm]
      exact (Nat.div_add_mod n b).symm
    · rintro ⟨x, hxpos, hbound, rfl⟩
      have hxlt : x < b := by omega
      rw [Nat.mul_comm _ b, Nat.add_comm (b * _), Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hxlt, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hxlt]
      exact ⟨b - x, 0, by omega, by omega, by omega, by simp; omega⟩
  · intro n hlarge
    have hq : b ≤ n / b := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [sq] using hlarge)
    change HasTwo b n ↔ _
    rw [hasTwo_iff_div_mod hb ((Nat.pow_pos (by omega : 0 < b)).trans_le hlarge)]
    constructor
    · rintro ⟨c, k, hc, hcb, hsum, he⟩
      cases k with
      | zero => simp only [pow_zero, Nat.mul_one] at he; omega
      | succ i =>
        refine ⟨c - 1, i, by omega, by omega, (digits_pattern_iff hb (by omega) (by omega) i).2 ?_⟩
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ c)] using And.intro hsum he
    · rintro ⟨d, i, hd, hdb, hdigits⟩
      exact ⟨d + 1, i + 1, by omega, by omega, (digits_pattern_iff hb hd hdb i).1 hdigits⟩

end MetaMathlibExt
