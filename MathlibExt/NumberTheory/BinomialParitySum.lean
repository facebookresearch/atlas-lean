/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.BitIndices

/-!
# Binomial parity sums at one less than a power of two

We evaluate the binomial parity sum for `n = 2 ^ ℓ - 1` by comparing the binary digits of the
binomial arguments using Lucas's theorem.
-/

namespace MetaMathlibExt

namespace sum_choose_two_pow_mul_mod_two_two_pow_sub_one

private theorem choose_mod_two_eq_one_iff (n k : ℕ) :
    n.choose k % 2 = 1 ↔ ∀ i, k.testBit i → n.testBit i := by
  let bound := max n k
  have hn : n < 2 ^ bound := (le_max_left n k).trans_lt Nat.lt_two_pow_self
  have hk : k < 2 ^ bound := (le_max_right n k).trans_lt Nat.lt_two_pow_self
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have digit (i : ℕ) :
      (n / 2 ^ i % 2).choose (k / 2 ^ i % 2) =
        if k.testBit i → n.testBit i then 1 else 0 := by
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with hn' | hn' <;>
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ i) with hk' | hk' <;>
      simp [hn', hk']
  have lucas := Choose.choose_modEq_prod_range_choose_nat hn hk
  change n.choose k % 2 = _ % 2 at lucas
  rw [lucas]
  simp_rw [digit]
  constructor
  · intro h i hi
    by_cases hil : i < bound
    · by_contra hn'
      have hz : (∏ j ∈ Finset.range bound, if k.testBit j → n.testBit j then 1 else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hil) (ite_eq_right (fun h' => hn' (h' hi)))
      simp [hz] at h
    · have : k < 2 ^ i := hk.trans_le (Nat.pow_le_pow_right (by decide) (le_of_not_gt hil))
      simp [Nat.testBit_lt_two_pow this] at hi
  · intro h
    rw [Finset.prod_eq_one fun i _ => ite_eq_left (h i)]
    decide

private theorem add_eq_shift_of_choose_mod_two_eq_one {m ℓ k : ℕ} (hm : 0 < m) (hℓ : 0 < ℓ)
    (hk : k < 2 ^ ℓ) (h : (2 ^ m * k).choose (2 ^ ℓ - 1 + k) % 2 = 1) :
    2 ^ ℓ - 1 + k = 2 ^ m * k := by
  have hbits := (choose_mod_two_eq_one_iff _ _).mp h
  have hshift : (2 ^ m * k).testBit 0 = false := by
    rw [mul_comm, Nat.testBit_mul_two_pow]
    simp [hm.not_ge]
  have hmask : (2 ^ ℓ - 1) % 2 = 1 := by
    apply of_decide_eq_true
    rw [← Nat.testBit_zero, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hℓ
  have hsum : ¬ (2 ^ ℓ - 1 + k).testBit 0 := by
    intro hb
    have := hbits 0 hb
    simp [hshift] at this
  have hodd : k = 2 * (k / 2) + 1 := by
    simp only [Nat.testBit_zero, decide_eq_true_eq] at hsum
    omega
  have hpos : 0 < (2 : ℕ) ^ ℓ := by positivity
  have hsmall : 2 * (k / 2) < 2 ^ ℓ := by omega
  have hsplit : 2 ^ ℓ - 1 + k = 2 ^ ℓ ||| 2 * (k / 2) := by
    calc
      2 ^ ℓ - 1 + k = 2 ^ ℓ + 2 * (k / 2) := by omega
      _ = _ := by simpa only [mul_one] using Nat.two_pow_add_eq_or_of_lt hsmall 1
  -- The bottom replaces bit zero of `k` with bit `ℓ`. The top shifts every set bit of `k`.
  have hbottom : (2 ^ ℓ - 1 + k).bitIndices.toFinset =
      insert ℓ (2 * (k / 2)).bitIndices.toFinset := by
    ext i
    simp only [hsplit, Finset.mem_insert, List.mem_toFinset, Nat.mem_bitIndices,
      Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq, eq_comm (a := i)]
  have hnew : ℓ ∉ (2 * (k / 2)).bitIndices.toFinset := by
    simp only [List.mem_toFinset, Nat.mem_bitIndices, Nat.testBit_lt_two_pow hsmall,
      Bool.false_eq_true, not_false_eq_true]
  have hcardBottom : (2 ^ ℓ - 1 + k).bitIndices.toFinset.card = k.bitIndices.length := by
    rw [hbottom, Finset.card_insert_of_notMem hnew,
      List.toFinset_card_of_nodup Nat.bitIndices_nodup]
    conv_rhs => rw [hodd]
    simp
  have hcardTop : (2 ^ m * k).bitIndices.toFinset.card = k.bitIndices.length := by
    rw [List.toFinset_card_of_nodup Nat.bitIndices_nodup, Nat.bitIndices_two_pow_mul,
      List.length_map]
  have heq := Finset.eq_of_subset_of_card_le
    (s := (2 ^ ℓ - 1 + k).bitIndices.toFinset) (t := (2 ^ m * k).bitIndices.toFinset)
    (by simpa only [Finset.subset_iff, List.mem_toFinset, Nat.mem_bitIndices] using hbits)
    (hcardTop.trans hcardBottom.symm).le
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  simpa only [List.mem_toFinset, Nat.mem_bitIndices] using Finset.ext_iff.mp heq i

end sum_choose_two_pow_mul_mod_two_two_pow_sub_one

open sum_choose_two_pow_mul_mod_two_two_pow_sub_one in
/-- **Binomial parity sums at one less than a power of two.** For all natural numbers $m$ and
$\ell$, with $n = 2^\ell - 1$, the sum
$$\sum_{k=0}^{n} \left( \binom{2^m k}{n + k} \binom{n}{k} \bmod 2 \right)$$
equals $1$ if $m$ divides $\ell$, and $0$ otherwise.

The paper takes $m \ge 2$; the statement holds for every $m$, where $0$ divides $\ell$ only
when $\ell = 0$.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 2. -/
public theorem sum_choose_two_pow_mul_mod_two_two_pow_sub_one (m ℓ : ℕ) :
    ∑ k ∈ Finset.range (2 ^ ℓ - 1 + 1), ((2 ^ m * k).choose (2 ^ ℓ - 1 + k) * (2 ^ ℓ -
        1).choose k) % 2 =
      if m ∣ ℓ then 1 else 0 := by
  by_cases hℓ : ℓ = 0
  · subst ℓ
    simp
  have hℓ' : 0 < ℓ := Nat.pos_of_ne_zero hℓ
  have hn : 0 < 2 ^ ℓ - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hℓ (by decide))
  by_cases hm : m = 0
  · subst m
    simp only [pow_zero, one_mul, Nat.zero_dvd, ite_eq_right hℓ]
    apply Finset.sum_eq_zero
    intro k _
    rw [Nat.choose_eq_zero_of_lt (by omega : k < 2 ^ ℓ - 1 + k), zero_mul, Nat.zero_mod]
  let n := (2 : ℕ) ^ ℓ - 1
  let q := (2 : ℕ) ^ m
  change (∑ k ∈ Finset.range (n + 1), ((q * k).choose (n + k) * n.choose k) % 2) = _
  have hq : 0 < q - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hm (by decide))
  have hdiv : q - 1 ∣ n ↔ m ∣ ℓ := by
    change 2 ^ m - 1 ∣ 2 ^ ℓ - 1 ↔ m ∣ ℓ
    simp only [Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one, Nat.sub_eq_zero_iff_le]
    constructor
    · intro h
      by_contra hne
      exact (Nat.one_lt_pow hne (by decide)).not_ge h
    · intro h
      simp [h]
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      ((q * k).choose (n + k) * n.choose k) % 2 = 1 ↔ (q - 1) * k = n := by
    have hk' : k < 2 ^ ℓ := by
      have hp : 1 ≤ (2 : ℕ) ^ ℓ := Nat.succ_le_of_lt (by positivity)
      simpa only [n, Nat.sub_add_cancel hp] using Finset.mem_range.mp hk
    have hchoose : n.choose k % 2 = 1 := by
      apply (choose_mod_two_eq_one_iff n k).mpr
      intro i hi
      change (2 ^ ℓ - 1).testBit i = true
      rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      by_contra! hle
      have hlt := hk'.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hle)
      simp [Nat.testBit_lt_two_pow hlt] at hi
    have hle : k ≤ q * k := Nat.le_mul_of_pos_left k (by dsimp [q]; positivity)
    rw [Nat.mul_mod, hchoose, mul_one, Nat.mod_mod, Nat.sub_mul, one_mul, Nat.sub_eq_iff_eq_add hle]
    refine ⟨fun h => (add_eq_shift_of_choose_mod_two_eq_one (Nat.pos_of_ne_zero hm) hℓ' hk' h).symm,
      fun h => ?_⟩
    rw [h, Nat.choose_self]
  by_cases h : m ∣ ℓ
  · obtain ⟨a, ha⟩ := hdiv.mpr h
    have ha' : a ∈ Finset.range (n + 1) := Finset.mem_range.mpr
      ((Nat.le_mul_of_pos_left a hq).trans_lt (ha ▸ Nat.lt_succ_self n))
    rw [ite_eq_left h, Finset.sum_eq_single_of_mem a ha']
    · exact (hterm a ha').mpr ha.symm
    · intro k hk hne
      exact (Nat.mod_two_eq_zero_or_one _).resolve_right fun h₁ =>
        hne (Nat.eq_of_mul_eq_mul_left hq ((hterm k hk).mp h₁ |>.trans ha))
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro k hk
    exact (Nat.mod_two_eq_zero_or_one _).resolve_right fun h₁ =>
      h (hdiv.mp ⟨k, ((hterm k hk).mp h₁).symm⟩)

end MetaMathlibExt
