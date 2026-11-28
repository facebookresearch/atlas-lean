/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import MathlibExt.NumberTheory.Digits.SzuszVolkmannCounterexample
public import MathlibExt.NumberTheory.NormalNumber

/-! # Sums of `h₁` and the jumps of `h₂` at powers of ten

For every `ℓ ≥ 1`, the sum of Campbell's auxiliary sequence `h₁` over `1, …, 10 ^ (ℓ + 1) - 1`
equals `∑ j ∈ Finset.range ℓ, 900 * 100 ^ j`. Moreover, writing `y₁(n) = h₂ (10 ^ (n - 1))`
and `y₂(n) = h₂ (10 ^ n - 1)` with `h₂` Campbell's sequence, for every `ℓ ≥ 2` the slope
`(y₂(ℓ) - y₁(ℓ)) / (9 * 10 ^ (ℓ - 1) - 1)` equals `10 ^ (ℓ - 1)` and the jump
`y₁(ℓ + 1) - y₂(ℓ)` equals `10 ^ (2 * (ℓ / 2))`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 2
(`jis-2026-26.3.4-lem-2`).
-/

namespace MetaMathlibExt

@[expose] public section

namespace campbellH1_sum_and_y_relations

-- `h₁` is constant on each decimal block past the first.
private theorem h1_of_mem_block {k i : ℕ} (hk : 1 ≤ k) (hlo : 10 ^ k ≤ i)
    (hhi : i < 10 ^ (k + 1)) : campbellH1 i = 10 ^ k := by
  have hilog : Nat.log 10 i = k := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  have h10 : (10 : ℕ) ≤ 10 ^ k := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 10) hk
    simpa using h
  have hi10 : ¬ i < 10 := by omega
  simp [campbellH1, hilog, hi10]

-- Sums of `h₁` over an interval inside one decimal block.
private theorem sum_h1_Icc {k a b : ℕ} (hk : 1 ≤ k) (ha : 10 ^ k ≤ a)
    (hb : b < 10 ^ (k + 1)) :
    ∑ i ∈ Finset.Icc a b, campbellH1 i = (b + 1 - a) * 10 ^ k := by
  by_cases hab : a ≤ b
  · rw [Finset.sum_const_nat (m := 10 ^ k) (fun i hi => h1_of_mem_block hk
      (ha.trans (Finset.mem_Icc.mp hi).1) ((Finset.mem_Icc.mp hi).2.trans_lt hb))]
    rw [Nat.card_Icc]
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hab
    rw [hempty, Finset.sum_empty]
    have hzero : b + 1 - a = 0 := by omega
    rw [hzero, zero_mul]

-- Splitting a sum over `Icc` at an interior point.
private theorem sum_Icc_split (f : ℕ → ℕ) (a b c : ℕ) (hab : a ≤ b + 1)
    (hbc : b ≤ c) :
    (∑ i ∈ Finset.Icc a b, f i) + (∑ i ∈ Finset.Icc (b + 1) c, f i) =
      ∑ i ∈ Finset.Icc a c, f i := by
  rw [← Finset.Ico_add_one_right_eq_Icc a b, ← Finset.Ico_add_one_right_eq_Icc (b + 1) c,
    ← Finset.Ico_add_one_right_eq_Icc a c]
  exact Finset.sum_Ico_consecutive f hab (by omega)

-- `h₁` vanishes below `10`.
private theorem sum_h1_Icc_one_nine : ∑ i ∈ Finset.Icc 1 9, campbellH1 i = 0 := by
  rw [Finset.sum_const_nat (m := 0) (fun i hi => by
    have hle : i ≤ 9 := (Finset.mem_Icc.mp hi).2
    have hi10 : i < 10 := by omega
    simp [campbellH1, hi10])]
  simp

-- Adding one more decimal block to the sum of `h₁`.
private theorem sum_h1_step (m : ℕ)
    (ih : ∑ i ∈ Finset.Icc 1 (10 ^ (m + 1) - 1), campbellH1 i =
      ∑ j ∈ Finset.range m, 900 * 100 ^ j) :
    ∑ i ∈ Finset.Icc 1 (10 ^ (m + 1 + 1) - 1), campbellH1 i =
      ∑ j ∈ Finset.range (m + 1), 900 * 100 ^ j := by
  have e : (10 : ℕ) ^ (m + 1 + 1) = 10 * 10 ^ (m + 1) := pow_succ' _ _
  have hpos : 0 < (10 : ℕ) ^ (m + 1) := pow_pos (by norm_num : (0 : ℕ) < 10) _
  have hsplit := sum_Icc_split campbellH1 1 (10 ^ (m + 1) - 1) (10 ^ (m + 1 + 1) - 1)
    (by omega) (by omega)
  have h10 : (10 : ℕ) ^ (m + 1) - 1 + 1 = 10 ^ (m + 1) := by omega
  rw [h10] at hsplit
  have hB := sum_h1_Icc (k := m + 1) (a := 10 ^ (m + 1)) (b := 10 ^ (m + 1 + 1) - 1)
    (by omega) le_rfl (by omega)
  have hcard : (10 ^ (m + 1 + 1) - 1) + 1 - 10 ^ (m + 1) = 9 * 10 ^ (m + 1) := by
    omega
  have hmul : 9 * 10 ^ (m + 1) * 10 ^ (m + 1) = 900 * 100 ^ m := by
    have e1 : (10 : ℕ) ^ (m + 1) = 10 * 10 ^ m := pow_succ' _ _
    have h100 : (100 : ℕ) = 10 * 10 := by norm_num
    have e2 : (100 : ℕ) ^ m = 10 ^ m * 10 ^ m := by
      rw [h100, mul_pow]
    rw [e1, e2]
    ring
  rw [hcard, hmul] at hB
  rw [Finset.sum_range_succ, ← hsplit, ih, hB]

-- Sums of `h₁` over initial segments ending before a power of ten.
private theorem sum_h1 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∑ i ∈ Finset.Icc 1 (10 ^ (ℓ + 1) - 1), campbellH1 i =
      ∑ j ∈ Finset.range ℓ, 900 * 100 ^ j := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  clear hℓ
  induction n with
  | zero =>
    have h99 : (10 : ℕ) ^ (0 + 1 + 1) - 1 = 99 := by norm_num
    rw [h99, Finset.sum_range_succ, Finset.sum_range_zero]
    have hD := sum_h1_Icc_one_nine
    have hsplit := sum_Icc_split campbellH1 1 9 99 (by norm_num) (by norm_num)
    have h9 : (9 : ℕ) + 1 = 10 := rfl
    rw [h9] at hsplit
    have hB := sum_h1_Icc (k := 1) (a := 10) (b := 99) (by norm_num) (by norm_num)
      (by norm_num)
    have hnum : (99 + 1 - 10) * 10 ^ 1 = 900 := by norm_num
    have hpow : (100 : ℕ) ^ 0 = 1 := pow_zero _
    omega
  | succ n ih => exact sum_h1_step (n + 1) ih

-- `h₂` at a power of ten is a rounded-down block sum.
private theorem h2_at_pow (k : ℕ) :
    campbellH2 (10 ^ k) = 10 ^ k * ((∑ i ∈ Finset.Icc 1 (10 ^ k), campbellH1 i) / 10 ^ k) := by
  have hlog : Nat.log 10 (10 ^ k) = k := Nat.log_pow (by norm_num) k
  have hempty : Finset.Icc (10 ^ k + 1) (10 ^ k) = ∅ :=
    Finset.Icc_eq_empty (by omega)
  simp only [campbellH2, hlog, hempty, Finset.sum_empty, add_zero]

-- `h₂` just before a power of ten.
private theorem h2_at_pred_pow (k : ℕ) (hk : 1 ≤ k) :
    campbellH2 (10 ^ (k + 1) - 1) =
      10 ^ k * ((∑ i ∈ Finset.Icc 1 (10 ^ k), campbellH1 i) / 10 ^ k) +
        (9 * 10 ^ k - 1) * 10 ^ k := by
  have e : (10 : ℕ) ^ (k + 1) = 10 * 10 ^ k := pow_succ' _ _
  have hpos : 0 < (10 : ℕ) ^ k := pow_pos (by norm_num : (0 : ℕ) < 10) _
  have hlog : Nat.log 10 (10 ^ (k + 1) - 1) = k :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have htail := sum_h1_Icc (k := k) (a := 10 ^ k + 1) (b := 10 ^ (k + 1) - 1)
    hk (by omega) (by omega)
  have hcard : (10 ^ (k + 1) - 1) + 1 - (10 ^ k + 1) = 9 * 10 ^ k - 1 := by omega
  rw [hcard] at htail
  simp [campbellH2, hlog, htail]

-- `h₂` just before `10 ^ ℓ`, with the predecessor exponent.
private theorem h2_at_pred (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    campbellH2 (10 ^ ℓ - 1) =
      10 ^ (ℓ - 1) * ((∑ i ∈ Finset.Icc 1 (10 ^ (ℓ - 1)), campbellH1 i) / 10 ^ (ℓ - 1)) +
        (9 * 10 ^ (ℓ - 1) - 1) * 10 ^ (ℓ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact h2_at_pred_pow k (by omega)

-- The block sum grows by one full block plus the new endpoint.
private theorem sum_block_step (k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ Finset.Icc 1 (10 ^ (k + 1)), campbellH1 i) =
      (∑ i ∈ Finset.Icc 1 (10 ^ k), campbellH1 i) + (9 * 10 ^ k - 1) * 10 ^ k +
        10 ^ (k + 1) := by
  have e : (10 : ℕ) ^ (k + 1) = 10 * 10 ^ k := pow_succ' _ _
  have hpos : 0 < (10 : ℕ) ^ k := pow_pos (by norm_num : (0 : ℕ) < 10) _
  have hsplit := sum_Icc_split campbellH1 1 (10 ^ k) (10 ^ (k + 1))
    (by omega) (by omega)
  have hsplit2 := sum_Icc_split campbellH1 (10 ^ k + 1) (10 ^ (k + 1) - 1)
    (10 ^ (k + 1)) (by omega) (by omega)
  have h10 : (10 : ℕ) ^ (k + 1) - 1 + 1 = 10 ^ (k + 1) := by omega
  rw [h10] at hsplit2
  have htail := sum_h1_Icc (k := k) (a := 10 ^ k + 1) (b := 10 ^ (k + 1) - 1)
    hk (by omega) (by omega)
  have hcard : (10 ^ (k + 1) - 1) + 1 - (10 ^ k + 1) = 9 * 10 ^ k - 1 := by omega
  rw [hcard] at htail
  have htop : ∑ i ∈ Finset.Icc (10 ^ (k + 1)) (10 ^ (k + 1)), campbellH1 i =
      10 ^ (k + 1) := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    have e2 : (10 : ℕ) ^ (k + 1 + 1) = 10 * 10 ^ (k + 1) := pow_succ' _ _
    exact h1_of_mem_block (by omega) le_rfl (by omega)
  omega

-- The sum over `1, …, 10 ^ m - 1` is the geometric partial sum.
private theorem sum_pred_eq (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ Finset.Icc 1 (10 ^ m - 1), campbellH1 i) =
      ∑ j ∈ Finset.range (m - 1), 900 * 100 ^ j := by
  rcases eq_or_ne m 1 with rfl | hm1
  · have e1 : (10 : ℕ) ^ 1 - 1 = 9 := by norm_num
    have e2 : (1 : ℕ) - 1 = 0 := by norm_num
    rw [e1, e2, sum_h1_Icc_one_nine, Finset.sum_range_zero]
  · obtain ⟨k, rfl, hk⟩ : ∃ k, m = k + 1 ∧ 1 ≤ k := ⟨m - 1, by omega, by omega⟩
    rw [Nat.add_sub_cancel]
    exact sum_h1 k hk

-- The block sum through `10 ^ m` splits off the endpoint.
private theorem block_sum_eq (m : ℕ) (hm : 1 ≤ m) :
    (∑ i ∈ Finset.Icc 1 (10 ^ m), campbellH1 i) =
      (∑ j ∈ Finset.range (m - 1), 900 * 100 ^ j) + 10 ^ m := by
  have hpos : 0 < (10 : ℕ) ^ m := pow_pos (by norm_num : (0 : ℕ) < 10) _
  have hsplit := sum_Icc_split campbellH1 1 (10 ^ m - 1) (10 ^ m) (by omega) (by omega)
  have h10 : (10 : ℕ) ^ m - 1 + 1 = 10 ^ m := by omega
  rw [h10] at hsplit
  have htop : ∑ i ∈ Finset.Icc (10 ^ m) (10 ^ m), campbellH1 i = 10 ^ m := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    have e2 : (10 : ℕ) ^ (m + 1) = 10 * 10 ^ m := pow_succ' _ _
    exact h1_of_mem_block hm le_rfl (by omega)
  rw [← hsplit, htop, sum_pred_eq m hm]

-- The geometric partial sums stay below the next power of `100`.
private theorem geom_bound (t : ℕ) :
    (∑ j ∈ Finset.range t, 900 * 100 ^ j) < 100 ^ (t + 1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hX : 0 < (100 : ℕ) ^ t := pow_pos (by norm_num : (0 : ℕ) < 100) _
    have e1 : (100 : ℕ) ^ (t + 1) = 100 * 100 ^ t := pow_succ' _ _
    have e2 : (100 : ℕ) ^ (t + 1 + 1) = 100 * 100 ^ (t + 1) := pow_succ' _ _
    omega

-- The geometric partial sums stay below ten times the current power of `100`.
private theorem geom_bound10 (t : ℕ) :
    (∑ j ∈ Finset.range t, 900 * 100 ^ j) < 10 * 100 ^ t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hX : 0 < (100 : ℕ) ^ t := pow_pos (by norm_num : (0 : ℕ) < 100) _
    have e1 : (100 : ℕ) ^ (t + 1) = 100 * 100 ^ t := pow_succ' _ _
    omega

-- High terms of the geometric sum vanish modulo a power of `100`.
private theorem geom_mod_pow (s m : ℕ) (hs : 1 ≤ s) (hm : s - 1 ≤ m) :
    (∑ j ∈ Finset.range m, 900 * 100 ^ j) % 100 ^ s =
      ∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => 900 * 100 ^ j) hm
  have hdvd : 100 ^ s ∣ ∑ j ∈ Finset.Ico (s - 1) m, 900 * 100 ^ j := by
    apply Finset.dvd_sum
    intro j hj
    have hjs : s - 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hle : s ≤ j + 1 := by omega
    have h100 : (100 : ℕ) ^ s ∣ 100 ^ (j + 1) := pow_dvd_pow _ hle
    have heq : 900 * 100 ^ j = 9 * 100 ^ (j + 1) := by
      rw [pow_succ']
      ring
    rw [heq]
    exact h100.trans (dvd_mul_left _ _)
  obtain ⟨t, ht⟩ := hdvd
  have hbound : (∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j) < 100 ^ s := by
    have hb := geom_bound (s - 1)
    have hs1 : s - 1 + 1 = s := by omega
    rw [hs1] at hb
    exact hb
  have hmod : (∑ j ∈ Finset.range m, 900 * 100 ^ j) =
      (∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j) + 100 ^ s * t := by
    rw [← hsplit, ht]
  rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

-- High terms of the geometric sum vanish modulo ten times a power of `100`.
private theorem geom_mod10_pow (s m : ℕ) (hm : s ≤ m) :
    (∑ j ∈ Finset.range m, 900 * 100 ^ j) % (10 * 100 ^ s) =
      ∑ j ∈ Finset.range s, 900 * 100 ^ j := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => 900 * 100 ^ j) hm
  have hdvd : 10 * 100 ^ s ∣ ∑ j ∈ Finset.Ico s m, 900 * 100 ^ j := by
    apply Finset.dvd_sum
    intro j hj
    have hjs : s ≤ j := (Finset.mem_Ico.mp hj).1
    have hexp : j + 1 = (s + 1) + (j - s) := by omega
    have h100 : (100 : ℕ) ^ (j + 1) = 100 ^ (s + 1) * 100 ^ (j - s) := by
      rw [← pow_add, hexp]
    refine ⟨90 * 100 ^ (j - s), ?_⟩
    calc 900 * 100 ^ j = 9 * 100 ^ (j + 1) := by
            rw [pow_succ']
            ring
      _ = 9 * (100 ^ (s + 1) * 100 ^ (j - s)) := by rw [h100]
      _ = (10 * 100 ^ s) * (90 * 100 ^ (j - s)) := by
            rw [pow_succ']
            ring
  obtain ⟨t, ht⟩ := hdvd
  have hbound := geom_bound10 s
  have hmod : (∑ j ∈ Finset.range m, 900 * 100 ^ j) =
      (∑ j ∈ Finset.range s, 900 * 100 ^ j) + (10 * 100 ^ s) * t := by
    rw [← hsplit, ht]
  rw [hmod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

-- The jump of `h₂` at `10 ^ ℓ` in terms of `ℓ / 2`.
private theorem h2_jump (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    campbellH2 (10 ^ ℓ) = campbellH2 (10 ^ ℓ - 1) + 10 ^ (2 * (ℓ / 2)) := by
  rcases Nat.even_or_odd ℓ with he | ho
  · obtain ⟨s, rfl⟩ := he
    have hs : 1 ≤ s := by omega
    have hdiv : (s + s) / 2 = s := by omega
    rw [hdiv]
    have hF := h2_at_pow (s + s)
    have hG := h2_at_pred (s + s) (by omega)
    have hJ1 := block_sum_eq (s + s) (by omega)
    have hJ0 := block_sum_eq (s + s - 1) (by omega)
    have hH := sum_block_step (s + s - 1) (by omega)
    have hexpH : s + s - 1 + 1 = s + s := by omega
    rw [hexpH] at hH
    have hss : s + s = 2 * s := by omega
    have h102 : (10 : ℕ) ^ 2 = 100 := by norm_num
    have e100 : (10 : ℕ) ^ (s + s) = 100 ^ s := by
      rw [hss, pow_mul, h102]
    have hexp10 : s + s - 1 = 2 * (s - 1) + 1 := by omega
    have e10 : (10 : ℕ) ^ (s + s - 1) = 10 * 100 ^ (s - 1) := by
      rw [hexp10, pow_succ', pow_mul, h102]
    have hR1 : (∑ i ∈ Finset.Icc 1 (10 ^ (s + s)), campbellH1 i) % 10 ^ (s + s) =
        ∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j := by
      rw [hJ1, Nat.add_mod_right, e100]
      exact geom_mod_pow s (s + s - 1) hs (by omega)
    have hR0 : (∑ i ∈ Finset.Icc 1 (10 ^ (s + s - 1)), campbellH1 i) %
          10 ^ (s + s - 1) =
        ∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j := by
      rw [hJ0, Nat.add_mod_right, e10]
      exact geom_mod10_pow (s - 1) (s + s - 1 - 1) (by omega)
    have hD1 := Nat.div_add_mod (∑ i ∈ Finset.Icc 1 (10 ^ (s + s)), campbellH1 i)
      (10 ^ (s + s))
    have hD0 := Nat.div_add_mod (∑ i ∈ Finset.Icc 1 (10 ^ (s + s - 1)), campbellH1 i)
      (10 ^ (s + s - 1))
    rw [hR1] at hD1
    rw [hR0] at hD0
    have h10e : (10 : ℕ) ^ (2 * s) = 10 ^ (s + s) := by rw [hss]
    rw [hF, hG, h10e]
    omega
  · obtain ⟨s, rfl⟩ := ho
    have hs : 1 ≤ s := by omega
    have hdiv : (2 * s + 1) / 2 = s := by omega
    rw [hdiv]
    have hF := h2_at_pow (2 * s + 1)
    have hG := h2_at_pred (2 * s + 1) (by omega)
    have hJ1 := block_sum_eq (2 * s + 1) (by omega)
    have hJ0 := block_sum_eq (2 * s + 1 - 1) (by omega)
    have hH := sum_block_step (2 * s + 1 - 1) (by omega)
    have hexpH : 2 * s + 1 - 1 + 1 = 2 * s + 1 := by omega
    rw [hexpH] at hH
    have h102 : (10 : ℕ) ^ 2 = 100 := by norm_num
    have eP : (10 : ℕ) ^ (2 * s + 1) = 10 * 100 ^ s := by
      rw [pow_succ', pow_mul, h102]
    have hexp0 : 2 * s + 1 - 1 = 2 * s := by omega
    have ep : (10 : ℕ) ^ (2 * s + 1 - 1) = 100 ^ s := by
      rw [hexp0, pow_mul, h102]
    have h10o : (10 : ℕ) ^ (2 * s) = 100 ^ s := by
      rw [pow_mul, h102]
    have hR1 : (∑ i ∈ Finset.Icc 1 (10 ^ (2 * s + 1)), campbellH1 i) %
          10 ^ (2 * s + 1) =
        ∑ j ∈ Finset.range s, 900 * 100 ^ j := by
      rw [hJ1, Nat.add_mod_right, eP]
      exact geom_mod10_pow s (2 * s + 1 - 1) (by omega)
    have hR0 : (∑ i ∈ Finset.Icc 1 (10 ^ (2 * s + 1 - 1)), campbellH1 i) %
          10 ^ (2 * s + 1 - 1) =
        ∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j := by
      rw [hJ0, Nat.add_mod_right, ep]
      exact geom_mod_pow s (2 * s + 1 - 1 - 1) hs (by omega)
    have hs1 : s - 1 + 1 = s := by omega
    have hGs : (∑ j ∈ Finset.range s, 900 * 100 ^ j) =
        (∑ j ∈ Finset.range (s - 1), 900 * 100 ^ j) + 900 * 100 ^ (s - 1) := by
      conv_lhs => rw [← hs1]
      rw [Finset.sum_range_succ]
    have hps : (100 : ℕ) ^ s = 100 * 100 ^ (s - 1) := by
      conv_lhs => rw [← hs1]
      rw [pow_succ']
    have hD1 := Nat.div_add_mod (∑ i ∈ Finset.Icc 1 (10 ^ (2 * s + 1)), campbellH1 i)
      (10 ^ (2 * s + 1))
    have hD0 := Nat.div_add_mod (∑ i ∈ Finset.Icc 1 (10 ^ (2 * s + 1 - 1)), campbellH1 i)
      (10 ^ (2 * s + 1 - 1))
    rw [hR1] at hD1
    rw [hR0] at hD0
    rw [hF, hG, h10o]
    omega

-- The slope of `h₂` across a decimal block.
private theorem slope_eq (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ((campbellH2 (10 ^ ℓ - 1) : ℚ) - campbellH2 (10 ^ (ℓ - 1))) / (9 * 10 ^ (ℓ - 1) - 1) =
      10 ^ (ℓ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hk : 1 ≤ k := by omega
  have h2e := h2_at_pred_pow k hk
  have h1e := h2_at_pow k
  have hnat : campbellH2 (10 ^ (k + 1) - 1) =
      campbellH2 (10 ^ k) + (9 * 10 ^ k - 1) * 10 ^ k := by rw [h2e, h1e]
  have hD0 : (1 : ℕ) ≤ 9 * 10 ^ k := by
    have hpos : 0 < (10 : ℕ) ^ k := pow_pos (by norm_num : (0 : ℕ) < 10) _
    omega
  have hDne : ((9 * 10 ^ k - 1 : ℕ) : ℚ) ≠ 0 := by
    have hpos : 0 < 9 * 10 ^ k - 1 := by omega
    exact_mod_cast ne_of_gt hpos
  have hDcast : ((9 * 10 ^ k - 1 : ℕ) : ℚ) = 9 * 10 ^ k - 1 := by
    simp [Nat.cast_sub hD0]
  have hDne' : (9 : ℚ) * 10 ^ k - 1 ≠ 0 := by
    rw [← hDcast]
    exact hDne
  have hcast : ((campbellH2 (10 ^ (k + 1) - 1)) : ℚ) =
      ((campbellH2 (10 ^ k)) : ℚ) + ((9 * 10 ^ k - 1 : ℕ) : ℚ) * ((10 ^ k : ℕ) : ℚ) := by
    exact_mod_cast hnat
  rw [div_eq_iff hDne', hcast, hDcast]
  push_cast
  ring

-- The jump of `h₂` at `10 ^ ℓ`, as integers.
private theorem jump_eq (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (campbellH2 (10 ^ ℓ) : ℤ) - campbellH2 (10 ^ ℓ - 1) = 10 ^ (2 * (ℓ / 2)) := by
  have h := h2_jump ℓ hℓ
  have hcast : ((10 ^ (2 * (ℓ / 2)) : ℕ) : ℤ) = 10 ^ (2 * (ℓ / 2)) := by norm_cast
  omega

end campbellH1_sum_and_y_relations

/-- **Sums of $h_1$ and the jumps of $h_2$ at powers of ten.** Let $h_1$ be Campbell's auxiliary
sequence and $h_2$ Campbell's sequence. For every integer $\ell \ge 1$,
$\sum_{i=1}^{10^{\ell+1}-1} h_1(i) = \sum_{j=0}^{\ell-1} 900 \cdot 100^j$, the number written
$9090\cdots900$ ($\ell$ blocks $90$, then $0$). Moreover, writing $y_1(n) = h_2(10^{n-1})$ and
$y_2(n) = h_2(10^n - 1)$, for every integer $\ell \ge 2$ we have
$(y_2(\ell) - y_1(\ell)) / (9 \cdot 10^{\ell-1} - 1) = 10^{\ell-1}$ and
$y_1(\ell + 1) - y_2(\ell) = 10^{2\lfloor \ell/2 \rfloor}$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 2
(`jis-2026-26.3.4-lem-2`). -/
theorem campbellH1_sum_and_y_relations :
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ i ∈ Finset.Icc 1 (10 ^ (ℓ + 1) - 1), campbellH1 i = ∑ j ∈ Finset.range ℓ, 900 * 100 ^ j) ∧
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      ((campbellH2 (10 ^ ℓ - 1) : ℚ) - campbellH2 (10 ^ (ℓ - 1))) / (9 * 10 ^ (ℓ - 1) - 1) =
          10 ^ (ℓ - 1) ∧
        (campbellH2 (10 ^ ℓ) : ℤ) - campbellH2 (10 ^ ℓ - 1) = 10 ^ (2 * (ℓ / 2)) := by
  exact ⟨fun ℓ hℓ => campbellH1_sum_and_y_relations.sum_h1 ℓ hℓ, fun ℓ hℓ =>
    ⟨campbellH1_sum_and_y_relations.slope_eq ℓ hℓ,
      campbellH1_sum_and_y_relations.jump_eq ℓ hℓ⟩⟩

end

end MetaMathlibExt
