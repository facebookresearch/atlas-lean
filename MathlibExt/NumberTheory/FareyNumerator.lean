/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Farey fractions with a given numerator

The theorem `farey_between_count` counts the reduced fractions with a fixed numerator
between consecutive unit fractions and in the subinterval cut off by their mediant.
-/

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

open Finset

/-- Reflection across the midpoint pairs the two halves of a reduced residue system. -/
private theorem twice_card_upper_residues {h : ℕ} (hh : 2 < h) :
    2 * (((range h).filter h.Coprime).filter (fun r => h < 2 * r)).card = h.totient := by
  let s := (range h).filter h.Coprime
  have reflect {r : ℕ} (hr : r ∈ s) :
      h - r ∈ s ∧ (h < 2 * (h - r) ↔ ¬ h < 2 * r) := by
    obtain ⟨hlt, hc⟩ := mem_filter.mp hr
    have hrlt := mem_range.mp hlt
    have hrpos : r ≠ 0 := by
      rintro rfl
      have := (Nat.coprime_zero_right _).mp hc
      omega
    have hmid : h ≠ 2 * r := by
      rintro rfl
      have := hc.symm.eq_one_of_dvd (dvd_mul_left r 2)
      omega
    exact ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),
      (Nat.coprime_self_sub_right hrlt.le).mpr hc⟩, by omega⟩
  have paired : (s.filter (fun r => h < 2 * r)).card =
      (s.filter (fun r => ¬ h < 2 * r)).card := by
    apply card_nbij' (h - ·) (h - ·)
    · intro r hr
      obtain ⟨hr, hu⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨(reflect hr).1, fun hx => (reflect hr).2.mp hx hu⟩
    · intro r hr
      obtain ⟨hr, hl⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨(reflect hr).1, (reflect hr).2.mpr hl⟩
    all_goals
      intro r hr
      exact Nat.sub_sub_self (mem_range.mp (mem_filter.mp (mem_filter.mp hr).1).1).le
  change 2 * (s.filter (fun r => h < 2 * r)).card = s.card
  rw [two_mul]
  simpa only [← paired] using card_filter_add_card_filter_not (s := s) (fun r => h < 2 * r)

/-- **Farey fractions with equal numerators between consecutive unit fractions.** Let $k$, $n$
and $h$ be natural numbers with $k > 1$, $h \ge 1$ and $n \ge kh - 1$, and let $\varphi$ be Euler's
totient function. The number of integers $b$ with $1 \le b \le n$, $\gcd(h, b) = 1$ and
$1/k < h/b \le 1/(k-1)$ is $\varphi(h)$. If moreover $h > 2$, then twice the number of integers
$b$ with $1 \le b \le n$, $\gcd(h, b) = 1$ and $1/k < h/b < 2/(2k-1)$ is $\varphi(h)$.

Equivalently, the Farey sequence of order $n$ has exactly $\varphi(h)$ fractions with numerator
$h$ in the interval $(1/k, 1/(k-1)]$, and for $h > 2$ exactly $\varphi(h)/2$ in the interval
$(1/k, 2/(2k-1))$.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
Lemma 1. -/
public theorem farey_between_count (k n h : ℕ)
    (hk : 1 < k) (hh : 1 ≤ h) (hn : k * h - 1 ≤ n) :
    ((Finset.Icc 1 n).filter (fun b => Nat.Coprime h b ∧
        (1 : ℚ) / k < (h : ℚ) / b ∧
          (h : ℚ) / b ≤ 1 / ((k : ℚ) - 1))).card =
        Nat.totient h ∧
      (2 < h →
        2 * ((Finset.Icc 1 n).filter (fun b =>
            Nat.Coprime h b ∧ (1 : ℚ) / k < (h : ℚ) / b ∧
              (h : ℚ) / b < 2 / (2 * (k : ℚ) - 1))).card =
          Nat.totient h) := by
  let a := (k - 1) * h
  have ha : 0 < a := Nat.mul_pos (by omega) hh
  have hend : k * h = a + h := by
    dsimp [a]
    rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
  have hcast : (a : ℚ) = ((k : ℚ) - 1) * h := by
    simp [a, Nat.cast_sub (by omega : 1 ≤ k)]
  have hkq : (1 : ℚ) < k := by exact_mod_cast hk
  have lower {b : ℕ} (hb : 0 < b) :
      (1 : ℚ) / k < (h : ℚ) / b ↔ b < a + h := by
    rw [div_lt_div_iff₀ (by linarith) (by exact_mod_cast hb), one_mul, ← hend, mul_comm k]
    norm_cast
  have upper {b : ℕ} (hb : 0 < b) :
      (h : ℚ) / b ≤ 1 / ((k : ℚ) - 1) ↔ a ≤ b := by
    rw [div_le_div_iff₀ (by exact_mod_cast hb) (by linarith), one_mul, mul_comm, ← hcast]
    norm_cast
  have middle {b : ℕ} (hb : 0 < b) :
      (h : ℚ) / b < 2 / (2 * (k : ℚ) - 1) ↔ 2 * a + h < 2 * b := by
    rw [div_lt_div_iff₀ (by exact_mod_cast hb) (by linarith)]
    have heq : (h : ℚ) * (2 * k - 1) = 2 * a + h := by rw [hcast]; ring
    rw [heq]
    norm_cast
  let block := (Ico a (a + h)).filter h.Coprime
  constructor
  · have full : ((Icc 1 n).filter (fun b => h.Coprime b ∧
        (1 : ℚ) / k < (h : ℚ) / b ∧ (h : ℚ) / b ≤ 1 / ((k : ℚ) - 1))) = block := by
      ext b
      simp only [block, mem_filter, mem_Icc, mem_Ico]
      by_cases hb : 0 < b
      · rw [lower hb, upper hb]
        omega
      · omega
    rw [full]
    exact Nat.filter_coprime_Ico_eq_totient h a
  · intro hh'
    have half : ((Icc 1 n).filter (fun b => h.Coprime b ∧
        (1 : ℚ) / k < (h : ℚ) / b ∧ (h : ℚ) / b < 2 / (2 * (k : ℚ) - 1))) =
        block.filter (fun b => 2 * a + h < 2 * b) := by
      ext b
      simp only [block, mem_filter, mem_Icc, mem_Ico]
      by_cases hb : 0 < b
      · rw [lower hb, middle hb]
        omega
      · omega
    have shift : (range h).map (addLeftEmbedding a) = Ico a (a + h) := by
      rw [range_eq_Ico, map_add_left_Ico, add_zero]
    rw [half]
    simp only [block, ← shift, filter_map, card_map, Function.comp_def, addLeftEmbedding_apply]
    simpa [a, mul_add, add_assoc] using twice_card_upper_residues hh'

end MathlibExt.NumberTheory.FareyNumeratorWanted
