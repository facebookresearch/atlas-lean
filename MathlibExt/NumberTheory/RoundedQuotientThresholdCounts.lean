/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Threshold counts for rounded quotients

We count the denominators in `Finset.Icc 1 n` for which `n / d` rounded to the
nearest integer, with halves rounded up, reaches a given positive threshold.
-/

namespace MetaMathlibExt

/-- **Counting large terms of the rounded quotient sequence.** Let $n$ be a natural number.
Every $d$ with $1 \le d \le n$ satisfies $\lfloor n/d + 1/2 \rfloor \ge 1$, and for every
integer $k \ge 2$ the number of $d$ with $1 \le d \le n$ and $\lfloor n/d + 1/2 \rfloor \ge k$
is $\lfloor 2n/(2k-1) \rfloor$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 13 (`jis-2024-24.2.5-lem-13`). -/
public theorem round_div_sequence_card_ge (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun d : ℕ => (1 : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋)).card
        = n ∧
      ∀ k : ℕ, 2 ≤ k →
        ((Finset.Icc 1 n).filter
            (fun d : ℕ => (k : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋)).card =
          2 * n / (2 * k - 1) := by
  constructor
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro d hd
      obtain ⟨hd₁, hdn⟩ := Finset.mem_Icc.mp hd
      have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
      have hdnq : (d : ℚ) ≤ n := by exact_mod_cast hdn
      have hdiv : (1 : ℚ) ≤ (n : ℚ) / d :=
        (le_div_iff₀ hdq).mpr (by simpa only [one_mul] using hdnq)
      rw [Int.le_floor, Int.cast_one]
      linarith only [hdiv]
  · intro k hk
    have htwo : 2 ≤ 2 * k - 1 := by omega
    have hpos : 0 < 2 * k - 1 := by omega
    have hsub : 1 ≤ 2 * k := by omega
    have hbound : 2 * n / (2 * k - 1) ≤ n :=
      Nat.div_le_of_le_mul (Nat.mul_le_mul_right n htwo)
    -- Clearing the positive denominator preserves equality at a half-integer.
    have hthreshold (d : ℕ) (hd : 1 ≤ d) :
        (k : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋ ↔ d ≤ 2 * n / (2 * k - 1) := by
      have hdq : (0 : ℚ) < d := by exact_mod_cast (show 0 < d by omega)
      rw [Int.le_floor, Int.cast_natCast, ← sub_le_iff_le_add, le_div_iff₀ hdq,
        Nat.le_div_iff_mul_le hpos]
      rw [← Nat.cast_le (α := ℚ) (m := d * (2 * k - 1)) (n := 2 * n)]
      push_cast [Nat.cast_sub hsub]
      constructor <;> intro h <;> nlinarith only [h]
    have hfilter :
        (Finset.Icc 1 n).filter (fun d : ℕ => (k : ℤ) ≤ ⌊(n : ℚ) / (d : ℚ) + 1 / 2⌋) =
          Finset.Icc 1 (2 * n / (2 * k - 1)) := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hd, _⟩, h⟩
        exact ⟨hd, (hthreshold d hd).mp h⟩
      · rintro ⟨hd, h⟩
        exact ⟨⟨hd, h.trans hbound⟩, (hthreshold d hd).mpr h⟩
    rw [hfilter]
    simp

end MetaMathlibExt
