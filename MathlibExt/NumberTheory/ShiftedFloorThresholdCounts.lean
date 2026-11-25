/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith

/-!
# Threshold counts for shifted floor quotients

We count the denominators in `Finset.Icc 1 n` for which a shifted floor quotient reaches a given
positive threshold.
-/

namespace MetaMathlibExt

-- Keep the original named hypotheses, including the bounds not needed by the proof.
set_option linter.unusedVariables false in
/-- **Tail counts of the shifted floor sequence.** Let $n$ be a natural number and let $\alpha$
and $\nu$ be real numbers with $0 \le \alpha < 1$, $0 \le \nu < 1$ and $\nu \le n\alpha$. Then
$\lfloor (n - \nu)/d + \alpha \rfloor \ge 1$ for all $n$ integers $d$ with $1 \le d \le n$, and
for every natural number $k \ge 2$ the number of integers $d$ with $1 \le d \le n$ and
$\lfloor (n - \nu)/d + \alpha \rfloor \ge k$ is $\lfloor (n - \nu)/(k - \alpha) \rfloor$.

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Lemma 24 (`jis-2024-24.2.5-lem-24`). -/
public theorem shifted_floor_sequence_card_ge (n : ℕ) (α ν : ℝ)
    (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hν₀ : 0 ≤ ν) (hν₁ : ν < 1)
    (hnαν : ν ≤ n * α) :
    ((Finset.Icc 1 n).filter
        (fun d : ℕ => (1 : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋)).card = n ∧
      ∀ k : ℕ, 2 ≤ k →
        (((Finset.Icc 1 n).filter
            (fun d : ℕ => (k : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋)).card : ℤ) =
          ⌊((n : ℝ) - ν) / (k - α)⌋ := by
  have hthreshold (k d : ℕ) (hd : 1 ≤ d) :
      (k : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋ ↔
        (d : ℝ) * ((k : ℝ) - α) ≤ n - ν := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [Int.le_floor, Int.cast_natCast, ← sub_le_iff_le_add, le_div_iff₀ hdpos, mul_comm]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · rw [Finset.filter_true_of_mem]
    · simp
    · intro d hd
      obtain ⟨hd₁, hdn⟩ := Finset.mem_Icc.mp hd
      have hdn' : (d : ℝ) ≤ n := by exact_mod_cast hdn
      have hmul := mul_le_mul_of_nonneg_right hdn' (sub_nonneg.mpr hα₁.le)
      have hlast : (n : ℝ) * (1 - α) ≤ n - ν := by
        rw [mul_sub, mul_one, sub_le_sub_iff_left]
        exact hnαν
      simpa only [Nat.cast_one] using (hthreshold 1 d hd₁).mpr (by simpa using hmul.trans hlast)
  · intro k hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : 1 ≤ (k : ℝ) - α := by linarith only [hk', hα₁]
    have hdenpos : 0 < (k : ℝ) - α := zero_lt_one.trans_le hden
    -- This also covers `n = 0`, when `hnαν` and `hν₀` force `ν = 0`.
    have hnum : 0 ≤ (n : ℝ) - ν := by
      apply sub_nonneg.mpr
      calc
        ν ≤ n * α := hnαν
        _ ≤ n * 1 := mul_le_mul_of_nonneg_left hα₁.le hn
        _ = n := mul_one _
    let t : ℝ := ((n : ℝ) - ν) / (k - α)
    have ht₀ : 0 ≤ ⌊t⌋ := Int.floor_nonneg.mpr (div_nonneg hnum hdenpos.le)
    have htn : t ≤ n := by
      apply (div_le_iff₀ hdenpos).mpr
      calc
        (n : ℝ) - ν ≤ n := sub_le_self _ hν₀
        _ = n * 1 := (mul_one _).symm
        _ ≤ n * ((k : ℝ) - α) := mul_le_mul_of_nonneg_left hden hn
    have hcast : (⌊t⌋.toNat : ℤ) = ⌊t⌋ := Int.toNat_of_nonneg ht₀
    have hbound : ⌊t⌋.toNat ≤ n := by
      have h : ⌊t⌋ ≤ (n : ℤ) := by exact_mod_cast (Int.floor_le t).trans htn
      exact_mod_cast (hcast.trans_le h)
    have hcut (d : ℕ) (hd : 1 ≤ d) :
        (k : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋ ↔ d ≤ ⌊t⌋.toNat := by
      rw [hthreshold k d hd, ← le_div_iff₀ hdenpos]
      change (d : ℝ) ≤ t ↔ d ≤ ⌊t⌋.toNat
      rw [← Int.cast_natCast, ← Int.le_floor]
      omega
    have hfilter :
        (Finset.Icc 1 n).filter (fun d : ℕ => (k : ℤ) ≤ ⌊((n : ℝ) - ν) / (d : ℝ) + α⌋) =
          Finset.Icc 1 ⌊t⌋.toNat := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hd, _⟩, h⟩
        exact ⟨hd, (hcut d hd).mp h⟩
      · rintro ⟨hd, h⟩
        exact ⟨⟨hd, h.trans hbound⟩, (hcut d hd).mpr h⟩
    rw [hfilter, Nat.card_Icc, Nat.add_sub_cancel]
    exact hcast

end MetaMathlibExt
