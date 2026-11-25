/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomidIndex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Averages of a binomid index

`IsBinomidIndex.binomidAverage_props` compares the initial average with averages of shifted blocks
and of prefixes of multiple length. It also gives the weighted average of two adjacent blocks.
-/

namespace MetaMathlibExt

/-- **Averages of a binomid index.** Let $\eta = (e_1, e_2, \dots)$ be a binomid index, write
$s_n = e_1 + \dots + e_n$, and for $i \ge 1$ and $l \ge 0$ let $A_{i,l} = (s_{i+l} - s_l)/i$
be the average of $e_{l+1}, \dots, e_{l+i}$. Then for all $i, l \ge 1$: $A_{i,l} \ge A_{i,0}$;
$A_{ki,0} \ge A_{i,0}$ for every $k \ge 1$; and
$A_{i+l,0} = \frac{i}{i+l} A_{i,l} + \frac{l}{l+i} A_{l,0}$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 2
(`integers-2024-A53-lem-2`). -/
public theorem IsBinomidIndex.binomidAverage_props {η : ℕ → ℕ} (hη : IsBinomidIndex η)
    {i l : ℕ} (hi : 1 ≤ i) (hl : 1 ≤ l) :
    binomidAverage η i ≤ ((∑ j ∈ Finset.Ico l (i + l), η j : ℕ) : ℚ) / i ∧
      (∀ k, 1 ≤ k → binomidAverage η i ≤ binomidAverage η (k * i)) ∧
      binomidAverage η (i + l) =
        (i : ℚ) / (i + l) * (((∑ j ∈ Finset.Ico l (i + l), η j : ℕ) : ℚ) / i) +
          (l : ℚ) / (l + i) * binomidAverage η l := by
  have block (a : ℕ) :
      ∑ j ∈ Finset.range i, η j ≤ ∑ j ∈ Finset.Ico a (a + i), η j := by
    simpa using hη i (a + i) (Nat.le_add_left i a)
  refine ⟨div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg i), ?_, ?_⟩
  · rw [add_comm i l]
    exact_mod_cast block l
  · intro k hk
    have blocks (n : ℕ) : n * ∑ j ∈ Finset.range i, η j ≤ ∑ j ∈ Finset.range (n * i), η j := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.succ_mul, Nat.succ_mul,
          ← Finset.sum_range_add_sum_Ico η (Nat.le_add_right (n * i) i)]
        exact Nat.add_le_add ih (block (n * i))
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [binomidAverage, binomidAverage, Nat.cast_mul, ← mul_div_mul_left _ _ hk']
    exact div_le_div_of_nonneg_right (by exact_mod_cast blocks k) (by positivity)
  · have hi' : (i : ℚ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
    have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
    rw [binomidAverage, binomidAverage, ← Finset.sum_range_add_sum_Ico η (Nat.le_add_left l i),
      Nat.cast_add, Nat.cast_add, add_comm (l : ℚ) i]
    field_simp
    ring

end MetaMathlibExt
