/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.BridgeTorchWeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # The return inequality for bridge crossings of capacity three -/

namespace MetaMathlibExt.BridgeTorchGeneralizations

private theorem bridgeWeight_return_bounds (i : ℕ) (hi : 0 < i) :
    0 ≤ bridgeWeight i ∧ -(3 : ℚ) ≤ bridgeWeight i - (i : ℚ) := by
  by_cases hi7 : 7 ≤ i
  · rw [bridgeWeight_of_seven_le i hi7]
    have hi' : (7 : ℚ) ≤ i := by exact_mod_cast hi7
    constructor <;> linarith
  · interval_cases i <;> norm_num [bridgeWeight]

/-- **Return inequality for the capacity-3 weights.** Let $y_i$ be the weights of the capacity-3
lower bound. For every nonempty set $R$ of positive integers with $|R| \le 3$,
$$\frac{9}{2}(|R| - 1) + \max R + \sum_{i \in R} (y_i - i) \ge 0.$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 16 (`jis-2026-26.5.6-lem-16`). -/
public theorem bridgeWeight_return_inequality (R : Finset ℕ) (hR : R.Nonempty)
    (hR3 : R.card ≤ 3) (hpos : 0 ∉ R) :
    0 ≤ 9 / 2 * ((R.card : ℚ) - 1) + ((R.max' hR : ℕ) : ℚ) +
      ∑ i ∈ R, (bridgeWeight i - (i : ℚ)) := by
  let m := R.max' hR
  have hm : m ∈ R := Finset.max'_mem R hR
  have hmem_pos (i : ℕ) (hi : i ∈ R) : 0 < i :=
    Nat.pos_of_ne_zero fun hz => hpos (hz ▸ hi)
  have hweight := (bridgeWeight_return_bounds m (hmem_pos m hm)).1
  have hs : ((R.erase m).card : ℚ) * (-3) ≤
      ∑ i ∈ R.erase m, (bridgeWeight i - (i : ℚ)) := by
    have hsum := Finset.sum_le_sum (s := R.erase m) (fun i hi =>
      (bridgeWeight_return_bounds i (hmem_pos i (Finset.mem_of_mem_erase hi))).2)
    simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
  -- The crossing time cancels the negative index of the maximum term.
  change 0 ≤ 9 / 2 * ((R.card : ℚ) - 1) + (m : ℚ) +
    ∑ i ∈ R, (bridgeWeight i - (i : ℚ))
  rw [← Finset.sum_erase_add R (fun i => bridgeWeight i - (i : ℚ)) hm]
  have hsize : ((R.erase m).card : ℚ) + 1 = (R.card : ℚ) := by
    exact_mod_cast (Finset.card_erase_add_one hm)
  have hcard_pos := Finset.card_pos.mpr hR
  have hcases : R.card = 1 ∨ R.card = 2 ∨ R.card = 3 := by omega
  have hcast : (R.card : ℚ) = 1 ∨ (R.card : ℚ) = 2 ∨ (R.card : ℚ) = 3 := by
    rcases hcases with hc | hc | hc
    · exact Or.inl (by exact_mod_cast hc)
    · exact Or.inr (Or.inl (by exact_mod_cast hc))
    · exact Or.inr (Or.inr (by exact_mod_cast hc))
  simp only [Finset.sum_sub_distrib] at hs ⊢
  rcases hcast with hc | hc | hc <;> linarith only [hsize, hs, hweight, hc]

end MetaMathlibExt.BridgeTorchGeneralizations
