/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Weights for bridge crossings of capacity three -/

@[expose] public section

namespace MetaMathlibExt.BridgeTorchGeneralizations

open Finset

/-- **Weights of the capacity-3 lower bound.** The rational weights $y_i$ are
$y_1 = y_2 = y_3 = 0$, $y_4 = 2$, $y_5 = 4$, $y_6 = 5$, and $y_i = (4i - 8)/3$ for $i \ge 7$.
The value $y_0$ is unused and set to $0$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
def bridgeWeight : ℕ → ℚ
  | 0 | 1 | 2 | 3 => 0
  | 4 => 2
  | 5 => 4
  | 6 => 5
  | i + 7 => (4 * ((i + 7 : ℕ) : ℚ) - 8) / 3

/-- **First seven weights of the capacity-3 lower bound.** The weights $y_1, \dots, y_7$ of the
capacity-3 lower bound are $0, 0, 0, 2, 4, 5, 20/3$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
theorem bridgeWeight_small :
    bridgeWeight 1 = 0 ∧ bridgeWeight 2 = 0 ∧ bridgeWeight 3 = 0 ∧ bridgeWeight 4 = 2 ∧
      bridgeWeight 5 = 4 ∧ bridgeWeight 6 = 5 ∧ bridgeWeight 7 = 20 / 3 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [bridgeWeight]
  norm_num

/-- **Weights of the capacity-3 lower bound from $7$ on.** For every natural number $i \ge 7$,
the weight $y_i$ of the capacity-3 lower bound equals $(4i - 8)/3$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15. -/
theorem bridgeWeight_of_seven_le (i : ℕ) (hi : 7 ≤ i) :
    bridgeWeight i = (4 * (i : ℚ) - 8) / 3 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hi
  rfl

-- For a maximum m ≥ 7, only the two largest possible indices need a correction.
private theorem adjusted_weight_le {i m : ℕ} (hi : 0 < i) (him : i ≤ m) (hm : 7 ≤ m) :
    bridgeWeight i + 9 / 2 ≤ i + ((m : ℚ) / 3 + 7 / 6) +
      (if i = m then 2 / 3 else 0) + (if i = m - 1 then 1 / 3 else 0) := by
  by_cases hi7 : 7 ≤ i
  · rw [bridgeWeight_of_seven_le i hi7]
    have hgap : (i : ℚ) + 2 ≤ m + (if i = m then 2 else 0) +
        (if i = m - 1 then 1 else 0) := by
      split_ifs <;> norm_cast <;> omega
    split_ifs at hgap ⊢ <;> linarith
  · have hweight : bridgeWeight i ≤ (i : ℚ) - 1 := by
      interval_cases i <;> norm_num [bridgeWeight]
    have hm' : (7 : ℚ) ≤ m := by exact_mod_cast hm
    split_ifs <;> linarith

/-- **Local inequality for the capacity-3 weights.** Let $y_i$ be the weights of the capacity-3
lower bound. For every nonempty set $T$ of positive integers with $|T| \le 3$,
$$\sum_{i \in T} y_i + \frac{9}{2}(|T| - 1) \le \max T + \sum_{i \in T} i.$$

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Lemma 15 (`jis-2026-26.5.6-lem-15`). -/
theorem bridgeWeight_local_inequality (T : Finset ℕ) (hT : T.Nonempty)
    (hT3 : T.card ≤ 3) (hpos : 0 ∉ T) :
    (∑ i ∈ T, bridgeWeight i) + 9 / 2 * ((T.card : ℚ) - 1) ≤
      ((T.max' hT : ℕ) : ℚ) + ∑ i ∈ T, (i : ℚ) := by
  set m := T.max' hT
  have hpos' (i) (hi : i ∈ T) : 0 < i := Nat.pos_of_ne_zero fun h ↦ hpos (h ▸ hi)
  have hle (i) (hi : i ∈ T) : i ≤ m := T.le_max' i hi
  by_cases hm : 7 ≤ m
  · have hsum := sum_le_sum fun i (hi : i ∈ T) ↦ adjusted_weight_le (hpos' i hi) (hle i hi) hm
    have hmem : m ∈ T := T.max'_mem hT
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq', hmem, ↓reduceIte] at hsum
    have hcard : (T.card : ℚ) ≤ 3 := by exact_mod_cast hT3
    have hm' : (7 : ℚ) ≤ m := by exact_mod_cast hm
    have hcap := mul_le_mul_of_nonneg_right hcard (show 0 ≤ (m : ℚ) / 3 + 7 / 6 by linarith)
    split_ifs at hsum <;> linarith
  · have hsmall : ∀ S ∈ (Icc 1 6 : Finset ℕ).powerset, ∀ hS : S.Nonempty, S.card ≤ 3 →
        (∑ i ∈ S, bridgeWeight i) + 9 / 2 * ((S.card : ℚ) - 1) ≤
          (S.max' hS : ℚ) + ∑ i ∈ S, (i : ℚ) := by decide +kernel
    apply hsmall T (mem_powerset.mpr ?_) hT hT3
    intro i hi
    exact mem_Icc.mpr ⟨hpos' i hi, (hle i hi).trans (by omega)⟩

end MetaMathlibExt.BridgeTorchGeneralizations
