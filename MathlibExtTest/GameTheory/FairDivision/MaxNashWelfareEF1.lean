/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.FairDivision.Indivisible
public import MathlibExt.GameTheory.FairDivision.MaxNashWelfare
public import MathlibExt.GameTheory.FairDivision.MaxNashWelfareEF1

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.FairDivision.MaxNashWelfareEF1

@[expose] public section

open MathlibExt.GameTheory.FairDivision.Indivisible

/-- Test valuations: agent `0` values goods `(4, 3, 0)`, agent `1` values
`(0, 3, 4)`. -/
def tv : Fin 2 → Fin 3 → ℝ := fun i g =>
  if i = 0 then (if g = 0 then 4 else if g = 1 then 3 else 0)
  else (if g = 0 then 0 else if g = 1 then 3 else 4)

/-- Test allocation: goods `0`, `1` to agent `0`, good `2` to agent `1`. -/
def tA : Fin 3 → Fin 2 := fun g => if g = 2 then 1 else 0

/-- Test values for `tv` and `tA`: bundle values `7` and `4`, welfare `28`. -/
theorem t1_values :
    value tv tA 0 = 7 ∧ value tv tA 1 = 4 ∧ positiveWelfare tv tA = 28 := by
  have hb0 : bundle tA 0 = {0, 1} := by decide
  have hb1 : bundle tA 1 = {2} := by decide
  have hv0 : value tv tA 0 = 7 := by
    unfold value bundleValue
    rw [hb0, Finset.sum_insert (by decide), Finset.sum_singleton]
    show (4 : ℝ) + 3 = 7
    norm_num
  have hv1 : value tv tA 1 = 4 := by
    unfold value bundleValue
    rw [hb1, Finset.sum_singleton]
    rfl
  have hw : positiveWelfare tv tA = 28 := by
    have hall : ∀ i : Fin 2, 0 < value tv tA i := by
      rw [Fin.forall_fin_two]
      constructor
      · rw [hv0]
        norm_num
      · rw [hv1]
        norm_num
    have hpos : positiveAgents tv tA = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hall i
    unfold positiveWelfare
    rw [hpos]
    have hprod : (∏ i ∈ Finset.univ, value tv tA i) = ∏ i, value tv tA i := by
      simp
    rw [hprod, Fin.prod_univ_two, hv0, hv1]
    norm_num
  exact ⟨hv0, hv1, hw⟩

/-- Test transfer values: moving good `1` to agent `1` gives values `4`
and `7`, with bundle `{1, 2}`. -/
theorem t2_transfer_values :
    value tv (transfer tA 1 1) 0 = 4 ∧ value tv (transfer tA 1 1) 1 = 7 ∧
    bundle (transfer tA 1 1) 1 = {1, 2} := by
  have hbB0 : bundle (transfer tA 1 1) 0 = {0} := by decide
  have hbB1 : bundle (transfer tA 1 1) 1 = {1, 2} := by decide
  have hvB0 : value tv (transfer tA 1 1) 0 = 4 := by
    unfold value bundleValue
    rw [hbB0, Finset.sum_singleton]
    rfl
  have hvB1 : value tv (transfer tA 1 1) 1 = 7 := by
    unfold value bundleValue
    rw [hbB1, Finset.sum_insert (by decide), Finset.sum_singleton]
    show (3 : ℝ) + 4 = 7
    norm_num
  exact ⟨hvB0, hvB1, hbB1⟩

/-- The welfare bound from the two bundle values: the product over the
positive agents is empty, one value, or both values. -/
theorem positiveWelfare_le_of_values {B : Fin 3 → Fin 2} {x y : ℝ}
    (h0 : value tv B 0 = x) (h1 : value tv B 1 = y)
    (hxy : x * y ≤ 28) (hx : x ≤ 28) (hy : y ≤ 28) :
    positiveWelfare tv B ≤ 28 := by
  unfold positiveWelfare
  by_cases h0m : (0 : Fin 2) ∈ positiveAgents tv B <;>
    by_cases h1m : (1 : Fin 2) ∈ positiveAgents tv B
  · have hset : positiveAgents tv B = {0, 1} := by
      ext i
      fin_cases i <;> simp [h0m, h1m]
    rw [hset, Finset.prod_pair (by decide), h0, h1]
    exact hxy
  · have hset : positiveAgents tv B = {0} := by
      ext i
      fin_cases i <;> simp [h0m, h1m]
    rw [hset, Finset.prod_singleton, h0]
    exact hx
  · have hset : positiveAgents tv B = {1} := by
      ext i
      fin_cases i <;> simp [h0m, h1m]
    rw [hset, Finset.prod_singleton, h1]
    exact hy
  · have hset : positiveAgents tv B = ∅ := by
      ext i
      fin_cases i <;> simp [h0m, h1m]
    rw [hset, Finset.prod_empty]
    norm_num

/-- The bundle value of an allocation is the indicator-weighted sum over
the three goods. -/
theorem value_eq_indicator_sum (B : Fin 3 → Fin 2) (i : Fin 2) :
    value tv B i = (if B 0 = i then tv i 0 else 0)
      + (if B 1 = i then tv i 1 else 0)
      + (if B 2 = i then tv i 2 else 0) := by
  unfold value bundleValue bundle
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_three]

/-- T3: `tA` is maximum Nash welfare, checked against all eight
allocations. -/
theorem tA_isMaxNashWelfare : IsMaxNashWelfare tv tA := by
  intro B
  have hposA : positiveAgents tv tA = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [positiveAgents, Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases i
    · show (0 : ℝ) < value tv tA 0
      rw [t1_values.1]
      norm_num
    · show (0 : ℝ) < value tv tA 1
      rw [t1_values.2.1]
      norm_num
  have hcardA : (positiveAgents tv tA).card = 2 := by
    rw [hposA]
    simp
  have hwA : positiveWelfare tv tA = 28 := t1_values.2.2
  have hcardB : (positiveAgents tv B).card ≤ 2 := by
    calc (positiveAgents tv B).card ≤ Finset.univ.card :=
          Finset.card_le_univ _
      _ = 2 := by simp
  refine ⟨by rw [hcardA]; exact hcardB, fun _ => ?_⟩
  have h01 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by
    intro x
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h0 := h01 (B 0)
  have h1 := h01 (B 1)
  have h2 := h01 (B 2)
  rw [hwA]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    · have hv0 : value tv B 0 = (if B 0 = 0 then (4 : ℝ) else 0)
          + (if B 1 = 0 then 3 else 0) + (if B 2 = 0 then 0 else 0) := by
        rw [value_eq_indicator_sum]
        norm_num [tv]
      have hv1 : value tv B 1 = (if B 0 = 1 then (0 : ℝ) else 0)
          + (if B 1 = 1 then 3 else 0) + (if B 2 = 1 then 4 else 0) := by
        rw [value_eq_indicator_sum]
        norm_num [tv]
      rw [h0, h1, h2] at hv0 hv1
      norm_num at hv0 hv1
      exact positiveWelfare_le_of_values hv0 hv1 (by norm_num [hv0, hv1])
        (by norm_num [hv0]) (by norm_num [hv1])

/-- T4: EF1 of `tA`, through the maximum-Nash-welfare theorem. -/
theorem tA_isEF1 : IsEF1 tv tA :=
  isEF1_of_isMaxNashWelfare
    (fun i g => by fin_cases i <;> fin_cases g <;> norm_num [tv])
    tA_isMaxNashWelfare

end

end MathlibExtTest.GameTheory.FairDivision.MaxNashWelfareEF1
