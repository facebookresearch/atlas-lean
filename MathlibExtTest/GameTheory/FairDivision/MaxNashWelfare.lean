/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.FairDivision.MaxNashWelfare

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.FairDivision.MaxNashWelfare

open MathlibExt.GameTheory.FairDivision.Indivisible

@[expose] public section

/-- Test valuation on two agents and two goods. -/
def tv : Fin 2 → Fin 2 → ℝ := fun i g =>
  if i = 0 then (if g = 0 then 3 else 1) else (if g = 0 then 1 else 2)

/-- Test allocation giving each good to the agent with the same index. -/
def tA0 : Fin 2 → Fin 2 := fun g => g

/-- Test allocation giving both goods to agent `0`. -/
def tA1 : Fin 2 → Fin 2 := fun _ => 0

/-- Values of the test valuation on all four agent-good pairs. -/
theorem tv_values : tv 0 0 = 3 ∧ tv 0 1 = 1 ∧ tv 1 0 = 1 ∧ tv 1 1 = 2 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp [tv, h10]

/-- Bundle values of the test allocations: under `tA0` the values are `3, 2`;
under `tA1` they are `4, 0`. -/
theorem tA_values :
    value tv tA0 0 = 3 ∧ value tv tA0 1 = 2 ∧
      value tv tA1 0 = 4 ∧ value tv tA1 1 = 0 := by
  have h00 : value tv tA0 0 = 3 := by
    have hb : bundle tA0 0 = {0} := by decide
    simp [value, bundleValue, hb, tv_values]
  have h01 : value tv tA0 1 = 2 := by
    have hb : bundle tA0 1 = {1} := by decide
    simp [value, bundleValue, hb, tv_values]
  have h10 : value tv tA1 0 = 4 := by
    have hb : bundle tA1 0 = {0, 1} := by decide
    have hne : (0 : Fin 2) ≠ 1 := by decide
    simp only [value, bundleValue, hb, Finset.sum_pair hne, tv_values]
    norm_num
  have h11 : value tv tA1 1 = 0 := by
    have hb : bundle tA1 1 = ∅ := by decide
    simp [value, bundleValue, hb]
  exact ⟨h00, h01, h10, h11⟩

/-- The positive-agent sets of the two test allocations. -/
theorem positiveAgents_test :
    positiveAgents tv tA0 = Finset.univ ∧ positiveAgents tv tA1 = {0} := by
  obtain ⟨h00, h01, h10, h11⟩ := tA_values
  have hA0 : positiveAgents tv tA0 = Finset.univ := by
    ext i
    simp only [mem_positiveAgents, Finset.mem_univ, iff_true]
    fin_cases i <;> simp [h00, h01]
  have hA1 : positiveAgents tv tA1 = {0} := by
    ext i
    simp only [mem_positiveAgents, Finset.mem_singleton]
    fin_cases i <;> simp [h10, h11]
  exact ⟨hA0, hA1⟩

/-- T1: positive-agent counts of the test allocations are `2` and `1`. -/
theorem t1_positiveAgents_card :
    (positiveAgents tv tA0).card = 2 ∧ (positiveAgents tv tA1).card = 1 := by
  obtain ⟨hA0, hA1⟩ := positiveAgents_test
  simp [hA0, hA1]

/-- T2: positive welfare values of the test allocations are `6` and `4`. -/
theorem t2_positiveWelfare_values :
    positiveWelfare tv tA0 = 6 ∧ positiveWelfare tv tA1 = 4 := by
  obtain ⟨hA0, hA1⟩ := positiveAgents_test
  obtain ⟨h00, h01, h10, _⟩ := tA_values
  constructor
  · simp only [positiveWelfare, hA0, Fin.prod_univ_two, h00, h01]
    norm_num
  · simp only [positiveWelfare, hA1, Finset.prod_singleton, h10]

/-- T3: with all agents positive, positive welfare is the Nash welfare. -/
theorem t3_positiveWelfare_eq_nashWelfare :
    positiveWelfare tv tA0 = nashWelfare tv tA0 := by
  obtain ⟨h00, h01, _, _⟩ := tA_values
  apply positiveWelfare_eq_nashWelfare
  intro i
  fin_cases i <;> simp [h00, h01]


/-- Test allocation exchanging the two goods. -/
def tA2 : Fin 2 → Fin 2 := fun g => if g = 0 then 1 else 0

/-- Test allocation giving both goods to agent `1`. -/
def tA3 : Fin 2 → Fin 2 := fun _ => 1

/-- Bundle values and positive welfare for the exchanged allocation. -/
theorem tA2_values :
    value tv tA2 0 = 1 ∧ value tv tA2 1 = 1 ∧ positiveWelfare tv tA2 = 1 := by
  have h0 : value tv tA2 0 = 1 := by
    have hb : bundle tA2 0 = {1} := by decide
    simp [value, bundleValue, hb, tv_values]
  have h1 : value tv tA2 1 = 1 := by
    have hb : bundle tA2 1 = {0} := by decide
    simp [value, bundleValue, hb, tv_values]
  have hpos : positiveAgents tv tA2 = Finset.univ := by
    ext i
    simp only [mem_positiveAgents, Finset.mem_univ, iff_true]
    fin_cases i <;> simp [h0, h1]
  refine ⟨h0, h1, ?_⟩
  simp only [positiveWelfare, hpos, Fin.prod_univ_two, h0, h1, mul_one]

/-- Bundle values and positive welfare when both goods go to agent `1`. -/
theorem tA3_values :
    value tv tA3 0 = 0 ∧ value tv tA3 1 = 3 ∧ positiveWelfare tv tA3 = 3 := by
  have h0 : value tv tA3 0 = 0 := by
    have hb : bundle tA3 0 = ∅ := by decide
    simp [value, bundleValue, hb]
  have h1 : value tv tA3 1 = 3 := by
    have hb : bundle tA3 1 = {0, 1} := by decide
    have hne : (0 : Fin 2) ≠ 1 := by decide
    simp only [value, bundleValue, hb, Finset.sum_pair hne, tv_values]
    norm_num
  have hpos : positiveAgents tv tA3 = {1} := by
    ext i
    simp only [mem_positiveAgents, Finset.mem_singleton]
    fin_cases i <;> simp [h0, h1]
  refine ⟨h0, h1, ?_⟩
  simp only [positiveWelfare, hpos, Finset.prod_singleton, h1]

/-- Every allocation of two goods to two agents is one of the four test
allocations. -/
theorem allocation_cases (B : Fin 2 → Fin 2) :
    B = tA1 ∨ B = tA0 ∨ B = tA2 ∨ B = tA3 := by
  have h0 : B 0 = 0 ∨ B 0 = 1 := by
    have hval : (B 0).val = 0 ∨ (B 0).val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  have h1 : B 1 = 0 ∨ B 1 = 1 := by
    have hval : (B 1).val = 0 ∨ (B 1).val = 1 := by omega
    exact hval.imp Fin.ext Fin.ext
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · refine Or.inl ?_
    funext g
    fin_cases g <;> simp [tA1, h0, h1]
  · refine Or.inr (Or.inl ?_)
    funext g
    fin_cases g <;> simp [tA0, h0, h1]
  · refine Or.inr (Or.inr (Or.inl ?_))
    funext g
    fin_cases g <;> simp [tA2, h0, h1]
  · refine Or.inr (Or.inr (Or.inr ?_))
    funext g
    fin_cases g <;> simp [tA3, h0, h1]

/-- T4: `tA0` is maximum Nash welfare, checked against all four allocations. -/
theorem tA0_isMaxNashWelfare : IsMaxNashWelfare tv tA0 := by
  intro B
  have hcardA : (positiveAgents tv tA0).card = 2 := t1_positiveAgents_card.1
  have hwA : positiveWelfare tv tA0 = 6 := t2_positiveWelfare_values.1
  have hcardB : (positiveAgents tv B).card ≤ 2 := by
    calc (positiveAgents tv B).card ≤ Finset.univ.card :=
          Finset.card_le_univ _
      _ = 2 := by simp
  refine ⟨by rw [hcardA]; exact hcardB, fun _ => ?_⟩
  rcases allocation_cases B with rfl | rfl | rfl | rfl
  · rw [t2_positiveWelfare_values.2, hwA]
    norm_num
  · exact le_refl _
  · rw [tA2_values.2.2, hwA]
    norm_num
  · rw [tA3_values.2.2, hwA]
    norm_num

/-- T5: Pareto optimality of `tA0`, through the MNW theorem. -/
theorem tA0_isParetoOptimal : IsParetoOptimal tv tA0 :=
  isParetoOptimal_of_isMaxNashWelfare tv
    (fun i g => by fin_cases i <;> fin_cases g <;> simp [tv]) tA0_isMaxNashWelfare

/-- T6: boundary case: with the zero valuation no allocation makes any
agent positive, yet an MNW (hence Pareto-optimal) allocation exists. -/
theorem t6_zero_boundary :
    ∃ A : Fin 2 → Fin 2, IsMaxNashWelfare (fun _ _ => (0 : ℝ)) A ∧
      IsParetoOptimal (fun _ _ => (0 : ℝ)) A := by
  obtain ⟨A, hA⟩ := exists_isMaxNashWelfare (ι := Fin 2) (γ := Fin 2)
    (fun _ _ => (0 : ℝ))
  exact ⟨A, hA, isParetoOptimal_of_isMaxNashWelfare _
    (fun _ _ => le_refl 0) hA⟩
end

end MathlibExtTest.GameTheory.FairDivision.MaxNashWelfare
