/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Generic finite packet regrouping before specializing to the original Conway coordinates. -/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Basic.Real.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem sum_smul_local {I E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset I) (c : I → ℝ) (x : E) :
    (∑ i ∈ s, c i • x) = (∑ i ∈ s, c i) • x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, add_smul]

/-- A finite weighted packet can be regrouped by its actual finite dictionary key. -/
theorem monsterNortonLine02_keyed_sum {I J E : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] [AddCommMonoid E] [Module ℝ E]
    (key : I → J) (c : I → ℝ) (F : J → E) :
    (∑ i : I, c i • F (key i)) =
      ∑ j : J, (∑ i : I, if key i = j then c i else 0) • F j := by
  calc
    _ = ∑ i : I, ∑ j : J, (if key i = j then c i else 0) • F j := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_eq]
      simp
    _ = ∑ j : J, ∑ i : I, (if key i = j then c i else 0) • F j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_smul_local Finset.univ _ _

/-- Regrouping retains the exact zero coefficients of discarded finite packet entries. -/
theorem monsterNortonLine02_selected_keyed_sum {I J E : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] [AddCommMonoid E] [Module ℝ E]
    (select : I → Bool) (key : I → J) (c : I → ℝ) (F : J → E) :
    (∑ i : I, if select i then c i • F (key i) else 0) =
      ∑ j : J, (∑ i : I, if select i ∧ key i = j then c i else 0) • F j := by
  have h := monsterNortonLine02_keyed_sum key (fun i => if select i then c i else 0) F
  calc
    _ = ∑ j : J, (∑ i : I, if key i = j then (if select i then c i else 0) else 0) • F j := by
      simpa only [ite_smul, zero_smul] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hs : select i = true <;> by_cases hk : key i = j <;> simp [hs, hk]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
