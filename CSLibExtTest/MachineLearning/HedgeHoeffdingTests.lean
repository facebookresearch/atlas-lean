/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.HedgeHoeffding
public import Mathlib.Tactic.NormNum

/-!
# Hedge Hoeffding-bound tests

With two experts and one round of losses `0, 1` from unit weights, the total weight becomes
`1 + exp (-η)`, Hedge pays `1/2`, the one-step bound reads
`1 + exp (-η) ≤ 2 exp (-η / 2 + η² / 8)`, and the regret bound against the expert with loss `0`
reads `1/2 ≤ log 2 / η + η / 8`. A closed check instantiates the regret bound for five experts.
-/

namespace Cslib.MachineLearning.Hedge

open Real

private noncomputable def round1 : Fin 2 → ℝ := ![0, 1]

private lemma round1_nonneg (i : Fin 2) : 0 ≤ round1 i := by
  fin_cases i <;> simp [round1]

private lemma round1_le_one (i : Fin 2) : round1 i ≤ 1 := by
  fin_cases i <;> simp [round1]

private lemma bounded_round1 : Bounded [round1] := by
  intro ℓ hℓ i
  rw [List.mem_singleton] at hℓ
  subst hℓ
  exact ⟨round1_nonneg i, round1_le_one i⟩

/-- The one-step bound on the fixture: `1 + exp (-η) ≤ 2 exp (-η / 2 + η² / 8)`. -/
example (η : ℝ) (hη : 0 ≤ η) : 1 + exp (-η) ≤ 2 * exp (-η * (1 / 2) + η ^ 2 / 8) := by
  have h := total_update_le_hoeffding (w := fun _ : Fin 2 => (1 : ℝ)) (ℓ := round1)
    (fun _ => one_pos) (by norm_num) hη round1_nonneg round1_le_one
  have hl : total (update η (fun _ : Fin 2 => (1 : ℝ)) round1) = 1 + exp (-η) := by
    simp [total, update, Fin.sum_univ_two, round1]
  have hr : roundLoss (fun _ : Fin 2 => (1 : ℝ)) round1 = 1 / 2 := by
    simp only [roundLoss, total, Fin.sum_univ_two, round1]
    norm_num
  have ht : total (fun _ : Fin 2 => (1 : ℝ)) = 2 := by
    simp only [total, Fin.sum_univ_two]
    norm_num
  rw [hl, hr, ht] at h
  exact h

/-- The regret bound on the fixture, against expert `0` (loss `0`): Hedge pays `1/2`, so
`1/2 ≤ log 2 / η + η / 8`. -/
example (η : ℝ) (hη : 0 < η) : (1 : ℝ) / 2 ≤ log 2 / η + η / 8 := by
  have h := algLoss_le_hoeffding hη [round1] bounded_round1 0
  have hL : algLoss η [round1] (fun _ => 1) = 1 / 2 := by
    simp only [algLoss, roundLoss, total, Fin.sum_univ_two, round1]
    norm_num
  have hE : expertLoss 0 [round1] = 0 := by
    simp [expertLoss, round1]
  rw [hL, hE] at h
  simpa using h

/-! Closed checks -/

example (η : ℝ) (hη : 0 < η) (ls : List (Fin 5 → ℝ)) (hb : Bounded ls) (i : Fin 5) :
    algLoss η ls (fun _ => 1) ≤ expertLoss i ls + log 5 / η + η * ls.length / 8 := by
  have := algLoss_le_hoeffding hη ls hb i
  simpa using this

#print axioms total_update_le_hoeffding
#print axioms total_weights_le_hoeffding
#print axioms algLoss_le_hoeffding

end Cslib.MachineLearning.Hedge
