/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Hedge
public import Mathlib.Tactic.NormNum

/-!
# Hedge tests

The reals are not computable, so the fixtures are checked by proof: with two experts and one
round of losses `0, 1`, Hedge pays `1/2` from unit weights, the experts end with weights `1`
and `exp (-η)`, and the round's second moment is `1/2`; the chord inequality is an equality at
`x = 0` and `x = 1`; a two-round run splits after its first round. Closed checks instantiate the
first- and second-order loss bounds.
-/

namespace Cslib.MachineLearning.Hedge

open Real

private noncomputable def round1 : Fin 2 → ℝ := ![0, 1]

example (η : ℝ) : algLoss η [round1] (fun _ => 1) = 1 / 2 := by
  simp only [algLoss, roundLoss, total, Fin.sum_univ_two, round1]
  norm_num

example (η : ℝ) : weights η [round1] (fun _ => 1) = ![1, exp (-η)] := by
  funext i
  rw [weights_apply]
  fin_cases i <;> simp [expertLoss, round1]

example (η : ℝ) : exp (-η * 0) = 1 - (1 - exp (-η)) * 0 := by simp

example (η : ℝ) : exp (-η * 1) = 1 - (1 - exp (-η)) * 1 := by simp

/-- The second moment of the same round is `1/2`, and a run splits at any round. -/
example (η : ℝ) : algSq η [round1] (fun _ => 1) = 1 / 2 := by
  simp only [algSq, roundSq, total, Fin.sum_univ_two, round1]
  norm_num

example (η : ℝ) : algLoss η ([round1] ++ [round1]) (fun _ => 1) =
    1 / 2 + algLoss η [round1] (weights η [round1] fun _ => 1) := by
  rw [algLoss_append]
  congr 1
  simp only [algLoss, roundLoss, total, Fin.sum_univ_two, round1]
  norm_num

/-! Closed checks -/

example (η : ℝ) (ls : List (Fin 5 → ℝ)) (hb : Bounded ls) (i : Fin 5) :
    (1 - exp (-η)) * algLoss η ls (fun _ => 1) ≤ η * expertLoss i ls + log 5 := by
  have := algLoss_le ls hb i (η := η)
  simpa using this

example (η : ℝ) (hη : 0 < η) (ls : List (Fin 5 → ℝ)) (hb : Nonneg ls) (i : Fin 5) :
    algLoss η ls (fun _ => 1) ≤ expertLoss i ls + η * algSq η ls (fun _ => 1) + log 5 / η := by
  have := algLoss_le_sq hη ls hb i
  simpa using this

#print axioms algLoss_le
#print axioms total_weights_le
#print axioms algLoss_le_sq

end Cslib.MachineLearning.Hedge
