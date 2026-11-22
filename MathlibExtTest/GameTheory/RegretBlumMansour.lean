/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.RegretBlumMansour
public import MathlibExt.GameTheory.Regret

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.RegretBlumMansour

open MathlibExt.GameTheory.Regret
open scoped BigOperators

/-- Identity recommendations for the two-action test: copy `j` plays `j`. -/
def qId : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ j a => if a = j then 1 else 0

/-- Uniform master play for the two-action test. -/
noncomputable def pU : Fin 1 → Fin 2 → ℝ :=
  fun _ _ => 1 / 2

/-- Example losses for the two-action test. -/
def l0 : Fin 1 → Fin 2 → ℝ :=
  fun _ a => if a = 0 then 2 else 6

theorem t1_stationary : IsStationaryPlay qId pU := by
  refine ⟨?_, ?_⟩
  · intro t
    refine ⟨?_, ?_⟩
    · intro a
      show (0 : ℝ) ≤ 1 / 2
      norm_num
    · simp only [pU, Fin.sum_univ_two]
      norm_num
  · intro t i
    simp only [pU, qId, Fin.sum_univ_two]
    fin_cases i <;> simp

theorem t2_consensus_value :
    expectedLoss pU l0 = 4 ∧
      ∑ j, expectedLoss (fun t => qId t j) (scaledLoss pU l0 j) = 4 := by
  constructor
  · simp only [expectedLoss, pU, l0, Fin.sum_univ_one, Fin.sum_univ_two]
    simp
    norm_num
  · simp only [expectedLoss, scaledLoss, qId, pU, l0, Fin.sum_univ_two,
      Fin.sum_univ_one]
    simp
    norm_num

end MathlibExtTest.GameTheory.RegretBlumMansour
