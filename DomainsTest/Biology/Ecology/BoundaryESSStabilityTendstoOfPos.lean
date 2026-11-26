/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.BoundaryESSStabilityTendstoOfPos
import Domains.Biology.Dynamics.ReplicatorStability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Global attraction in the Hawk–Dove game

An interior solution starting at `(1/4, 3/4)` converges to the ESS `(1/2, 1/2)`.
-/

open Matrix Filter Topology
open WantedExt.Biology.Ecology.BoundaryESSStabilityWanted

namespace DomainsTest.Biology.Ecology.BoundaryESSStabilityTendstoOfPos

private def hawkDove : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 2; 0, 1]

private noncomputable def half : Fin 2 → ℝ := ![1 / 2, 1 / 2]

private theorem half_isESS : IsESS hawkDove half := by
  refine ⟨⟨fun i => ?_, ?_⟩, fun q hq hne => Or.inr ⟨?_, ?_⟩⟩
  · fin_cases i <;> norm_num [half]
  · norm_num [half, Fin.sum_univ_two]
  · have h1 := hq.2
    simp only [Fin.sum_univ_two] at h1
    simp [hawkDove, half, mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith
  · have h1 := hq.2
    simp only [Fin.sum_univ_two] at h1
    have h0 : q 0 - 1 / 2 ≠ 0 := fun h0 => hne <| by
      funext i
      fin_cases i <;> simp [half] <;> linarith
    have hsq := pow_pos (abs_pos.2 h0) 2
    rw [sq_abs] at hsq
    simp [hawkDove, half, mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith

example : ∃ x : ℝ → Fin 2 → ℝ, x 0 = ![1 / 4, 3 / 4] ∧
    IsReplicatorSolution hawkDove x ∧ Tendsto x atTop (𝓝 half) := by
  have h0 : (![1 / 4, 3 / 4] : Fin 2 → ℝ) ∈ simplex (Fin 2) :=
    ⟨fun i => by fin_cases i <;> norm_num, by norm_num [Fin.sum_univ_two]⟩
  obtain ⟨x, hx0, hx⟩ :=
    MathlibExt.Biology.Dynamics.Replicator.exists_isSolution_mulVec hawkDove h0
  have hsol : IsReplicatorSolution hawkDove x := hx.hasDerivAt
  refine ⟨x, hx0, hsol, half_isESS.tendsto_of_pos ?_ hsol (hx0 ▸ h0) ?_⟩
  · intro i
    fin_cases i <;> norm_num [half]
  · intro i
    rw [hx0]
    fin_cases i <;> norm_num

end DomainsTest.Biology.Ecology.BoundaryESSStabilityTendstoOfPos
