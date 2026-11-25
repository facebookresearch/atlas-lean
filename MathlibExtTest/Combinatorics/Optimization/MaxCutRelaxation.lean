/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Optimization.MaxCutRelaxation
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

open Real MathlibExt.Combinatorics.Optimization.GoemansWilliamson

namespace MathlibExtTest.Combinatorics.Optimization.MaxCutRelaxation

/-- One edge `{0, 1}` of weight `1`. -/
def edgeWeight : Fin 2 → Fin 2 → ℝ := fun _ _ => 1

/-- The cut `{0}` of the single edge has weight `1`. -/
theorem cutWeight_single : cutWeight edgeWeight {0} = 1 := by
  simp [cutWeight, pairs, edgeWeight, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Non-vacuity: the relaxation value of the single edge is at least `1` in `ℝ^1`. -/
example : 1 ≤ relaxationValue edgeWeight 1 := by
  have h := cutWeight_le_relaxationValue (m := 1) Nat.one_pos edgeWeight {0}
  rwa [cutWeight_single] at h

/-- The term-by-term bound applies to the antipodal embedding of the cut `{0}`. -/
example : gwConstant * vectorObjective edgeWeight
      (fun i => cutSign ({0} : Finset (Fin 2)) i • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ≤
    hyperplaneExpectation edgeWeight
      (fun i => cutSign ({0} : Finset (Fin 2)) i • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :=
  gwConstant_mul_vectorObjective_le (fun _ _ => zero_le_one)
    (vectorObjective_cutSign_single Nat.one_pos edgeWeight {0}).1

/-- The identity matrix is feasible for the semidefinite program (orthonormal vectors). -/
theorem sdpFeasible_one : SDPFeasible (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
  ⟨Matrix.PosSemidef.one, fun i => by simp⟩

/-- Non-vacuity: the identity is the Gram matrix of unit vectors in some `ℝ^m`. -/
example : ∃ m : ℕ, ∃ v : Fin 3 → EuclideanSpace ℝ (Fin m), (∀ i, ‖v i‖ = 1) ∧
    Matrix.gram ℝ v = 1 :=
  exists_gram_eq_of_sdpFeasible sdpFeasible_one

end MathlibExtTest.Combinatorics.Optimization.MaxCutRelaxation
