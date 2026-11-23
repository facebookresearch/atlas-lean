/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Optimization.RandomHyperplane

@[expose] public section

open Real MeasureTheory ProbabilityTheory MathlibExt.Combinatorics.Optimization.GoemansWilliamson

namespace MathlibExtTest.Combinatorics.Optimization.RandomHyperplane

/-- Antipodal unit vectors in `ℝ^1` are separated almost surely. -/
example : (stdGaussian (EuclideanSpace ℝ (Fin 1))).real
    {r | (0 ≤ inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) r) ≠
      (0 ≤ inner ℝ (-EuclideanSpace.single 0 (1 : ℝ)) r)} = 1 := by
  rw [measureReal_sign_ne (by simp) (by simp)]
  simp [arccos_neg_one, pi_ne_zero]

/-- Theorem 3.1 on one edge embedded antipodally: the expected cut weight is the edge weight. -/
example : ∫ r, cutWeight (fun _ _ : Fin 2 => (1 : ℝ))
      (Finset.univ.filter fun i => 0 ≤ inner ℝ
        (cutSign ({0} : Finset (Fin 2)) i • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) r)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 1))) =
    hyperplaneExpectation (fun _ _ : Fin 2 => (1 : ℝ))
      (fun i => cutSign ({0} : Finset (Fin 2)) i • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :=
  integral_cutWeight_hyperplane _
    (vectorObjective_cutSign_single Nat.one_pos (fun _ _ => (1 : ℝ)) {0}).1

/-- Non-vacuity of the `ε`-version: any unit vectors qualify with
`ε = Z_P - (their objective)`. -/
example (S : Finset (Fin 2)) :
    let v := fun i => cutSign ({0} : Finset (Fin 2)) i • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
    gwConstant * (cutWeight (fun _ _ : Fin 2 => (1 : ℝ)) S -
        (relaxationValue (fun _ _ : Fin 2 => (1 : ℝ)) 1 -
          vectorObjective (fun _ _ : Fin 2 => (1 : ℝ)) v)) ≤
      ∫ r, cutWeight (fun _ _ : Fin 2 => (1 : ℝ))
        (Finset.univ.filter fun i => 0 ≤ inner ℝ (v i) r)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  intro v
  exact gwConstant_mul_cutWeight_sub_le_integral Nat.one_pos (fun _ _ => zero_le_one)
    (vectorObjective_cutSign_single Nat.one_pos (fun _ _ => (1 : ℝ)) {0}).1
    (le_of_eq (sub_sub_cancel _ _)) S

end MathlibExtTest.Combinatorics.Optimization.RandomHyperplane
