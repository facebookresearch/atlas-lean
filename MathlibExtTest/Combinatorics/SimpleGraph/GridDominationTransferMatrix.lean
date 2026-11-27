/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GridDominationTransferMatrix

/-!
# Tests for the grid and cylinder domination transfer formulas

Check the empty-grid boundary, the count of dominating sets of a square, the empty cylinders and
the count of dominating sets of the triangular prism.
-/

open MetaMathlibExt DominationState Polynomial SimpleGraph

open scoped Classical in
-- With zero rows, only the all-covered boundary contributes to the transfer sum.
example (m : ℕ) :
    ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph m))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      (dominationTransferMatrix (pathGraph m) ^ (0 : ℕ)) σ (allCoveredSignature _) = 1 := by
  rw [← dominationPolynomial_grid_eq_sum_transferMatrix_pow]
  have h : (default : Finset (Fin m × Fin 0)) = ∅ := rfl
  simp [dominationPolynomial, Finset.univ_unique, IsDominating, h]

open scoped Classical in
-- The square has six dominating pairs, four triples, and the full set.
example :
    (∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph 2))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      (dominationTransferMatrix (pathGraph 2) ^ (2 : ℕ)) σ (allCoveredSignature _)).eval 1 = 11 := by
  let (S : Finset (Fin 2 × Fin 2)) :
      Decidable ((pathGraph 2 □ pathGraph 2).IsDominating (S : Set _)) := by
    simp only [IsDominating, Finset.mem_coe, boxProd_adj]
    infer_instance
  rw [← dominationPolynomial_grid_eq_sum_transferMatrix_pow, dominationPolynomial_eval_one]
  decide

#print axioms MetaMathlibExt.dominationPolynomial_grid_eq_sum_transferMatrix_pow

open scoped Classical in
-- With zero rows, the cylinder has no vertices and only the all-covered boundary contributes.
example (m : ℕ) :
    ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph m))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      (dominationTransferMatrix (cycleGraph m) ^ (0 : ℕ)) σ (allCoveredSignature _) = 1 := by
  rw [← dominationPolynomial_cylinder_eq_sum_transferMatrix_pow]
  have h : (default : Finset (Fin m × Fin 0)) = ∅ := rfl
  simp [dominationPolynomial, Finset.univ_unique, IsDominating, h]

open scoped Classical in
-- A cylinder whose rows have width zero has no vertices, whatever the number of rows.
example (n : ℕ) :
    ∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph 0))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      (dominationTransferMatrix (cycleGraph 0) ^ n) σ (allCoveredSignature _) = 1 := by
  rw [← dominationPolynomial_cylinder_eq_sum_transferMatrix_pow]
  have h : (default : Finset (Fin 0 × Fin n)) = ∅ := rfl
  simp [dominationPolynomial, Finset.univ_unique, IsDominating, h]

open scoped Classical in
-- The triangular prism `C₃ □ P₂` has 49 dominating sets meeting both triangles, and the two
-- triangles themselves.
example :
    (∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph 3))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      (dominationTransferMatrix (cycleGraph 3) ^ (2 : ℕ)) σ (allCoveredSignature _)).eval 1 =
        51 := by
  let (S : Finset (Fin 3 × Fin 2)) :
      Decidable ((cycleGraph 3 □ pathGraph 2).IsDominating (S : Set _)) := by
    simp only [IsDominating, Finset.mem_coe, boxProd_adj]
    infer_instance
  rw [← dominationPolynomial_cylinder_eq_sum_transferMatrix_pow, dominationPolynomial_eval_one]
  decide

#print axioms MetaMathlibExt.dominationPolynomial_cylinder_eq_sum_transferMatrix_pow
