/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.GridDominationTransfer

/-!
# Tests for grid and cylinder domination polynomials

Check empty rows, the three last-row states of a single vertex, and a one-row cylinder.
-/

open MetaMathlibExt DominationState Polynomial SimpleGraph
open scoped Classical

-- In a grid of width zero the empty set contributes the constant term.
example (n : ℕ) :
    ∑ σ ∈ (Finset.univ : Finset (DominationSignature (pathGraph 0))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      almostDominatingPolynomial (pathGraph 0) n σ.1 = 1 := by
  rw [← dominationPolynomial_grid_eq_sum_almostDominatingPolynomial]
  have h : (default : Finset (Fin 0 × Fin (n + 1))) = ∅ := rfl
  simp [dominationPolynomial, Finset.univ_unique, IsDominating, h]

-- In a one-vertex grid only the occupied state contributes to the domination polynomial.
-- The empty set contributes to the uncovered state of the almost dominating polynomial.
example (s : DominationState) :
    almostDominatingPolynomial (pathGraph 1) 0 (fun _ => s) =
      match s with
      | uncovered => 1
      | covered => 0
      | occupied => X := by
  have hsets : (Finset.univ : Finset (Finset (Fin 1 × Fin 1))) = {∅, Finset.univ} := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    obtain h | ⟨v, hv⟩ := S.eq_empty_or_nonempty
    · exact Or.inl h
    · exact Or.inr (Finset.eq_univ_of_forall fun w => Subsingleton.elim v w ▸ hv)
  have hne : (∅ : Finset (Fin 1 × Fin 1)) ≠ Finset.univ := Finset.univ_nonempty.ne_empty.symm
  cases s <;> simp [almostDominatingPolynomial, hsets, Finset.sum_filter, hne,
    vertexDominationState]

#print axioms MetaMathlibExt.dominationPolynomial_grid_eq_sum_almostDominatingPolynomial

-- In a one-row cylinder of width three, every nonempty vertex set dominates the triangle.
example :
    (∑ σ ∈ (Finset.univ : Finset (DominationSignature (cycleGraph 3))).filter
        (fun σ => ∀ i, σ.1 i ≠ uncovered),
      almostDominatingPolynomial (cycleGraph 3) 0 σ.1).eval 1 = 7 := by
  let (S : Finset (Fin 3 × Fin 1)) :
      Decidable ((cycleGraph 3 □ pathGraph 1).IsDominating (S : Set _)) := by
    simp only [IsDominating, Finset.mem_coe, boxProd_adj]
    infer_instance
  rw [← dominationPolynomial_cylinder_eq_sum_almostDominatingPolynomial,
    dominationPolynomial_eval_one]
  decide

#print axioms MetaMathlibExt.dominationPolynomial_cylinder_eq_sum_almostDominatingPolynomial
