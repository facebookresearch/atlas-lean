/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.TorusDominationTransfer

/-!
# Tests for the torus domination polynomial

Check the trace formula on a single vertex, a two-row torus and an empty torus.
-/

open MetaMathlibExt Polynomial SimpleGraph

-- The only dominating set of a one-vertex torus is its singleton.
example : Matrix.trace (dominationTransferMatrix (cycleGraph 1) ^ (1 : ℕ)) = X := by
  rw [← dominationPolynomial_torus_eq_trace_transferMatrix_pow 1 1 (hn := by decide)]
  classical
  have hsets : (Finset.univ : Finset (Finset (Fin 1 × Fin 1))) = {∅, Finset.univ} := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    obtain h | ⟨v, hv⟩ := S.eq_empty_or_nonempty
    · exact Or.inl h
    · exact Or.inr (Finset.eq_univ_of_forall fun w => Subsingleton.elim v w ▸ hv)
  have hne : (∅ : Finset (Fin 1 × Fin 1)) ≠ Finset.univ := Finset.univ_nonempty.ne_empty.symm
  simp [dominationPolynomial, hsets, Finset.sum_filter, hne, IsDominating]

-- The two-by-two torus is a four-cycle, with eleven dominating sets.
example : (Matrix.trace (dominationTransferMatrix (cycleGraph 2) ^ (2 : ℕ))).eval 1 = 11 := by
  let (S : Finset (Fin 2 × Fin 2)) :
      Decidable ((cycleGraph 2 □ cycleGraph 2).IsDominating (S : Set _)) := by
    simp only [IsDominating, Finset.mem_coe, boxProd_adj]
    infer_instance
  rw [← dominationPolynomial_torus_eq_trace_transferMatrix_pow 2 2 (hn := by decide),
    dominationPolynomial_eval_one]
  decide

-- An empty torus has precisely the empty dominating set.
example (n : ℕ) :
    Matrix.trace (dominationTransferMatrix (cycleGraph 0) ^ (n + 1)) = 1 := by
  rw [← dominationPolynomial_torus_eq_trace_transferMatrix_pow 0 (n + 1) (hn := by omega)]
  classical
  have h : (default : Finset (Fin 0 × Fin (n + 1))) = ∅ := rfl
  simp [dominationPolynomial, Finset.univ_unique, IsDominating, h]

#print axioms MetaMathlibExt.dominationPolynomial_torus_eq_trace_transferMatrix_pow
