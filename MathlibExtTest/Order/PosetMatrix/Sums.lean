/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.PosetMatrix.Sums

/-!
# Tests for direct and ordinal sums of poset matrices
-/

namespace MetaMathlibExt.directSum_ordinalSum_represents

-- Two singletons give an antichain in the direct sum and a chain in the ordinal sum.
example : (∃ e : Fin 2 ≃ Fin 1 ⊕ Fin 1, ¬ e 0 ≤ e 1 ∧ ¬ e 1 ≤ e 0) ∧
    (∃ e : Fin 2 ≃ Fin 1 ⊕ₗ Fin 1, e 0 ≤ e 1 ∧ ¬ e 1 ≤ e 0) := by
  let A : Matrix (Fin 1) (Fin 1) Bool := fun _ _ => true
  have hA : IsPosetMatrix 1 A := by
    unfold IsPosetMatrix A
    decide
  let e := Equiv.refl (Fin 1)
  have he (i j : Fin 1) : e i ≤ e j ↔ A i j = true := by simp [e, A, Fin.fin_one_eq_zero]
  obtain ⟨⟨_, d, hd⟩, ⟨_, o, ho⟩⟩ := directSum_ordinalSum_represents 1 1 A A hA hA e he e he
  refine ⟨⟨d, ?_⟩, ⟨o, ?_⟩⟩
  · rw [hd, hd]
    decide
  · rw [ho, ho]
    decide

-- With an empty left summand the ordinal sum represents exactly the right block.
example {k : ℕ} (B : Matrix (Fin k) (Fin k) Bool) (hB : IsPosetMatrix k B)
    {Q : Type*} [PartialOrder Q] (eB : Fin k ≃ Q) (heB : ∀ i j, eB i ≤ eB j ↔ B i j = true) :
    ∃ e : Fin (0 + k) ≃ Fin 0 ⊕ₗ Q, ∀ i j : Fin k,
      e (i.natAdd 0) ≤ e (j.natAdd 0) ↔ B i j = true := by
  let A : Matrix (Fin 0) (Fin 0) Bool := fun i => i.elim0
  have hA : IsPosetMatrix 0 A := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  obtain ⟨e, he⟩ := (directSum_ordinalSum_represents 0 k A B hA hB (Equiv.refl _)
    (fun i => i.elim0) eB heB).2.2
  refine ⟨e, fun i j => ?_⟩
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₂₂] using he (i.natAdd 0) (j.natAdd 0)

end MetaMathlibExt.directSum_ordinalSum_represents
