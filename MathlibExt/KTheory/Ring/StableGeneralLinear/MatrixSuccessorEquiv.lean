/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.MatrixDiagram

/-!
# Successor-index equivalences for matrix flattening

For a finite index type `ι : Type u` with `[Fintype ι]`,
this file provides the one-step successor equivalences
`(Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n+1) * card ι)` in the finite-index
universe `u`.

* `blockSuccEquiv` is block-indexed: flatten each summand separately via
  `finProdMatrixEquiv` (`Fin n × ι ≃ Fin (n*card)`, `Fin 1 × ι ≃ Fin card`
  via `oneMulFinCongr`), sum them with `finSumFinEquiv`, then collapse
  `Fin (n*card+card)` to `Fin ((n+1)*card)` via `castSuccMul`. Successor
  index `n` orients as trailing `card ι` block after outer `Fin n`.

* `prodSuccEquiv` is product-decomposition: first
  `finSuccProdDecomp : Fin (n+1) × ι ≃ (Fin n × ι) ⊕ (Fin 1 × ι)` distributing
  `Fin (n+1) ≃ Fin n ⊕ Fin 1`, then `finProdMatrixEquiv (n+1)` flattens.
  Same successor-index `n` and flattening orientation (outer `Fin` slowest,
  `ι` via noncanonical `equivFinMatrix`).

No ring universe is involved; the same universe is used by the current
diagram API. The equality lemma shows both orientations agree.

Public API preserved for downstream stabilization square:
`blockSuccEquiv`, `prodSuccEquiv`, `blockSuccEquiv_eq_prodSuccEquiv`.
-/

@[expose] public section

universe u

namespace AlgebraicKTheory
namespace MatrixDiagram

variable {ι : Type u} [Fintype ι]

/-- Block-indexed successor equivalence
`(Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n+1) * card ι)`.

Successor-index `n` adds a trailing `card ι` block; flattening orients outer
`Fin n` slowest (`finProdMatrixEquiv_val`) and `ι` via noncanonical
`equivFinMatrix`. Built as `(finProdMatrixEquiv n ⊕ (finProdMatrixEquiv 1 ≫
oneMulFinCongr)) ≫ finSumFinEquiv ≫ castSuccMul`. -/
noncomputable def blockSuccEquiv (n : ℕ) :
    (Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n + 1) * Fintype.card ι) :=
  ((finProdMatrixEquiv (ι := ι) n).sumCongr
    ((finProdMatrixEquiv (ι := ι) 1).trans (oneMulFinCongr (Fintype.card ι)))).trans
    (finSumFinEquiv.trans (castSuccMul (ι := ι) n))

/-- Product-decomposition successor equivalence
`(Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n+1) * card ι)`.

Same successor-index `n` and flattening orientation as `blockSuccEquiv`
(outer `Fin (n+1)` slowest, trailing block for successor), oriented as
`finSuccProdDecomp` distributing successor first, then
`finProdMatrixEquiv (n+1)` flattening. -/
noncomputable def prodSuccEquiv (n : ℕ) :
    (Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n + 1) * Fintype.card ι) :=
  (finSuccProdDecomp (ι := ι) n).symm.trans (finProdMatrixEquiv (ι := ι) (n + 1))

private lemma fin1_val_zero (b : Fin 1) : b.val = 0 := by
  have : b = 0 := Subsingleton.elim b 0
  subst this
  rfl

private lemma blockSuccEquiv_inl_val (n : ℕ) (a : Fin n) (x : ι) :
    (blockSuccEquiv (ι := ι) n (Sum.inl (a, x))).val =
      (equivFinMatrix (ι := ι) x).val + Fintype.card ι * a.val := by
  simp only [blockSuccEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, castSuccMul, oneMulFinCongr, finCongr_apply_coe,
    Fin.val_castAdd, finProdMatrixEquiv_val]

private lemma blockSuccEquiv_inr_val (n : ℕ) (b : Fin 1) (x : ι) :
    (blockSuccEquiv (ι := ι) n (Sum.inr (b, x))).val =
      n * Fintype.card ι + ((equivFinMatrix (ι := ι) x).val + Fintype.card ι * b.val) := by
  simp only [blockSuccEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, castSuccMul, oneMulFinCongr, finCongr_apply_coe,
    Fin.val_natAdd, finProdMatrixEquiv_val]

private lemma prodSuccEquiv_inl_val (n : ℕ) (a : Fin n) (x : ι) :
    (prodSuccEquiv (ι := ι) n (Sum.inl (a, x))).val =
      (equivFinMatrix (ι := ι) x).val + Fintype.card ι * a.val := by
  simp only [prodSuccEquiv, Equiv.trans_apply, finSuccProdDecomp_symm_apply_inl,
    finProdMatrixEquiv_val, Fin.val_castAdd]

private lemma prodSuccEquiv_inr_val (n : ℕ) (b : Fin 1) (x : ι) :
    (prodSuccEquiv (ι := ι) n (Sum.inr (b, x))).val =
      (equivFinMatrix (ι := ι) x).val + Fintype.card ι * (n + b.val) := by
  simp only [prodSuccEquiv, Equiv.trans_apply, finSuccProdDecomp_symm_apply_inr,
    finProdMatrixEquiv_val, Fin.val_natAdd]

/-- Equality of the two successor-index orientations: block-indexed
`blockSuccEquiv` and product-decomposition `prodSuccEquiv` agree as
`(Fin n × ι) ⊕ (Fin 1 × ι) ≃ Fin ((n+1) * card ι)`, both with outer `Fin`
slowest flattening and trailing `card ι` block for successor index `n`. -/
theorem blockSuccEquiv_eq_prodSuccEquiv (n : ℕ) :
    blockSuccEquiv (ι := ι) n = prodSuccEquiv (ι := ι) n := by
  ext p
  · cases p with
    | inl q =>
      obtain ⟨a, x⟩ := q
      rw [blockSuccEquiv_inl_val, prodSuccEquiv_inl_val]
    | inr q =>
      obtain ⟨b, x⟩ := q
      rw [blockSuccEquiv_inr_val, prodSuccEquiv_inr_val, fin1_val_zero b]
      simp only [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
      calc n * Fintype.card ι + (equivFinMatrix x).val
          = (equivFinMatrix x).val + n * Fintype.card ι := Nat.add_comm _ _
        _ = (equivFinMatrix x).val + Fintype.card ι * n := by
            rw [Nat.mul_comm n (Fintype.card ι)]

end MatrixDiagram
end AlgebraicKTheory

end
