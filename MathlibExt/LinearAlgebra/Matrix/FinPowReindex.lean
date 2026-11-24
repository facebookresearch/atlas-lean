/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Power-successor reindexing for `Fin` and square matrices

`finPowSuccEquiv` specializes `finProdFinEquiv` through `Nat.pow_succ'`, giving
the one-step block decomposition used by recursive matrix constructions.
-/

set_option autoImplicit false

universe u

@[expose] public section

/-- Block reindexing of `Fin (q ^ (k + 1))` as `Fin q × Fin (q ^ k)` via `(i / q ^ k, i % q ^ k)`. -/
def finPowSuccEquiv (q k : ℕ) : Fin (q ^ (k + 1)) ≃ Fin q × Fin (q ^ k) :=
  (finCongr (by rw [Nat.pow_succ'])).trans finProdFinEquiv.symm

/-- Reindex both matrix indices along block reindexing. -/
def matrixFinPowSuccEquiv {F : Type u} (q k : ℕ) :
    Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F ≃
    Matrix (Fin q × Fin (q ^ k)) (Fin q × Fin (q ^ k)) F :=
  Matrix.reindex (finPowSuccEquiv q k) (finPowSuccEquiv q k)

/-- Value of a reindexed matrix at a pair of block indices. -/
theorem matrixFinPowSuccEquiv_apply {F : Type u} (q k : ℕ)
    (M : Matrix (Fin (q ^ (k + 1))) (Fin (q ^ (k + 1))) F)
    (i j : Fin q × Fin (q ^ k)) :
    (matrixFinPowSuccEquiv q k M) i j =
      M ((finPowSuccEquiv q k).symm i) ((finPowSuccEquiv q k).symm j) := by
  simp [matrixFinPowSuccEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

end
