/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.Semiseparable

open MetaMathlibExt.Matrix

example {K : Type*} [Field K] (T : ℕ) : IsSemiseparable (0 : Matrix (Fin T) (Fin T) K) 0 := by
  constructor
  · intro i j hij
    rfl
  · intro s
    simp

-- The rank bound alone does not make a matrix semiseparable: it must also be lower triangular.
example : ¬ IsSemiseparable (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) 2 := by
  intro h
  have hentry := h.1 (i := 0) (j := 1) (by decide)
  exact (by decide : (1 : ℚ) ≠ 0) hentry

-- Any selection of rows and columns within a single cut inherits that cut's bound.
example {K : Type*} [Field K] {T N p q : ℕ} {M : Matrix (Fin T) (Fin T) K}
    (h : IsSemiseparable M N) {s : Fin T} (r : Fin p → Set.Ici s) (c : Fin q → Set.Iic s) :
    (M.submatrix (fun i => (r i).val) (fun j => (c j).val)).rank ≤ N := by
  have hsub := Matrix.rank_submatrix_le
    (M.submatrix (Subtype.val : Set.Ici s → Fin T) (Subtype.val : Set.Iic s → Fin T)) r c
  exact hsub.trans (h.2 s)
