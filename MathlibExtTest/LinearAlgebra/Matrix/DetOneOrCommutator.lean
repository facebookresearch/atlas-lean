/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.DetOneOrCommutator

@[expose] public section

-- Consumer with the original binders.
example : ∀ g : GL (Fin 2) (ZMod 3),
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 →
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
        ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3),
          g = x * y * x⁻¹ * y⁻¹ :=
  fun g hg => Matrix.GeneralLinearGroup.eq_one_or_eq_commutator_of_det_eq_one g hg

-- The determinant hypothesis matters: the diagonal matrix `diag (2, 1)`,
-- whose determinant in `ZMod 3` is `2`, is neither the identity nor a
-- commutator (a commutator has determinant one).
example :
    let g : GL (Fin 2) (ZMod 3) :=
      ⟨!![2, 0; 0, 1], !![2, 0; 0, 1], by decide, by decide⟩
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 1 ∧
      ¬ ((g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 1 ∨
        ∃ x : GL (Fin 2) (ZMod 3), ∃ y : GL (Fin 2) (ZMod 3),
          g = x * y * x⁻¹ * y⁻¹) := by
  decide +kernel
