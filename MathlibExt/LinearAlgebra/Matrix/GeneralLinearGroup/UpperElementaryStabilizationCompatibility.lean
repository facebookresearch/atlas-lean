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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSpecialLinear
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.SpecialLinearStabilization

/-!
# Upper-elementary / special-linear stabilization compatibility

Ring-generic compatibility between the already accepted upper-elementary
successor stabilization and the accepted special-linear successor
stabilization.  The proof descends to the existing `GL` coercion identities
`coe_stabilization`, `toGL_stabilization` and `toGL_toSLHom` and does not
redo matrix entry calculations.  No Bruhat or monomial-matrix material is
introduced in this file.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup.UpperElementary

variable {R : Type*} [CommRing R] {n : ℕ}

@[simp]
theorem toSLHom_stabilization (u : upperElementarySubgroup (Fin n) R) :
    toSLHom (stabilization R n u) =
      Matrix.SpecialLinearGroup.stabilization R (toSLHom u) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  calc Matrix.SpecialLinearGroup.toGL (toSLHom (stabilization R n u))
      = (stabilization R n u : Matrix.GeneralLinearGroup (Fin (n + 1)) R) := by
        rw [toGL_toSLHom]
    _ = Matrix.GeneralLinearGroup.stabilization R (u : Matrix.GeneralLinearGroup (Fin n) R) := by
        rw [coe_stabilization]
    _ = Matrix.GeneralLinearGroup.stabilization R
          (Matrix.SpecialLinearGroup.toGL (toSLHom u)) := by
        rw [toGL_toSLHom]
    _ = Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.stabilization R (toSLHom u)) := by
        rw [Matrix.SpecialLinearGroup.toGL_stabilization]

theorem toSLHom_comp_stabilization :
    (toSLHom (R := R) (ι := Fin (n + 1))).comp (stabilization R n) =
      (Matrix.SpecialLinearGroup.stabilization (R := R) (n := n)).comp
        (toSLHom (R := R) (ι := Fin n)) := by
  apply MonoidHom.ext
  intro u
  exact toSLHom_stabilization (R := R) (n := n) u

end Matrix.GeneralLinearGroup.UpperElementary
