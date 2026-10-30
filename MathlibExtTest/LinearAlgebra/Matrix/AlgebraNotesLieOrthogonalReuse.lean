/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical matrix commutator and special-unitary/orthogonal carriers.
No caller-defined Lie predicate or group-simplicity theorem is introduced.
-/

namespace AlgebraNotesApiProbe

private theorem matrix_commutator (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    ⁅A, B⁆ = A * B - B * A := Ring.lie_def A B

private theorem special_unitary_membership (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔
      A ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ A.det = 1 :=
  Matrix.mem_specialUnitaryGroup_iff

-- The stock carriers already provide the group structures.
example : Group (Matrix.specialUnitaryGroup (Fin 2) ℂ) := inferInstance
example : Group (Matrix.orthogonalGroup (Fin 2) ℝ) := inferInstance
example : Group (Matrix.specialOrthogonalGroup (Fin 2) ℝ) := inferInstance

#print axioms matrix_commutator
#print axioms special_unitary_membership

end AlgebraNotesApiProbe
