/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.StateSpace.Coefficients

open ControlTheory Matrix

-- Matrix-built coefficients act by matrix-vector multiplication, and the
-- matrix view round-trips.
example (A : Matrix (Fin 2) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ)
    (C : Matrix (Fin 1) (Fin 2) ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (x : Fin 2 → ℝ) (u : Fin 1 → ℝ) :
    (StateSpaceCoeffs.ofMatrix A B C D).A x = A *ᵥ x ∧
      (StateSpaceCoeffs.ofMatrix A B C D).B u = B *ᵥ u ∧
      (StateSpaceCoeffs.ofMatrix A B C D).C x = C *ᵥ x ∧
      (StateSpaceCoeffs.ofMatrix A B C D).D u = D *ᵥ u ∧
      StateSpaceCoeffs.toMatrix (StateSpaceCoeffs.ofMatrix A B C D) = (A, B, C, D) :=
  ⟨StateSpaceCoeffs.ofMatrix_A_apply A B C D x,
    StateSpaceCoeffs.ofMatrix_B_apply A B C D u,
    StateSpaceCoeffs.ofMatrix_C_apply A B C D x,
    StateSpaceCoeffs.ofMatrix_D_apply A B C D u,
    StateSpaceCoeffs.toMatrix_ofMatrix A B C D⟩

-- Scalar SISO coefficients built from matrices agree with the matrix maps.
example (A : Matrix (Fin 1) (Fin 1) ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ)
    (C : Matrix (Fin 1) (Fin 1) ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (x u : Fin 1 → ℝ) :
    (StateSpaceCoeffs.ofMatrix A B C D).A x + (StateSpaceCoeffs.ofMatrix A B C D).B u
      = A *ᵥ x + B *ᵥ u := by
  rw [StateSpaceCoeffs.ofMatrix_A_apply, StateSpaceCoeffs.ofMatrix_B_apply]

-- The coefficient record itself does not require a complete scalar
-- field: it can be formed over `ℚ` from already-given continuous maps.
example : StateSpaceCoeffs ℚ ℚ ℚ ℚ :=
  ⟨0, 0, 0, 0⟩

-- Matrix extraction does not require decidable equality on the output
-- index type.
example {p : Type*} [Fintype p]
    (S : StateSpaceCoeffs ℝ (Fin 2 → ℝ) (Fin 1 → ℝ) (p → ℝ)) : True := by
  have h := StateSpaceCoeffs.toMatrix S
  trivial

-- Empty state, input, and output index types are allowed for the matrix
-- adapter.
example :
    StateSpaceCoeffs.toMatrix
        (StateSpaceCoeffs.ofMatrix (𝕜 := ℝ) (n := Fin 0) (m := Fin 0) (p := Fin 0)
          0 0 0 0)
      = (0, 0, 0, 0) :=
  StateSpaceCoeffs.toMatrix_ofMatrix 0 0 0 0

#print axioms StateSpaceCoeffs.ofMatrix_A_apply
#print axioms StateSpaceCoeffs.ofMatrix_B_apply
#print axioms StateSpaceCoeffs.ofMatrix_C_apply
#print axioms StateSpaceCoeffs.ofMatrix_D_apply
#print axioms StateSpaceCoeffs.toMatrix_ofMatrix
