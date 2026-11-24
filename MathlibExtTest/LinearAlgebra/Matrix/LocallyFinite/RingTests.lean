/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.Ring
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Int.Basic

/-!
# Noncommutative coefficient and finite-ring clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe un uR uS

namespace Matrix.LocallyFinite.SourceClients.Ring

/-- The actual upper matrix unit in the noncommutative coefficient ring. -/
def upper : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]

/-- The actual lower matrix unit in the noncommutative coefficient ring. -/
def lower : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]

/-- The ordered outer matrix product retains the noncommutative coefficient product. -/
theorem ordered_coefficient_product :
    ((diagonal (fun _ : ℕ => upper)).comp (diagonal (fun _ => lower)) 0 0) 0 0 = 1 := by
  rw [diagonal_comp_apply]
  simp [diagonal_apply, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

/-- Reversing the original factors gives a different original coefficient. -/
theorem reversed_coefficient_product :
    ((diagonal (fun _ : ℕ => lower)).comp (diagonal (fun _ => upper)) 0 0) 0 0 = 0 := by
  rw [diagonal_comp_apply]
  simp [diagonal_apply, upper, lower, Matrix.mul_apply, Fin.sum_univ_two]

/-- The actual finite-index comparison preserves the original standard matrix product. -/
theorem finite_comparison_product {n : Type un} {R : Type uR} [Semiring R] [Fintype n]
    (A B : Matrix n n R) :
    ofMatrixRingEquiv (n := n) (R := R) (A * B) =
      ofMatrixRingEquiv (n := n) (R := R) A * ofMatrixRingEquiv (n := n) (R := R) B :=
  (ofMatrixRingEquiv (n := n) (R := R)).map_mul A B

/-- Independently sized coefficient worlds keep the original product map. -/
theorem independent_coefficient_map {n : Type un} {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) (A B : Matrix.LocallyFinite n n R) :
    mapRingHom f (A * B) = mapRingHom f A * mapRingHom f B := (mapRingHom f).map_mul A B

end Matrix.LocallyFinite.SourceClients.Ring

end
