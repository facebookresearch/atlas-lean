/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSpatialMatrixWord

/-! Whole original rational matrix word action with proven zero-coefficient guards. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- The complete original matrix action evaluates source coefficients only at genuine nonzero inverse columns. -/
def generatedAxisGlobalRationalSpatialMatrixWordSparse (ls : List (Fin 10))
    (A : Matrix (Fin 24) (Fin 24) ℚ) (i j : Fin 24) : ℚ :=
  ∑ u : Fin 24, if generatedAxisGlobalRationalSpatialInverseMatrix ls u i = 0 then 0 else
    ∑ v : Fin 24, if generatedAxisGlobalRationalSpatialInverseMatrix ls v j = 0 then 0 else
      A u v * generatedAxisGlobalRationalSpatialInverseMatrix ls u i *
        generatedAxisGlobalRationalSpatialInverseMatrix ls v j

/-- Every guarded coefficient equals the complete original rational matrix action. -/
theorem generatedAxisGlobalRationalSpatialMatrixWordSparse_eq (ls : List (Fin 10))
    (A : Matrix (Fin 24) (Fin 24) ℚ) :
    generatedAxisGlobalRationalSpatialMatrixWordSparse ls A =
      generatedAxisGlobalRationalSpatialMatrixWord ls A := by
  funext i j
  unfold generatedAxisGlobalRationalSpatialMatrixWordSparse generatedAxisGlobalRationalSpatialMatrixWord
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : generatedAxisGlobalRationalSpatialInverseMatrix ls u i = 0
  · simp only [h, ↓reduceIte, mul_zero, zero_mul, Finset.sum_const_zero]
  · rw [ite_eq_right h]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : generatedAxisGlobalRationalSpatialInverseMatrix ls v j = 0
    · simp only [hv, ↓reduceIte, mul_zero]
    · rw [ite_eq_right hv]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
