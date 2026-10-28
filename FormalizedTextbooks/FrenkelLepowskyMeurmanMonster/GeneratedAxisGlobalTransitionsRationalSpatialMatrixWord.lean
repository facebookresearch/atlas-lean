/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSpatialWordFast

/-! Complete actual matrix transport by literal rational spatial words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every original spatial generator letter retains its genuine inverse letter. -/
def generatedAxisGlobalRationalSpatialInverseLetter : Fin 10 → Fin 10 :=
  ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8]

/-- The inverse spelling is the identical original spatial inverse. -/
theorem generatedAxisGlobalRationalSpatialInverseLetter_actual (l : Fin 10) :
    generatedAxisGlobalOddSourceSpatialLetter (generatedAxisGlobalRationalSpatialInverseLetter l) =
      (generatedAxisGlobalOddSourceSpatialLetter l)⁻¹ := by
  fin_cases l <;> simp [generatedAxisGlobalRationalSpatialInverseLetter,
    generatedAxisGlobalOddSourceSpatialLetter, inv_inv]

/-- Reverse the original word and invert every literal original spatial letter. -/
def generatedAxisGlobalRationalSpatialInverseWord (ls : List (Fin 10)) : List (Fin 10) :=
  ls.reverse.map generatedAxisGlobalRationalSpatialInverseLetter

/-- The recorded inverse word is exactly the genuine inverse of the complete spatial word. -/
theorem generatedAxisGlobalRationalSpatialInverseWord_actual (ls : List (Fin 10)) :
    ((generatedAxisGlobalRationalSpatialInverseWord ls).map
      generatedAxisGlobalOddSourceSpatialLetter).prod =
      ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)⁻¹ := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [generatedAxisGlobalRationalSpatialInverseWord, List.reverse_cons,
      List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [generatedAxisGlobalRationalSpatialInverseLetter_actual]
    change ((generatedAxisGlobalRationalSpatialInverseWord ls).map
      generatedAxisGlobalOddSourceSpatialLetter).prod *
      (generatedAxisGlobalOddSourceSpatialLetter l)⁻¹ = _
    rw [ih, mul_inv_rev]

/-- All physical inverse columns of the full genuine original spatial word. -/
def generatedAxisGlobalRationalSpatialInverseMatrix (ls : List (Fin 10))
    (i j : Fin 24) : ℚ :=
  generatedAxisGlobalRationalSpatialWordFast (generatedAxisGlobalRationalSpatialInverseWord ls)
    (Pi.single j 1) i

/-- Each complete rational inverse column is the full actual original inverse image. -/
theorem generatedAxisGlobalRationalSpatialInverseMatrix_actual (ls : List (Fin 10))
    (j : Fin 24) :
    (((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)⁻¹).val (Pi.single j 1) =
      fun i => (generatedAxisGlobalRationalSpatialInverseMatrix ls i j : ℝ) := by
  have h := generatedAxisGlobalRationalSpatialWordFast_actual
    (generatedAxisGlobalRationalSpatialInverseWord ls) (Pi.single j 1)
  rw [generatedAxisGlobalRationalSpatialInverseWord_actual] at h
  have he : (fun i => (((Pi.single j (1 : ℚ) : Fin 24 → ℚ) i : ℚ) : ℝ)) = Pi.single j (1 : ℝ) := by
    funext i
    by_cases hi : i = j <;> simp [hi]
  rw [he] at h
  exact h

/-- Every entry of the true rational matrix transport uses both complete original inverse columns. -/
def generatedAxisGlobalRationalSpatialMatrixWord (ls : List (Fin 10))
    (A : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℚ := fun i j =>
  ∑ u : Fin 24, ∑ v : Fin 24, A u v *
    generatedAxisGlobalRationalSpatialInverseMatrix ls u i *
      generatedAxisGlobalRationalSpatialInverseMatrix ls v j

/-- The whole rational matrix formula equals the complete original genuine spatial matrix action. -/
theorem generatedAxisGlobalRationalSpatialMatrixWord_actual (ls : List (Fin 10))
    (A : Matrix (Fin 24) (Fin 24) ℚ) :
    conwayMatrixAction ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)
      (A.map (Rat.castHom ℝ)) =
      (generatedAxisGlobalRationalSpatialMatrixWord ls A).map (Rat.castHom ℝ) := by
  ext i j
  rw [← Matrix.toBilin'_single
      (conwayMatrixAction ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)
        (A.map (Rat.castHom ℝ))) i j, conwayMatrixAction_pairing]
  change Matrix.toBilin' (A.map (Rat.castHom ℝ))
    ((((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)⁻¹).val (Pi.single i 1))
    ((((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)⁻¹).val (Pi.single j 1)) =
    (generatedAxisGlobalRationalSpatialMatrixWord ls A i j : ℝ)
  rw [generatedAxisGlobalRationalSpatialInverseMatrix_actual,
    generatedAxisGlobalRationalSpatialInverseMatrix_actual]
  simp only [Matrix.toBilin'_apply, generatedAxisGlobalRationalSpatialMatrixWord,
    Matrix.map_apply, Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change (generatedAxisGlobalRationalSpatialInverseMatrix ls u i : ℝ) * (A u v : ℝ) *
      (generatedAxisGlobalRationalSpatialInverseMatrix ls v j : ℝ) = _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
