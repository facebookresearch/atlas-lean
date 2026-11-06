/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSourceFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMatrixProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! Every physical matrix coefficient of the nine actual odd-family source root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original signed spatial source letters in the same complete product order. -/
def generatedAxisGlobalOddSourceSpatialLetter (l : Fin 10) : leechIsomSubgroup :=
  let k : Fin 5 := ⟨l.val / 2, by omega⟩
  if l.val % 2 = 1 then (omegaOrbitIsometry k)⁻¹ else omegaOrbitIsometry k

/-- Each genuine local source letter has this original spatial projection. -/
theorem generatedAxisGlobalOddSourceSpatialLetter_projection (l : Fin 10) :
    projH (generatedAxisGlobalOddSourceLocalLetter l) =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalOddSourceSpatialLetter l) := by
  by_cases h : l.val % 2 = 1
  · simp only [generatedAxisGlobalOddSourceLocalLetter, generatedAxisGlobalOddSourceSpatialLetter,
      h, ↓reduceIte, map_inv, generatedAxisGlobalOddSourceBaseLocal_projection]
  · simp only [generatedAxisGlobalOddSourceLocalLetter, generatedAxisGlobalOddSourceSpatialLetter,
      h, ↓reduceIte, generatedAxisGlobalOddSourceBaseLocal_projection]

/-- Original complete spatial product accompanying each genuine root word. -/
def generatedAxisGlobalOddSourceSpatialWord (k : Fin 9) : leechIsomSubgroup :=
  ((generatedAxisGlobalOddSourceRootWords k).map generatedAxisGlobalOddSourceSpatialLetter).prod

/-- The full phase-preserving local product has this genuine Conway spatial projection. -/
theorem generatedAxisGlobalOddSourceSpatialWord_projection (k : Fin 9) :
    projH (generatedAxisGlobalOddSourceRootLocalWord k) =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalOddSourceSpatialWord k) := by
  rw [generatedAxisGlobalOddSourceRootLocalWord, generatedAxisGlobalOddSourceSpatialWord,
    map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left (fun _ _ => generatedAxisGlobalOddSourceSpatialLetter_projection _)

/-- Exact original diagonal of the actual odd-axis matrix constituent. -/
def generatedAxisGlobalOddMatrixDiagonal (i : Fin 24) : ℝ :=
  1 / 4 + if i = 0 then 2 else 0

/-- Every actual root matrix output is the complete original spatial matrix action. -/
theorem generatedAxisGlobalOddSourceWord_matrix (k : Fin 9) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) generatedOddAxis)).1 =
      conwayMatrixAction (generatedAxisGlobalOddSourceSpatialWord k)
        (Matrix.diagonal generatedAxisGlobalOddMatrixDiagonal) := by
  rw [generatedAxisGlobalOddSourceRootFiber_encode, generatedAxisGlobalRaw_matrix_projection]
  change generatedAxisGlobalCo1MatrixAction
    (projH (localFiberIntoH (generatedAxisGlobalOddSourceRootFiber k))) _ = _
  rw [generatedAxisGlobalOddSourceRootFiber_local,
    generatedAxisGlobalOddSourceSpatialWord_projection]
  change generatedAxisGlobalCo1MatrixAction
    (QuotientGroup.mk (generatedAxisGlobalOddSourceSpatialWord k)) _ = _
  rw [generatedAxisGlobalCo1MatrixAction_mk, generatedOddAxis, generatedAxis_triality_odd_matrix]
  rfl

/-- Each actual physical matrix entry is an exact sum over the original 24 coordinates. -/
theorem generatedAxisGlobalOddSourceWord_matrix_entry (k : Fin 9) (i j : Fin 24) :
    (griessConwayEncode
      (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord k) generatedOddAxis)).1 i j =
      ∑ t : Fin 24, generatedAxisGlobalOddMatrixDiagonal t *
        (generatedAxisGlobalOddSourceSpatialWord k).val.symm (Pi.single i 1) t *
        (generatedAxisGlobalOddSourceSpatialWord k).val.symm (Pi.single j 1) t := by
  rw [generatedAxisGlobalOddSourceWord_matrix]
  let e := generatedAxisGlobalOddSourceSpatialWord k
  let A := Matrix.diagonal generatedAxisGlobalOddMatrixDiagonal
  calc
    _ = Matrix.toBilin' (conwayMatrixAction e A) (Pi.single i 1) (Pi.single j 1) :=
      (Matrix.toBilin'_single (conwayMatrixAction e A) i j).symm
    _ = Matrix.toBilin' A (e.val.symm (Pi.single i 1))
        (e.val.symm (Pi.single j 1)) := conwayMatrixAction_pairing e A _ _
    _ = _ := by
      simp only [A, Matrix.toBilin'_apply, Matrix.diagonal_apply]
      simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro t _
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
