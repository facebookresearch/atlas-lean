/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalSpatialMatrixWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMatrixProjection

/-! The whole original local matrix action is the literal rational spatial word action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- All original fiber words project to precisely the corresponding original physical lattice words. -/
theorem generatedAxisGlobalRationalLocalWord_projection (ls : List (Fin 10)) :
    projH (localFiberIntoH ((ls.map generatedAxisGlobalOddSourceFiberLetter).prod)) =
      QuotientGroup.mk' signsSubgroup ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod) := by
  rw [map_list_prod, map_list_prod, map_list_prod]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  dsimp only [Function.comp_apply]
  rw [generatedAxisGlobalOddSourceFiberLetter_local]
  exact generatedAxisGlobalOddSourceSpatialLetter_projection l

/-- An original extraspecial correction has no physical matrix effect on the complete source word. -/
theorem generatedAxisGlobalRationalCorrectedLocalWord_projection (ls : List (Fin 10)) (q : Q) :
    projH (localFiberIntoH (localFiberIncl q * (ls.map generatedAxisGlobalOddSourceFiberLetter).prod)) =
      QuotientGroup.mk' signsSubgroup ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod) := by
  rw [map_mul, map_mul]
  change projH (inclQ q) * projH (localFiberIntoH
    ((ls.map generatedAxisGlobalOddSourceFiberLetter).prod)) = _
  rw [projH_inclQ, one_mul, generatedAxisGlobalRationalLocalWord_projection]

/-- Every original corrected local matrix coefficient is the full actual rational spatial-word coefficient. -/
theorem generatedAxisGlobalRationalLocalMatrixWord_actual (ls : List (Fin 10)) (q : Q)
    (x : GriessSpace) (A : Matrix (Fin 24) (Fin 24) ℚ)
    (hx : (griessConwayEncode x).1 = A.map (Rat.castHom ℝ)) :
    (griessConwayEncode (rhoLocal
      (localFiberIntoH (localFiberIncl q * (ls.map generatedAxisGlobalOddSourceFiberLetter).prod)) x)).1 =
      (generatedAxisGlobalRationalSpatialMatrixWord ls A).map (Rat.castHom ℝ) := by
  change (griessConwayEncode (localGriessRepresentation
    (localFiberIncl q * (ls.map generatedAxisGlobalOddSourceFiberLetter).prod) x)).1 = _
  rw [localGriessRepresentation_encode, generatedAxisGlobalRaw_matrix_projection]
  change generatedAxisGlobalCo1MatrixAction (projH (localFiberIntoH
    (localFiberIncl q * (ls.map generatedAxisGlobalOddSourceFiberLetter).prod)))
    (griessConwayEncode x).1 = _
  rw [generatedAxisGlobalRationalCorrectedLocalWord_projection]
  change conwayMatrixAction ((ls.map generatedAxisGlobalOddSourceSpatialLetter).prod)
    (griessConwayEncode x).1 = _
  rw [hx]
  exact generatedAxisGlobalRationalSpatialMatrixWord_actual ls A

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
