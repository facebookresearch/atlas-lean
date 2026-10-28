/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonWords
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddNorm
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairingCriterion

/-! Literal genuine generated words for three full odd-axis comparison equalities. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Original forward root-zero, inverse root-zero and inverse root-six generated words. -/
def generatedAxisGlobalOddComparisonAction (k : Fin 3) : ↥G :=
  if k = 0 then extraIntoGenerated * localIntoGenerated (generatedAxisGlobalOddSourceRootLocalWord 0)
  else if k = 1 then extraIntoGenerated⁻¹ * localIntoGenerated (generatedAxisGlobalOddSourceRootLocalWord 0)
  else extraIntoGenerated⁻¹ * localIntoGenerated (generatedAxisGlobalOddSourceRootLocalWord 6)

/-- Every comparison starts with the literal genuine forward or inverse triality source image. -/
theorem generatedAxisGlobalOddComparisonAction_actual (k : Fin 3) :
    (generatedAxisGlobalOddComparisonAction k).val generatedOddAxis =
      if k = 0 then sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)
      else if k = 1 then sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 0) generatedOddAxis)
      else sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 6) generatedOddAxis) := by
  fin_cases k <;> rfl

/-- An exact complete pairing of 128 proves equality of the entire actual source vectors. -/
theorem generatedAxisGlobalOddComparison_eq_of_pairing (k : Fin 3)
    (hp : griessForm ((generatedAxisGlobalOddComparisonAction k).val generatedOddAxis)
      (rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis) = 128) :
    (generatedAxisGlobalOddComparisonAction k).val generatedOddAxis =
      rhoLocal (generatedAxisGlobalOddComparisonLocal k) generatedOddAxis := by
  apply generatedAxisGlobal_eq_of_preserved_pairing
    (generatedAxisGlobalOddComparisonAction k)
    (localIntoGenerated (generatedAxisGlobalOddComparisonLocal k)) generatedOddAxis
  rw [generatedAxisGlobalOdd_norm]
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
