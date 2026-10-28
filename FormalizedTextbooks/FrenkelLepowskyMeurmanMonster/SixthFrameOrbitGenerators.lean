/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitBinaryActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitAction

/-! Original spatial generator words and their genuine binary actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original fifteen spatial generators used by the checked frame parent tree. -/
def sixthFrameOrbitOriginalIsometry (k : Fin 15) : leechIsomSubgroup :=
  if h : k.val < 14 then sixthFrameOrbitMonomialIsometry (Fin.castAdd 2 ⟨k.val, h⟩)
  else (generatedSixthRawGenerator 4).val.2

/-- Their actual images in the Conway quotient by the two central signs. -/
def sixthFrameOrbitOriginalGenerator (k : Fin 15) : Co1 :=
  QuotientGroup.mk' signsSubgroup (sixthFrameOrbitOriginalIsometry k)

/-- The last original fiber has exactly the inverse-C, Xi, C spatial factor. -/
theorem sixthFrameOrbit_last_spatial :
    (generatedSixthRawGenerator 4).val.2 =
      sixthFrameOrbitMonomialIsometry 15 * co1XiIsometry *
        sixthFrameOrbitMonomialIsometry 14 := by
  rfl

/-- All fifteen packed matrices are the genuine binary actions of the original source words. -/
theorem sixthFrameOrbitOriginalGenerator_binary (k : Fin 15) (v : Fin 24 → ZMod 2) :
    co1BinaryAction (sixthFrameOrbitOriginalGenerator k) v =
      sixthFrameOrbitColumnMatrix (sixthFrameOrbitColumns k) *ᵥ v := by
  change leechBinaryAction (sixthFrameOrbitOriginalIsometry k) v = _
  by_cases h : k.val < 14
  · simp only [sixthFrameOrbitOriginalIsometry, h, dite_true]
    rw [sixthFrameOrbit_monomial_binary, sixthFrameOrbit_monomial_columns_check]
    rfl
  · have hk : k = 14 := by apply Fin.ext; omega
    subst k
    change leechBinaryAction (generatedSixthRawGenerator 4).val.2 v = _
    rw [sixthFrameOrbit_last_spatial, map_mul, map_mul]
    simp only [LinearEquiv.mul_apply]
    rw [sixthFrameOrbit_monomial_binary]
    have hxi (w : Fin 24 → ZMod 2) :
        leechBinaryAction co1XiIsometry w = omegaOrbitBinaryMatrices 0 *ᵥ w :=
      omegaOrbitIsometry_binary 0 w
    rw [hxi, sixthFrameOrbit_monomial_binary, sixthFrameOrbit_xi_columns_check]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
