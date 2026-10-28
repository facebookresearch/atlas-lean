/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7TwoLineSigns

/-! A genuine Golay-code right inverse for every even six-coordinate outside sign pattern. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000

/-- The six actual nonzero coordinates of the unsigned norm-twelve line. -/
def generatedTenthE7OutsideSignCoordinates : Fin 6 → Fin 24 := ![4, 7, 8, 11, 18, 20]

/-- Five original Golay coefficient labels giving an actual even-pattern basis. -/
def generatedTenthE7OutsideSignBasisLabels : Fin 5 → Fin 4096 := ![71, 74, 31, 28, 12]

/-- Every basis code is an actual original Golay encoder output. -/
def generatedTenthE7OutsideSignBasis (j : Fin 5) : golayCode :=
  ⟨golayEncoder (golayLabelCoefficients (generatedTenthE7OutsideSignBasisLabels j)), ⟨_, rfl⟩⟩

/-- All five actual source words give the desired complete outside and normal restrictions. -/
theorem generatedTenth_e7_outside_sign_basis_actual :
    (∀ j i : Fin 5, (generatedTenthE7OutsideSignBasis j).val
        (generatedTenthE7OutsideSignCoordinates (Fin.castAdd 1 i)) = if j = i then 1 else 0) ∧
      (∀ j : Fin 5, (generatedTenthE7OutsideSignBasis j).val
        (generatedTenthE7OutsideSignCoordinates 5) = 1) ∧
      (∀ j : Fin 5, (generatedTenthE7OutsideSignBasis j).val 16 =
        (generatedTenthE7OutsideSignBasis j).val 21) := by
  decide +kernel

/-- An arbitrary five-bit vector is lifted by an actual linear combination
of original Golay codes. -/
def generatedTenthE7OutsideSignLift (y : Fin 5 → ZMod 2) : golayCode :=
  ⟨∑ j : Fin 5, y j • (generatedTenthE7OutsideSignBasis j).val,
    Submodule.sum_mem golayCode (fun j _ =>
      Submodule.smul_mem golayCode (y j) (generatedTenthE7OutsideSignBasis j).property)⟩

/-- The lift attains every requested initial outside sign exactly. -/
theorem generatedTenth_e7_outside_sign_lift_initial (y : Fin 5 → ZMod 2) (i : Fin 5) :
    (generatedTenthE7OutsideSignLift y).val
      (generatedTenthE7OutsideSignCoordinates (Fin.castAdd 1 i)) = y i := by
  change (∑ j : Fin 5, y j * (generatedTenthE7OutsideSignBasis j).val
    (generatedTenthE7OutsideSignCoordinates (Fin.castAdd 1 i))) = y i
  simp_rw [generatedTenth_e7_outside_sign_basis_actual.1]
  simp

/-- The sixth coordinate is exactly the parity needed for an even outside pattern. -/
theorem generatedTenth_e7_outside_sign_lift_last (y : Fin 5 → ZMod 2) :
    (generatedTenthE7OutsideSignLift y).val (generatedTenthE7OutsideSignCoordinates 5) =
      ∑ j, y j := by
  change (∑ j : Fin 5, y j * (generatedTenthE7OutsideSignBasis j).val
    (generatedTenthE7OutsideSignCoordinates 5)) = ∑ j, y j
  simp_rw [generatedTenth_e7_outside_sign_basis_actual.2.1, mul_one]

/-- Every lifted outside pattern retains equality of the two actual normal signs. -/
theorem generatedTenth_e7_outside_sign_lift_normal (y : Fin 5 → ZMod 2) :
    (generatedTenthE7OutsideSignLift y).val 16 = (generatedTenthE7OutsideSignLift y).val 21 := by
  change (∑ j : Fin 5, y j * (generatedTenthE7OutsideSignBasis j).val 16) =
    ∑ j : Fin 5, y j * (generatedTenthE7OutsideSignBasis j).val 21
  apply Finset.sum_congr rfl
  intro j _
  rw [generatedTenth_e7_outside_sign_basis_actual.2.2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
