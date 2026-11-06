/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialSignSpatial

/-! Original binary certificates for all equal-sign Golay coefficients on the sixth root triple. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The two remaining root coordinates, compared to sixteen. -/
def generatedSixthSignConstraintCoordinates : Fin 2 → Fin 24 := ![17, 19]

/-- The exact two original Golay bit-difference equations. -/
def generatedSixthSignConstraintMatrix : Matrix (Fin 2) (Fin 12) (ZMod 2) :=
  fun j i => (golayGeneratorBit i 16 : ZMod 2) +
    (golayGeneratorBit i (generatedSixthSignConstraintCoordinates j) : ZMod 2)

/-- The ten literal source-code coefficient columns. -/
def generatedSixthSignBasisMatrix : Matrix (Fin 12) (Fin 10) (ZMod 2) :=
  fun i j => golayLabelCoefficients (generatedSixthMonomialSignCode j) i

/-- The free original coefficient indices in this actual code kernel. -/
def generatedSixthSignFreeCoordinates : Fin 10 → Fin 12 := ![0, 1, 2, 3, 6, 7, 8, 9, 10, 11]

/-- A checked left inverse selecting the original free coefficients. -/
def generatedSixthSignBasisLeftInverse : Matrix (Fin 10) (Fin 12) (ZMod 2) :=
  fun j i => if i = generatedSixthSignFreeCoordinates j then 1 else 0

/-- An exact complement to the actual ten-dimensional coefficient kernel. -/
def generatedSixthSignBasisComplement : Matrix (Fin 12) (Fin 2) (ZMod 2) :=
  fun i j => golayLabelCoefficients (![48, 16] j) i

/-- The ten source-code columns are independent in the genuine original coefficient module. -/
theorem generatedSixth_sign_basis_left_inverse :
    generatedSixthSignBasisLeftInverse * generatedSixthSignBasisMatrix = 1 := by
  decide +kernel

/-- Every source-code column satisfies the original equal-sign equations. -/
theorem generatedSixth_sign_basis_constraint :
    generatedSixthSignConstraintMatrix * generatedSixthSignBasisMatrix = 0 := by
  decide +kernel

/-- The literal coefficient projection and two-equation complement sum to the identity. -/
theorem generatedSixth_sign_basis_projection :
    generatedSixthSignBasisMatrix * generatedSixthSignBasisLeftInverse +
      generatedSixthSignBasisComplement * generatedSixthSignConstraintMatrix = 1 := by
  decide +kernel

/-- Matrix constraints are the two original coordinate-bit differences in the Golay encoder. -/
theorem generatedSixth_sign_constraint_encoder (t : Fin 12 → ZMod 2) (j : Fin 2) :
    (generatedSixthSignConstraintMatrix *ᵥ t) j =
      golayEncoder t 16 + golayEncoder t (generatedSixthSignConstraintCoordinates j) := by
  change (∑ i, ((golayGeneratorBit i 16 : ZMod 2) +
    (golayGeneratorBit i (generatedSixthSignConstraintCoordinates j) : ZMod 2)) * t i) = _
  simp only [add_mul, Finset.sum_add_distrib]
  change (∑ i, (golayGeneratorBit i 16 : ZMod 2) * t i) +
    (∑ i, (golayGeneratorBit i (generatedSixthSignConstraintCoordinates j) : ZMod 2) * t i) =
    (∑ i, t i * (golayGeneratorBit i 16 : ZMod 2)) +
    (∑ i, t i * (golayGeneratorBit i (generatedSixthSignConstraintCoordinates j) : ZMod 2))
  simp only [mul_comm]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
