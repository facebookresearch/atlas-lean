/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIsometryData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric

/-! Literal rational matrices construct genuine Leech lattice isometries
with their full orientation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact rational matrix is an actual whole oriented lattice isometry. -/
def generatedNinthLowerSpinDirectIsometry (i : Fin 11) : leechIsomSubgroup :=
  generatedTwelfthCertifiedMatrixIsometry
    (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i))
    (generatedNinthLowerSpinDirectIntegralMatrix i)
    (generatedNinthLowerSpinDirectIntegralInverse i)
    (generatedNinthLowerSpinTensorSpatialDenominator i)
    (generatedNinth_lower_spin_direct_integral_denominator i)
    (generatedNinth_lower_spin_direct_isometry_left i)
    (generatedNinth_lower_spin_direct_isometry_right i)
    (generatedNinth_lower_spin_direct_integral_basis i)
    (generatedNinth_lower_spin_direct_isometry_inverse i)

/-- The constructed isometry has every entry of the literal oriented physical matrix. -/
theorem generatedNinth_lower_spin_direct_isometry_matrix (i : Fin 11) :
    leechIsomMatrix (generatedNinthLowerSpinDirectIsometry i) =
      generatedTwelfthCertifiedRealMatrix
        (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i))
        (generatedNinthLowerSpinTensorSpatialDenominator i) :=
  generatedTwelfth_certified_isometry_matrix _ _ _ _ _ _ _ _ _

/-- Every original physical coordinate retains its exact numerator and denominator. -/
theorem generatedNinth_lower_spin_direct_isometry_numerator (i : Fin 11) :
    (generatedNinthLowerSpinTensorSpatialDenominator i : ℝ) •
      leechIsomMatrix (generatedNinthLowerSpinDirectIsometry i) =
        (Matrix.of (generatedNinthLowerSpinTensorSpatialNumerator i)).map
          (Int.castRingHom ℝ) :=
  generatedTwelfth_certified_isometry_numerator _ _ _ _ _ _ _ _ _

/-- The genuine isometry acts on all twenty-four binary coordinates by its integral basis matrix. -/
theorem generatedNinth_lower_spin_direct_isometry_binary (i : Fin 11)
    (v : Fin 24 → ZMod 2) :
    leechBinaryAction (generatedNinthLowerSpinDirectIsometry i) v =
      (leechHyperbolicInverse *
        (generatedNinthLowerSpinDirectIntegralMatrix i).map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *ᵥ v :=
  generatedTwelfth_certified_isometry_binary _ _ _ _ _ _ _ _ _ v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
