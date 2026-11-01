/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingCertifiedMatrixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixActionGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinCompactOriented
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates

/-! Complete actual candidate lattice and spin binary actions agree with the original source. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The complete incoming rational matrix is an actual Leech lattice isometry. -/
def generatedTwelfthIncomingCertifiedSpatial : leechIsomSubgroup :=
  generatedTwelfthCertifiedMatrixIsometry
    generatedTwelfthIncomingCertifiedNumerator generatedTwelfthIncomingCertifiedIntegral
    generatedTwelfthIncomingCertifiedIntegralInverse 4 (by decide)
    generatedTwelfth_incoming_certified_orthogonal_left
    generatedTwelfth_incoming_certified_orthogonal_right
    generatedTwelfth_incoming_certified_basis generatedTwelfth_incoming_certified_integral_inverse

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Compare every complete original binary column after the integral basis change.
/-- Every actual lattice binary column is the checked original source column. -/
theorem generatedTwelfth_incoming_certified_binary_certificate : ∀ j : Fin 24,
    (leechHyperbolicInverse *
      generatedTwelfthIncomingCertifiedIntegral.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ
          monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val) =
      toAdd (qQuotHom (generatedAxisGlobalFifthQCache 9 j)) := by
  decide +kernel

/-- The explicitly oriented spin candidate retains every original binary column. -/
theorem generatedTwelfth_incoming_compact_binary_generator (j : Fin 24) :
    spinBinaryAction (generatedTwelfthIncomingSpinCompactOriented 0)
        (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
      toAdd (qQuotHom (generatedAxisGlobalFifthQCache 9 j)) := by
  rw [generatedTwelfth_spin_compact_binary_basis]
  change qBinaryAction (spinConjugation (generatedTwelfthIncomingSpinCompactOriented 0))
    (toAdd (qQuotHom (qCoordinateGenerator j))) = _
  rw [qBinaryAction_apply, generatedTwelfth_incoming_spin_compact_oriented_conjugation,
    ← generatedTwelfth_incoming_spin_compact_source_Q,
    generatedTwelfth_incoming_spin_compact_conjugation,
    generatedTwelfth_incoming_spin_compact_source_certificate]

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24,
      e (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        f (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply, generatedTwelfth_spin_compact_binary_basis] using h j

/-- The complete actual candidate spin and lattice actions define a genuine local fiber. -/
theorem generatedTwelfth_incoming_certified_compatibility :
    spinBinaryAction (generatedTwelfthIncomingSpinCompactOriented 0) =
      leechBinaryAction generatedTwelfthIncomingCertifiedSpatial := by
  apply binary_equiv_eq_of_columns
  intro j
  rw [generatedTwelfth_incoming_compact_binary_generator]
  change _ = leechBinaryAction (generatedTwelfthCertifiedMatrixIsometry
    generatedTwelfthIncomingCertifiedNumerator generatedTwelfthIncomingCertifiedIntegral
    generatedTwelfthIncomingCertifiedIntegralInverse 4 (by decide)
    generatedTwelfth_incoming_certified_orthogonal_left
    generatedTwelfth_incoming_certified_orthogonal_right
    generatedTwelfth_incoming_certified_basis
    generatedTwelfth_incoming_certified_integral_inverse) _
  rw [generatedTwelfth_certified_isometry_binary,
    generatedTwelfth_incoming_certified_binary_certificate]

/-- The fully certified incoming candidate is an element of the defining local fiber product. -/
def generatedTwelfthIncomingCertifiedFiber : localFiberSubgroup :=
  ⟨(generatedTwelfthIncomingSpinCompactOriented 0, generatedTwelfthIncomingCertifiedSpatial),
    generatedTwelfth_incoming_certified_compatibility⟩

/-- The candidate's complete physical matrix has precisely the original numerator and denominator. -/
theorem generatedTwelfth_incoming_certified_spatial_matrix :
    leechIsomMatrix generatedTwelfthIncomingCertifiedSpatial =
      generatedTwelfthCertifiedRealMatrix generatedTwelfthIncomingCertifiedNumerator 4 :=
  generatedTwelfth_certified_isometry_matrix _ _ _ _ _ _ _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
