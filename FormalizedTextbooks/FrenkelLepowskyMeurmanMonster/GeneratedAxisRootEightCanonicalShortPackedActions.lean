/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortTransportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalPositiveFiber
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQMaskGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! The original full-Q canonical action determines every signed preferred-short image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
-- All triangular cocycle entries and every generator central bit retain their actual values.
/-- Original packed correction rows and coefficients represent the full canonical generator images. -/
theorem generatedRootEight_canonical_short_packed_metadata :
    (∀ i j, monsterCo1GeometryBinaryMaskDecode (generatedRootEightCanonicalShortPackedRows i) j =
      if i < j then qBeta (monsterCo1GeometryBinaryMaskDecode
        (generatedRootEightCompactBinaryColumns 12 i)) (monsterCo1GeometryBinaryMaskDecode
          (generatedRootEightCompactBinaryColumns 12 j)) + qBeta (Pi.single i 1) (Pi.single j 1)
      else 0) ∧
    (∀ i, monsterCo1GeometryBinaryMaskDecode generatedRootEightCanonicalShortPackedCoefficients i =
      toAdd (generatedRootEightCompactBasisImage 12 i).coeff) := by
  decide +kernel

/-- The complete canonical compact word acts on every original Q mask by the finite polynomial. -/
theorem generatedRootEight_canonical_short_packed_actual (v : ℕ) :
    spinConjugation generatedRootEightCanonicalPositiveFiber.val.1 (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedRootEightCompactBinaryColumns 12)
        generatedRootEightCanonicalShortPackedRows generatedRootEightCanonicalShortPackedCoefficients v := by
  have hs (w : Fin 24 → ZMod 2) :
      squareQuad (qBinaryAction (spinConjugation (generatedRootEightCompactSpin 12)) w) =
        squareQuad w := by
    change squareQuad (spinBinaryAction (generatedRootEightCompactSpin 12) w) = _
    rw [generatedRootEight_canonical_positive_compatibility]
    exact leechBinaryAction_squareQuad _ w
  apply generatedNinth_lower_spin_q_mask_from_units _ hs
    (generatedRootEightCompactBasisImage 12)
  · intro i
    rw [generatedRootEight_compact_conjugation]
    exact generatedRootEight_compact_q_basis_12 i
  · intro i
    rfl
  · exact generatedRootEight_canonical_short_packed_metadata.1
  · exact generatedRootEight_canonical_short_packed_metadata.2

/-- Every original short coordinate has its genuine preferred lift in the packed binary dictionary. -/
theorem generatedRootEight_canonical_short_mask_actual (r : GriessShortIndex) :
    generatedAxisGlobalQMask (generatedAxisGlobalShortMask r) = monsterNortonShortQ r := by
  rw [← generatedAxisGlobalShortMask_Q_actual,
    generatedAxisGlobalShortQFinite_actual, monsterNortonShortQ_eq]

/-- The two finite polynomial obligations for one original preferred-Q canonical image. -/
def generatedRootEightCanonicalShortPackedCondition (r : GriessShortIndex) : Prop :=
  generatedAxisGlobalQMaskVector (generatedRootEightCompactBinaryColumns 12)
      (generatedAxisGlobalShortMask r) =
    generatedAxisGlobalShortMask (generatedRootEightCanonicalShortDestination r) ∧
  (if (generatedAxisGlobalQMaskCentral generatedRootEightCanonicalShortPackedRows
    generatedRootEightCanonicalShortPackedCoefficients (generatedAxisGlobalShortMask r)).testBit 0
    then (1 : ZMod 2) else 0) = generatedRootEightCanonicalShortPhase r

/-- Every complete packed certificate gives the genuine original signed short image. -/
theorem generatedRootEight_canonical_short_image_of_packed (r : GriessShortIndex)
    (h : generatedRootEightCanonicalShortPackedCondition r) :
    spinConjugation generatedRootEightCanonicalPositiveFiber.val.1 (monsterNortonShortQ r) =
      qCentral (generatedRootEightCanonicalShortPhase r) *
        monsterNortonShortQ (generatedRootEightCanonicalShortDestination r) := by
  rw [← generatedRootEight_canonical_short_mask_actual r,
    ← generatedRootEight_canonical_short_mask_actual (generatedRootEightCanonicalShortDestination r),
    generatedRootEight_canonical_short_packed_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ h.1 h.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
