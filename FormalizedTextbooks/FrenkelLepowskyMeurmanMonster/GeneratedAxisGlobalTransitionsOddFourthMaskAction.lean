/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskEncode

/-! Complete actual extraspecial comparison actions from checked original binary cochains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine local comparison fiber preserves the original extraspecial square form. -/
theorem generatedAxisGlobalOddFourthMaskAction_square (k : Fin 4)
    (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1) v) = squareQuad v := by
  change squareQuad (spinBinaryAction (generatedAxisGlobalOddFourthComparisonFiber k).val.1 v) = _
  rw [(generatedAxisGlobalOddFourthComparisonFiber k).property]
  exact leechBinaryAction_squareQuad _ v

/-- Checked coordinate images give the complete actual polynomial vector and central action. -/
theorem generatedAxisGlobalOddFourthMaskAction_actual (k : Fin 4) (v : ℕ) :
    generatedAxisGlobalOddFourthQImage k (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalOddFourthQCacheBinary k)
        (generatedAxisGlobalOddFourthMaskRows k)
        (generatedAxisGlobalOddFourthMaskCoefficients k) v := by
  let a := spinConjugation (generatedAxisGlobalOddFourthComparisonFiber k).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalOddFourthQCache k i :=
    (generatedAxisGlobalOddFourthQImage_actual k _).trans
      (generatedAxisGlobalOddFourthQCache_certificate k i)
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFourthQCacheBinary k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalOddFourthQCache_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalOddFourthMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalOddFourthMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalOddFourthMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi]
    exact (generatedAxisGlobalOddFourthMaskCoefficients_checked k i).symm
  rw [← generatedAxisGlobalOddFourthQImage_actual]
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalOddFourthMaskAction_square k) _ _ _ hb hr hc v

/-- Two complete finite bit identities certify the entire original preferred-Q comparison image. -/
theorem generatedAxisGlobalOddFourthMaskCheck_actual (k : Fin 4) (q r : Q) (c : ZMod 2)
    (hq : q.coeff = 1) (hr : r.coeff = 1)
    (hb : generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFourthQCacheBinary k)
      (generatedAxisGlobalMaskEncode (toAdd q.base)) =
        generatedAxisGlobalMaskEncode (toAdd r.base))
    (hc : (if Nat.testBit
      (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFourthMaskRows k)
        (generatedAxisGlobalOddFourthMaskCoefficients k)
        (generatedAxisGlobalMaskEncode (toAdd q.base))) 0 then (1 : ZMod 2) else 0) = c) :
    generatedAxisGlobalOddFourthQImage k q = qCentral c * r := by
  conv_lhs => rw [generatedAxisGlobalQMaskEncode_positive q hq]
  conv_rhs => rw [generatedAxisGlobalQMaskEncode_positive r hr]
  rw [generatedAxisGlobalOddFourthMaskAction_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hb hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
