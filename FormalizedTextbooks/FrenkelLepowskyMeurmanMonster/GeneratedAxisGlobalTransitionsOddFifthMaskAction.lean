/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskEncode

/-! Complete actual extraspecial comparison actions from checked original binary cochains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine local comparison fiber preserves the original extraspecial square form. -/
theorem generatedAxisGlobalOddFifthMaskAction_square (k : Fin 2)
    (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1) v) = squareQuad v := by
  change squareQuad (spinBinaryAction (generatedAxisGlobalOddFifthComparisonFiber k).val.1 v) = _
  rw [(generatedAxisGlobalOddFifthComparisonFiber k).property]
  exact leechBinaryAction_squareQuad _ v

/-- Checked coordinate images give the complete actual polynomial vector and central action. -/
theorem generatedAxisGlobalOddFifthMaskAction_actual (k : Fin 2) (v : ℕ) :
    generatedAxisGlobalOddFifthQImage k (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalOddFifthQCacheBinary k)
        (generatedAxisGlobalOddFifthMaskRows k)
        (generatedAxisGlobalOddFifthMaskCoefficients k) v := by
  let a := spinConjugation (generatedAxisGlobalOddFifthComparisonFiber k).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalOddFifthQCache k i :=
    (generatedAxisGlobalOddFifthQImage_actual k _).trans
      (generatedAxisGlobalOddFifthQStageFinal_actual k i)
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddFifthQCacheBinary k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalOddFifthQCache_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalOddFifthMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalOddFifthMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalOddFifthMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi]
    exact (generatedAxisGlobalOddFifthMaskCoefficients_checked k i).symm
  rw [← generatedAxisGlobalOddFifthQImage_actual]
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalOddFifthMaskAction_square k) _ _ _ hb hr hc v

/-- Two complete finite bit identities certify the entire original preferred-Q comparison image. -/
theorem generatedAxisGlobalOddFifthMaskCheck_actual (k : Fin 2) (q r : Q) (c : ZMod 2)
    (hq : q.coeff = 1) (hr : r.coeff = 1)
    (hb : generatedAxisGlobalQMaskVector (generatedAxisGlobalOddFifthQCacheBinary k)
      (generatedAxisGlobalMaskEncode (toAdd q.base)) =
        generatedAxisGlobalMaskEncode (toAdd r.base))
    (hc : (if Nat.testBit
      (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddFifthMaskRows k)
        (generatedAxisGlobalOddFifthMaskCoefficients k)
        (generatedAxisGlobalMaskEncode (toAdd q.base))) 0 then (1 : ZMod 2) else 0) = c) :
    generatedAxisGlobalOddFifthQImage k q = qCentral c * r := by
  conv_lhs => rw [generatedAxisGlobalQMaskEncode_positive q hq]
  conv_rhs => rw [generatedAxisGlobalQMaskEncode_positive r hr]
  rw [generatedAxisGlobalOddFifthMaskAction_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hb hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
