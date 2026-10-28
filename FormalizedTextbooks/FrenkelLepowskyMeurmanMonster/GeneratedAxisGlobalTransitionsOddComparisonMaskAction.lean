/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonQCacheCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskEncode

/-! Complete actual extraspecial comparison actions from checked original binary cochains. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The genuine local comparison fiber preserves the original extraspecial square form. -/
theorem generatedAxisGlobalOddComparisonMaskAction_square (k : Fin 3)
    (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation (generatedAxisGlobalOddComparisonFiber k).val.1) v) = squareQuad v := by
  change squareQuad (spinBinaryAction (generatedAxisGlobalOddComparisonFiber k).val.1 v) = _
  rw [(generatedAxisGlobalOddComparisonFiber k).property]
  exact leechBinaryAction_squareQuad _ v

/-- Checked coordinate images give the complete actual polynomial vector and central action. -/
theorem generatedAxisGlobalOddComparisonMaskAction_actual (k : Fin 3) (v : ℕ) :
    generatedAxisGlobalOddComparisonQImage k (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalOddComparisonQCacheBinary k)
        (generatedAxisGlobalOddComparisonMaskRows k)
        (generatedAxisGlobalOddComparisonMaskCoefficients k) v := by
  let a := spinConjugation (generatedAxisGlobalOddComparisonFiber k).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalOddComparisonQCache k i :=
    (generatedAxisGlobalOddComparisonQImage_actual k _).trans
      (generatedAxisGlobalOddComparisonQCache_certificate k i)
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddComparisonQCacheBinary k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalOddComparisonQCache_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalOddComparisonMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalOddComparisonMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalOddComparisonMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi]
    exact (generatedAxisGlobalOddComparisonMaskCoefficients_checked k i).symm
  rw [← generatedAxisGlobalOddComparisonQImage_actual]
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalOddComparisonMaskAction_square k) _ _ _ hb hr hc v

/-- Two complete finite bit identities certify the entire original preferred-Q comparison image. -/
theorem generatedAxisGlobalOddComparisonMaskCheck_actual (k : Fin 3) (q r : Q) (c : ZMod 2)
    (hq : q.coeff = 1) (hr : r.coeff = 1)
    (hb : generatedAxisGlobalQMaskVector (generatedAxisGlobalOddComparisonQCacheBinary k)
      (generatedAxisGlobalMaskEncode (toAdd q.base)) =
        generatedAxisGlobalMaskEncode (toAdd r.base))
    (hc : (if Nat.testBit
      (generatedAxisGlobalQMaskCentral (generatedAxisGlobalOddComparisonMaskRows k)
        (generatedAxisGlobalOddComparisonMaskCoefficients k)
        (generatedAxisGlobalMaskEncode (toAdd q.base))) 0 then (1 : ZMod 2) else 0) = c) :
    generatedAxisGlobalOddComparisonQImage k q = qCentral c * r := by
  conv_lhs => rw [generatedAxisGlobalQMaskEncode_positive q hq]
  conv_rhs => rw [generatedAxisGlobalQMaskEncode_positive r hr]
  rw [generatedAxisGlobalOddComparisonMaskAction_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ hb hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
