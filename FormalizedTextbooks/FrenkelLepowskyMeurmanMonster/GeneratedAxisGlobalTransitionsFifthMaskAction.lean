/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQFast

/-! The complete genuine fifth root-word Q action from its checked bit-cochain metadata. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual root fiber preserves the original extraspecial square form. -/
theorem generatedAxisGlobalFifthMaskAction_square (k : Fin 14) (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation (generatedAxisGlobalFifthShortWordFiber k).val.1) v) =
      squareQuad v := by
  change squareQuad (spinBinaryAction (generatedAxisGlobalFifthShortWordFiber k).val.1 v) = _
  rw [(generatedAxisGlobalFifthShortWordFiber k).property]
  exact leechBinaryAction_squareQuad _ v

/-- Actual checked unit images give the full genuine vector and central mask evaluator. -/
theorem generatedAxisGlobalFifthMaskAction_actual (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i) (v : ℕ) :
    spinConjugation (generatedAxisGlobalFifthShortWordFiber k).val.1
        (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalFifthQCacheBinary k)
        (generatedAxisGlobalFifthMaskRows k) (generatedAxisGlobalFifthMaskCoefficients k) v := by
  let a := spinConjugation (generatedAxisGlobalFifthShortWordFiber k).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i :=
    (generatedAxisGlobalFifthShortWord_QImage k _).trans (hk i)
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthQCacheBinary k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalFifthQCache_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalFifthMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalFifthMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalFifthMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi]
    exact (generatedAxisGlobalFifthMaskCoefficients_checked k i).symm
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalFifthMaskAction_square k) _ _ _ hb hr hc v

/-- The original complete Q evaluator agrees with the same proved polynomial mask evaluation. -/
theorem generatedAxisGlobalFifthQFast_mask (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i) (v : ℕ) :
    generatedAxisGlobalFifthQFast k (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalFifthQCacheBinary k)
        (generatedAxisGlobalFifthMaskRows k) (generatedAxisGlobalFifthMaskCoefficients k) v := by
  rw [← generatedAxisGlobalFifthQFast_actual k hk,
    ← generatedAxisGlobalFifthShortWord_QImage]
  exact generatedAxisGlobalFifthMaskAction_actual k hk v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
