/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQFast

/-! The complete genuine odd root-word Q action from its checked bit-cochain metadata. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual root fiber preserves the original extraspecial square form. -/
theorem generatedAxisGlobalOddRootMaskAction_square (k : Fin 9) (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction
      (spinConjugation (generatedAxisGlobalOddSourceRootFiber k).val.1) v) =
      squareQuad v := by
  change squareQuad (spinBinaryAction (generatedAxisGlobalOddSourceRootFiber k).val.1 v) = _
  rw [(generatedAxisGlobalOddSourceRootFiber k).property]
  exact leechBinaryAction_squareQuad _ v

/-- Actual checked unit images give the full genuine vector and central mask evaluator. -/
theorem generatedAxisGlobalOddRootMaskAction_actual (k : Fin 9)
    (hk : ∀ i, generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k)
      (qCoordinateGenerator i) =
      generatedAxisGlobalOddRootQCache k i) (v : ℕ) :
    spinConjugation (generatedAxisGlobalOddSourceRootFiber k).val.1
        (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalOddRootQCacheBinary k)
        (generatedAxisGlobalOddRootMaskRows k)
        (generatedAxisGlobalOddRootMaskCoefficients k) v := by
  let a := spinConjugation (generatedAxisGlobalOddSourceRootFiber k).val.1
  have hi (i : Fin 24) : a (qCoordinateGenerator i) =
      generatedAxisGlobalOddRootQCache k i :=
    (generatedAxisGlobalOddSourceFastRoot_actual k _).trans (hk i)
  have hb (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddRootQCacheBinary k i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (generatedAxisGlobalOddRootQCache_base k i)
  have hr : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix (generatedAxisGlobalOddRootMaskRows k) := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hb]
    exact (generatedAxisGlobalOddRootMaskRows_checked k i j).symm
  have hc (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalOddRootMaskCoefficients k) i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi]
    exact (generatedAxisGlobalOddRootMaskCoefficients_checked k i).symm
  exact generatedAxisGlobalQMaskImage_actual a
    (generatedAxisGlobalOddRootMaskAction_square k) _ _ _ hb hr hc v

/-- The original complete Q evaluator agrees with the same proved polynomial mask evaluation. -/
theorem generatedAxisGlobalOddRootQFast_mask (k : Fin 9)
    (hk : ∀ i, generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k)
      (qCoordinateGenerator i) =
      generatedAxisGlobalOddRootQCache k i) (v : ℕ) :
    generatedAxisGlobalOddRootQFast k (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalOddRootQCacheBinary k)
        (generatedAxisGlobalOddRootMaskRows k)
        (generatedAxisGlobalOddRootMaskCoefficients k) v := by
  rw [← generatedAxisGlobalOddRootQFast_actual k hk,
    ← generatedAxisGlobalOddSourceFastRoot_actual]
  exact generatedAxisGlobalOddRootMaskAction_actual k hk v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
