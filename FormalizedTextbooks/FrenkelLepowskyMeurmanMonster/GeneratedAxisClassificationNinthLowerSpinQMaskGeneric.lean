/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.QCoordinateGenerators

/-! Exact full extraspecial action by finite bit masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The decoded columns, triangular cocycle matrix, and unit central bits bind the whole
actual extraspecial image from its twenty-four complete generator images. -/
theorem generatedNinth_lower_spin_q_mask_from_units (a : MulAut Q)
    (hR : ∀ v, squareQuad (qBinaryAction a v) = squareQuad v)
    (images : Fin 24 → Q) (cols rows : Fin 24 → ℕ) (coeff : ℕ)
    (hi : ∀ i, a (qCoordinateGenerator i) = images i)
    (hb : ∀ i, toAdd (images i).base = monsterCo1GeometryBinaryMaskDecode (cols i))
    (hr : ∀ i j, monsterCo1GeometryBinaryMaskDecode (rows i) j =
      if i < j then qBeta (monsterCo1GeometryBinaryMaskDecode (cols i))
        (monsterCo1GeometryBinaryMaskDecode (cols j)) +
        qBeta (Pi.single i 1) (Pi.single j 1) else 0)
    (hc : ∀ i, monsterCo1GeometryBinaryMaskDecode coeff i = toAdd (images i).coeff)
    (v : ℕ) : a (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage cols rows coeff v := by
  have hbase (i : Fin 24) : qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (cols i) := by
    have h := qBinaryAction_apply a (qCoordinateGenerator i)
    change qBinaryAction a (Pi.single i 1) = toAdd (a (qCoordinateGenerator i)).base at h
    rw [hi] at h
    exact h.trans (hb i)
  have hrows : qCorrectionMatrix (qBinaryAction a) =
      monsterCo1GeometryBinaryMaskMatrix rows := by
    ext i j
    change (if i < j then qCocycleDifference (qBinaryAction a)
      (Pi.single i 1) (Pi.single j 1) else 0) = _
    simp only [qCocycleDifference_apply, hbase]
    exact (hr i j).symm
  have hcoeff (i : Fin 24) : co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode coeff i := by
    change toAdd (a (qCoordinateGenerator i)).coeff = _
    rw [hi]
    exact (hc i).symm
  exact generatedAxisGlobalQMaskImage_actual a hR cols rows coeff hbase hrows hcoeff v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
