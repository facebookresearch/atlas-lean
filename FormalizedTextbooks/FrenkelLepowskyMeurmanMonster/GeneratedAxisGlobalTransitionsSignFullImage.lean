/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignHighImage
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignShort

/-! A single complete extraspecial and preferred-short evaluator for every actual source sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual phase-correct Q image for all 4096 unshifted original source signs. -/
def generatedAxisGlobalSignFullImage (a : Fin 4096) (q : Q) : Q :=
  if h : a.val < 2048 then generatedAxisGlobalSignSpinImage ⟨a.val, h⟩ q
  else generatedAxisGlobalSignHighImage ⟨a.val - 2048, by omega⟩ q

/-- The single explicit evaluator equals genuine source fiber conjugation on every Q element. -/
theorem generatedAxisGlobalSignFull_QImage (a : Fin 4096) (q : Q) :
    spinConjugation (generatedFifthSignFiber a 0).val.1 q =
      generatedAxisGlobalSignFullImage a q := by
  by_cases ha : a.val < 2048
  · let b : Fin 2048 := ⟨a.val, ha⟩
    have hb : generatedAxisGlobalSignLowCode b = a := by apply Fin.ext; rfl
    rw [← hb, generatedAxisGlobalSignLow_QImage]
    simp only [generatedAxisGlobalSignFullImage, hb, ha, ↓reduceDIte]
    rfl
  · let b : Fin 2048 := ⟨a.val - 2048, by omega⟩
    have hb : generatedAxisGlobalCodeHighLabel b = a := by
      apply Fin.ext
      change a.val - 2048 + 2048 = a.val
      omega
    rw [← hb, generatedAxisGlobalSignHigh_QImage]
    simp only [generatedAxisGlobalSignFullImage, hb, ha, ↓reduceDIte]
    rfl

/-- Every actual preferred short phase is now a finite full-label extraspecial coefficient. -/
theorem generatedAxisGlobalSignFull_short_phase (a : Fin 4096) (r : GriessShortIndex) :
    localShortPhase (generatedFifthSignFiber a 0) r =
      Multiplicative.toAdd (generatedAxisGlobalSignFullImage a (griessShortQ r)).coeff := by
  unfold localShortPhase
  rw [generatedAxisGlobalSignFull_QImage]

/-- A finite complete Q certificate gives the entire actual source-sign short-unit image. -/
theorem generatedAxisGlobalSignFull_short_basis (a : Fin 4096)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalSignFullImage a (griessShortQ r) =
      qCentral c * griessShortQ s) :
    (sourceGeneratedY a 0).val (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s (1 : ℝ), 0)) := by
  rw [← generatedFifth_sign_local_generated, ← generatedFifth_sign_fiber_local]
  change localGriessRepresentation (generatedFifthSignFiber a 0) _ = _
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, generatedAxisGlobalSignFull_QImage]
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
