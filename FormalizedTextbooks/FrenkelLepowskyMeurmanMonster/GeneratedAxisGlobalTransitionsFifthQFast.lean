/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCacheData

/-! Twenty-four verified coordinate images suffice for complete actual preferred-short transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A complete coordinate-normal-form evaluator, including its actual central correction. -/
def generatedAxisGlobalFifthQFast (k : Fin 14) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedAxisGlobalFifthQCache k) q

/-- Verified coordinate images bind this finite evaluator to the full genuine root-word Q action. -/
theorem generatedAxisGlobalFifthQFast_actual (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i) (q : Q) :
    generatedAxisGlobalFifthChainQImage k 7 q = generatedAxisGlobalFifthQFast k q := by
  rw [← generatedAxisGlobalFifthShortWord_QImage]
  apply monsterNortonCoordinateEvaluation_eq
  intro i
  rw [generatedAxisGlobalFifthShortWord_QImage]
  exact hk i

/-- A finite fast preferred-Q certificate determines the entire signed Griess short-unit image. -/
theorem generatedAxisGlobalFifthQFast_griess_basis (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalFifthQFast k (monsterNortonShortQ r) =
      qCentral c * monsterNortonShortQ s) :
    rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s (1 : ℝ), 0)) := by
  rw [← generatedAxisGlobalFifthShortWordFiber_local]
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [generatedAxisGlobalFifthShortWord_QImage, generatedAxisGlobalFifthQFast_actual k hk]
  exact hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
