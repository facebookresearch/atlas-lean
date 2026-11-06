/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQImage

/-! Actual full signed short transport by the fourteen genuine source root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The full original root word has an executable preferred-short phase on every actual label. -/
theorem generatedAxisGlobalFifthShortWord_short_phase (k : Fin 14) (r : GriessShortIndex) :
    localShortPhase (generatedAxisGlobalFifthShortWordFiber k) r =
      toAdd (generatedAxisGlobalFifthChainQImage k 7 (griessShortQ r)).coeff := by
  unfold localShortPhase
  rw [generatedAxisGlobalFifthShortWord_QImage]

/-- A finite complete Q certificate gives the whole signed short-unit root-word image. -/
theorem generatedAxisGlobalFifthShortWord_short_basis (k : Fin 14)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalFifthChainQImage k 7 (griessShortQ r) =
      qCentral c * griessShortQ s) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber k) (Pi.single r 1) =
      qSign c • Pi.single s (1 : ℝ) := by
  apply monsterNortonShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, generatedAxisGlobalFifthShortWord_QImage]
  exact hc

/-- The same finite certificate gives the entire actual Griess short-unit root-word image. -/
theorem generatedAxisGlobalFifthShortWord_griess_basis (k : Fin 14)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalFifthChainQImage k 7 (griessShortQ r) =
      qCentral c * griessShortQ s) :
    rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0, (qSign c • Pi.single s (1 : ℝ), 0)) := by
  rw [← generatedAxisGlobalFifthShortWordFiber_local]
  apply monsterNortonGriessShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq, generatedAxisGlobalFifthShortWord_QImage]
  exact hc

/-- Complete finite preferred-Q certificates transport every coefficient
of a supported short sum. -/
theorem generatedAxisGlobalFifthShortWord_short_sum {ι : Type*} [Fintype ι]
    (k : Fin 14) (r s : ι → GriessShortIndex) (p : ι → ZMod 2) (c : ι → ℝ)
    (hc : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (griessShortQ (r i)) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalFifthShortWordFiber k)
        (∑ i, c i • Pi.single (r i) (1 : ℝ)) =
      ∑ i, (c i * qSign (p i)) • Pi.single (s i) (1 : ℝ) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, generatedAxisGlobalFifthShortWord_short_basis k _ _ _ (hc i), smul_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
