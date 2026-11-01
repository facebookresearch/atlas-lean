/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine diagonal short signs for every actual Q element, including Norton v. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The true short-coordinate phase of an actual Q element is its binary polar pairing. -/
theorem monsterNortonQ_short_phase (q : Q) (r : GriessShortIndex) :
    localShortPhase (localFiberIncl q) r =
      (qBeta (toAdd q.base) (toAdd (griessShortQ r).base) +
        qBeta (toAdd (griessShortQ r).base) (toAdd q.base)) := by
  change toAdd (spinConjugation (spinHolomorphIncl q) (griessShortQ r)).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero]

/-- The full actual short operator of Q is this diagonal sign on every coordinate. -/
theorem monsterNortonQ_short_apply (q : Q) (X : GriessShortIndex → ℝ)
    (r : GriessShortIndex) :
    localShortRepresentation (localFiberIncl q) X r =
      qSign ((qBeta (toAdd q.base) (toAdd (griessShortQ r).base) +
        qBeta (toAdd (griessShortQ r).base) (toAdd q.base))) * X r := by
  have hp : griessShortPermutation (localFiberIncl q).val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]
    rfl
  have h := localShortOperator_image (localFiberIncl q) X r
  rw [hp, monsterNortonQ_short_phase] at h
  exact h

/-- The actual Q action on a pure-short basis vector is the corresponding full signed basis. -/
theorem monsterNortonQ_griess_short_basis (q : Q) (r : GriessShortIndex) :
    localGriessRepresentation (localFiberIncl q)
      (griessConwayDecode (0, (Pi.single r 1, 0))) =
      griessConwayDecode (0,
        (qSign ((qBeta (toAdd q.base) (toAdd (monsterNortonShortQ r).base) +
          qBeta (toAdd (monsterNortonShortQ r).base) (toAdd q.base))) • Pi.single r 1, 0)) := by
  apply monsterNortonGriessShortBasis_of_Q_image
  change spinConjugation (spinHolomorphIncl q) (monsterNortonShortQ r) = _
  rw [spinConjugation_incl, q_conjugation_central_phase]

set_option maxRecDepth 10000 in
/-- The literal Norton involution has its genuine binary translation/modulation coordinates. -/
theorem monsterNortonVQ_coordinate_certificate :
    (∀ i : Fin 24, (toAdd y555NortonVQ.base i).val =
      if (0x80140e : ℕ).testBit i.val then 1 else 0) ∧ toAdd y555NortonVQ.coeff = 0 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
