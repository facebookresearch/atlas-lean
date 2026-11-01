/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full original odd-short coordinates after the next genuine Norton U step. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ShortSeventhU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire finite odd-short coordinate vector after the actual next Norton U step. -/
noncomputable def monsterNortonLine01SeventhUShortCoordinates : GriessShortIndex → ℝ :=
  (1 / 512 : ℝ) • ∑ j : Fin 16, ∑ p : Fin 32,
    (monsterNortonLine01OctadSeventhCoefficientLookup j
      (monsterNortonLine01OctadSignLabel p) : ℝ) •
      (qSign (monsterNortonLine01ShortInversePhase (monsterNortonLine01OctadSourceA j p)
        (monsterNortonLine01OctadSourceK j p)) •
        Pi.single (Sum.inr (Sum.inr
          (monsterNortonLine01ShortInputCode (monsterNortonLine01OctadSourceA j p),
            monsterNortonLine01ShortPhysicalColumn (monsterNortonLine01OctadSourceK j p)))) 1)

private theorem source_short_lift (d : Fin 2048) (i : Fin 24) :
    monsterNortonShortLiftLinear (Pi.single (Sum.inr (Sum.inr (d, i))) 1) =
      trialityXYZBasis 0 (finProdFinEquiv (d, i)) := by
  rw [monsterNortonSourceX_pure_short, monsterNortonShortLiftLinear_apply]
  rfl

/-- The full checked next-U short vector is precisely the original pure-short decoder. -/
theorem monsterNortonLine01SeventhUShortCoordinates_actual :
    monsterNortonShortLiftLinear monsterNortonLine01SeventhUShortCoordinates =
      monsterNortonLine01ShortSeventhUVector := by
  rw [monsterNortonLine01SeventhUShortCoordinates, map_smul, map_sum]
  simp only [map_sum, map_smul, source_short_lift]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
