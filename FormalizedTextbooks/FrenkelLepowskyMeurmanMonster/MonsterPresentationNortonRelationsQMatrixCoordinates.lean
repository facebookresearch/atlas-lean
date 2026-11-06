/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Pointwise physical matrix transport by every actual local Q element. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixUTwo

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual Q element fixes the whole original pure symmetric matrix vector. -/
theorem monsterNortonQ_pure_matrix (q : Q) (A : Matrix (Fin 24) (Fin 24) ℝ)
    (ha : ∀ i j, A i j = A j i) :
    (qIntoGenerated q).val (griessConwayDecode (A, (0, 0))) =
      griessConwayDecode (A, (0, 0)) := by
  change localGriessRepresentation (localFiberIncl q) (griessConwayDecode (A, (0, 0))) = _
  have h := localGriessRepresentation_encode (localFiberIncl q)
    (griessConwayDecode (A, (0, 0)))
  rw [griessConwayEncode_decode _ ha, localConwayRawRepresentation_apply,
    map_zero, map_zero] at h
  change griessConwayEncode (localGriessRepresentation (localFiberIncl q)
    (griessConwayDecode (A, (0, 0)))) = (conwayMatrixAction 1 A, (0, 0)) at h
  rw [map_one] at h
  have hd := congrArg griessConwayDecode h
  rw [griessConwayDecode_encode] at hd
  exact hd

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
