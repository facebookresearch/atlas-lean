/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete next Norton point/line checks, using the full actual u conjugation image. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImage

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4000000 in
-- Normalize the full seven-factor spin image on 24 binary coordinates and its central phase.
set_option maxRecDepth 10000 in
/-- The normalized center/second-line Q coefficient is exactly the initial x400 point. -/
theorem monsterNortonLineOne_center_Q :
    monsterNortonPointLineQ 1 1 = sourceQCode 1024 0 := by
  rw [monsterNortonPointLineQ_eq_orbit]
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    change (Multiplicative.toAdd (monsterNortonQOrbit 1 (y555NortonVQ * 1) *
      y555NortonVQ).base : Fin 24 → ZMod 2) =
      Multiplicative.toAdd (sourceQCode 1024 0).base
    decide +kernel
  · apply Multiplicative.toAdd.injective
    change (Multiplicative.toAdd (monsterNortonQOrbit 1 (y555NortonVQ * 1) *
      y555NortonVQ).coeff : ZMod 2) = Multiplicative.toAdd (sourceQCode 1024 0).coeff
    decide +kernel

set_option maxHeartbeats 4000000 in
-- Normalize the full seven-factor spin image on 24 binary coordinates and its central phase.
set_option maxRecDepth 10000 in
/-- The normalized initial-point/second-line Q coefficient is the actual second odd cocode. -/
theorem monsterNortonLineOne_point_zero_Q :
    monsterNortonPointLineQ 1 (y555NortonPointQ 0) = y555NortonPointQ 1 := by
  rw [monsterNortonPointLineQ_eq_orbit]
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    change (Multiplicative.toAdd (monsterNortonQOrbit 1
      (y555NortonVQ * y555NortonPointQ 0) * y555NortonVQ).base : Fin 24 → ZMod 2) =
      Multiplicative.toAdd (y555NortonPointQ 1).base
    decide +kernel
  · apply Multiplicative.toAdd.injective
    change (Multiplicative.toAdd (monsterNortonQOrbit 1
      (y555NortonVQ * y555NortonPointQ 0) * y555NortonVQ).coeff : ZMod 2) =
      Multiplicative.toAdd (y555NortonPointQ 1).coeff
    decide +kernel

/-- The actual center/second-line parameter word has cube one. -/
theorem monsterNortonLineOne_center_cube :
    ((1 : ↥G) * (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 3 = 1 := by
  have h := (monsterNortonPointLineQ_pow_iff 1 1 3).mpr (by
    rw [monsterNortonLineOne_center_Q]
    exact monsterNortonInitialStep_cube)
  simpa only [map_one] using h

/-- The actual initial-point/second-line parameter word has square one. -/
theorem monsterNortonLineOne_point_zero_square :
    (y555NortonPoint 0 * (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2 = 1 := by
  apply (monsterNortonPointLineQ_pow_iff 1 (y555NortonPointQ 0) 2).mpr
  rw [monsterNortonLineOne_point_zero_Q]
  exact monsterNortonPoint_succ_triality_square 0

/-- The second adjacent center/line Coxeter relation holds in the actual wreath. -/
theorem monsterNortonCandidate_center_line_one_cube :
    (y555NortonActualCandidate none * y555NortonActualCandidate (some (1, 0))) ^ 3 = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  exact monsterNortonLineOne_center_cube

/-- The initial point and second line satisfy their nonincident Coxeter square. -/
theorem monsterNortonCandidate_point_zero_line_one_square :
    (y555NortonActualCandidate (y555NortonPointVertex 0) *
      y555NortonActualCandidate (some (1, 0))) ^ 2 = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [y555NortonParameter_point]
  exact monsterNortonLineOne_point_zero_square

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
