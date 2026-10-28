/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Every actual Norton point/line and center/line Coxeter relation. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOrbitOrders
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A line vertex at one of the three even depths on a Y555 arm. -/
def monsterNortonLineVertex (a k : Fin 3) : Y555Vertex :=
  some (a, ⟨2 * k.val, by omega⟩)

/-- Its concrete parameter is the source line with the committed Norton label. -/
theorem monsterNortonParameter_line (a k : Fin 3) :
    y555NortonParameter monsterSourceTriality (monsterNortonLineVertex a k) =
      y555NortonLine monsterSourceTriality (y555NortonLineLabels a k) := by
  fin_cases k <;> rfl

/-- The finite cycle exponent agrees exactly with Y555 point/line incidence. -/
theorem monsterNortonPointLine_exponent (p : Fin 6) (a k : Fin 3) :
    monsterNortonNormalExponent
      ⟨((y555NortonLineLabels a k).val + (monsterNortonPointOrbitOffset p).val) % 13,
        Nat.mod_lt _ (by omega)⟩ =
      (if y555Adjacent (y555NortonPointVertex p) (monsterNortonLineVertex a k) then 3 else 2) := by
  revert p a k
  decide +kernel

/-- The same finite comparison gives the three center-adjacent line vertices. -/
theorem monsterNortonCenterLine_exponent (a k : Fin 3) :
    monsterNortonNormalExponent (y555NortonLineLabels a k) =
      (if y555Adjacent none (monsterNortonLineVertex a k) then 3 else 2) := by
  revert a k
  decide +kernel

/-- All fifty-four actual point/line pairs obey the precise Y555 Coxeter relation. -/
theorem monsterNortonCandidate_point_line_coxeter (p : Fin 6) (a k : Fin 3) :
    (y555NortonActualCandidate (y555NortonPointVertex p) *
      y555NortonActualCandidate (monsterNortonLineVertex a k)) ^
      (if y555Adjacent (y555NortonPointVertex p) (monsterNortonLineVertex a k)
        then 3 else 2) = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [y555NortonParameter_point, monsterNortonParameter_line]
  apply (monsterNortonPointLineQ_pow_iff _ _ _).mpr
  rw [monsterNortonPointLineQ_data, ← monsterNortonPointLine_exponent]
  exact monsterNortonNormalQData_order _

/-- All nine actual center/line candidate pairs obey the precise Y555 Coxeter relation. -/
theorem monsterNortonCandidate_center_line_coxeter (a k : Fin 3) :
    (y555NortonActualCandidate none *
      y555NortonActualCandidate (monsterNortonLineVertex a k)) ^
      (if y555Adjacent none (monsterNortonLineVertex a k) then 3 else 2) = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [monsterNortonParameter_line]
  change ((1 : ↥G) * (y555NortonLine monsterSourceTriality _)⁻¹) ^ _ = 1
  have h := (monsterNortonPointLineQ_pow_iff (y555NortonLineLabels a k) 1
    (if y555Adjacent none (monsterNortonLineVertex a k) then 3 else 2)).mpr (by
      rw [monsterNortonCenterLineQ_data, ← monsterNortonCenterLine_exponent]
      exact monsterNortonNormalQData_order _)
  simpa only [map_one] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
