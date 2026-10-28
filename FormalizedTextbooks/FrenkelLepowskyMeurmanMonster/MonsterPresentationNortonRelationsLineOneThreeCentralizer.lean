/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine centralizer witness for the independent distance-two Norton line ratio. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPointLineAll
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem point_inverts_line (p l : ↥G) (hp : p ^ 2 = 1)
    (hpl : (p * l⁻¹) ^ 2 = 1) : l * p = p * l⁻¹ := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hp])
  have hli : (p * l⁻¹)⁻¹ = p * l⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hpl])
  simpa only [mul_inv_rev, inv_inv, hpi] using hli

private theorem inverse_line_point (p l : ↥G) (h : l * p = p * l⁻¹) :
    l⁻¹ * p = p * l := by
  calc
    _ = l⁻¹ * (p * l⁻¹) * l := by group
    _ = l⁻¹ * (l * p) * l := by rw [← h]
    _ = _ := by group

private theorem line_pair_commutes_points (l m p q : ↥G)
    (hp : p ^ 2 = 1) (hq : q ^ 2 = 1)
    (hpl : (p * l⁻¹) ^ 2 = 1) (hpm : (p * m⁻¹) ^ 2 = 1)
    (hql : (q * l⁻¹) ^ 2 = 1) (hqm : (q * m⁻¹) ^ 2 = 1) :
    Commute (l * m⁻¹) (p * q) := by
  have hlp := point_inverts_line p l hp hpl
  have hmp := inverse_line_point p m (point_inverts_line p m hp hpm)
  have hlq := inverse_line_point q l (point_inverts_line q l hq hql)
  have hmq := point_inverts_line q m hq hqm
  change (l * m⁻¹) * (p * q) = (p * q) * (l * m⁻¹)
  calc
    _ = l * (m⁻¹ * p) * q := by group
    _ = l * (p * m) * q := by rw [hmp]
    _ = (l * p) * (m * q) := by group
    _ = (p * l⁻¹) * (q * m⁻¹) := by rw [hlp, hmq]
    _ = p * (l⁻¹ * q) * m⁻¹ := by group
    _ = _ := by rw [hlq]; group

/-- The actual product of the four common nonincident point lifts for source lines one and three. -/
def monsterNortonLineOneThreeFourPointQ : Q :=
  (y555NortonPointQ 0 * y555NortonPointQ 3) *
    (y555NortonPointQ 4 * y555NortonPointQ 5)

private def commonPoint : Fin 4 → Fin 6 := ![0, 3, 4, 5]
private def commonArm : Fin 2 → Fin 3 := ![1, 2]

private theorem common_point_square (p : Fin 4) (a : Fin 2) :
    (y555NortonPoint (commonPoint p) *
      (y555NortonLine monsterSourceTriality
        (y555NortonLineLabels (commonArm a) 0))⁻¹) ^ 2 = 1 := by
  have h := monsterNortonCandidate_point_line_coxeter (commonPoint p) (commonArm a) 0
  have hn : ¬ y555Adjacent (y555NortonPointVertex (commonPoint p))
      (monsterNortonLineVertex (commonArm a) 0) := by
    clear h
    revert p a
    decide +kernel
  simp only [hn, ite_false] at h
  have hp := (y555NortonCandidate_coxeter_iff _ _ _ _).mp h
  rw [y555NortonParameter_point, monsterNortonParameter_line] at hp
  exact hp

private theorem commutes_pair (p q : Fin 4) :
    Commute (y555NortonLine monsterSourceTriality 1 *
      (y555NortonLine monsterSourceTriality 3)⁻¹)
        (y555NortonPoint (commonPoint p) * y555NortonPoint (commonPoint q)) := by
  have hp0 := common_point_square p 0
  have hp1 := common_point_square p 1
  have hq0 := common_point_square q 0
  have hq1 := common_point_square q 1
  have ha0 : y555NortonLineLabels (commonArm 0) 0 = 1 := by decide +kernel
  have ha1 : y555NortonLineLabels (commonArm 1) 0 = 3 := by decide +kernel
  rw [ha0] at hp0 hq0
  rw [ha1] at hp1 hq1
  exact line_pair_commutes_points _ _ _ _
    (y555NortonPoint_sq _) (y555NortonPoint_sq _) hp0 hp1 hq0 hq1

/-- The genuine source line-one/line-three ratio commutes with its full four-point lift. -/
theorem monsterNortonLineOneThree_commutes_fourPoint :
    Commute (y555NortonLine monsterSourceTriality 1 *
      (y555NortonLine monsterSourceTriality 3)⁻¹)
        (qIntoGenerated monsterNortonLineOneThreeFourPointQ) := by
  have h := (commutes_pair 0 1).mul_right (commutes_pair 2 3)
  change Commute _ ((qIntoGenerated (y555NortonPointQ 0) *
    qIntoGenerated (y555NortonPointQ 3)) * (qIntoGenerated (y555NortonPointQ 4) *
      qIntoGenerated (y555NortonPointQ 5))) at h
  simpa only [monsterNortonLineOneThreeFourPointQ, map_mul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
