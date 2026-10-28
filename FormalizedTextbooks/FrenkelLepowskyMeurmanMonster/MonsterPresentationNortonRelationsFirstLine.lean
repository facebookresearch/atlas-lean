/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Coxeter relations between Norton's first line and the five nonincident cocode points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonActualCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The five noninitial point lifts are exactly the positive source cocodes. -/
theorem monsterNortonPoint_succ_cocode (i : Fin 5) :
    y555NortonPointQ i.succ =
      cocodeQ (golayLabelCoefficients (y555NortonPointCocodeLabel i)) := by
  fin_cases i <;> rfl

/-- Every one of these cocodes has odd source parity. -/
theorem monsterNortonPoint_succ_odd (i : Fin 5) :
    (golayLabelCoefficients (y555NortonPointCocodeLabel i)) 11 = 1 := by
  fin_cases i <;> decide +kernel

/-- Norton v commutes with each of the five noninitial point lifts in actual Q. -/
theorem monsterNortonVQ_commute_point_succ (i : Fin 5) :
    y555NortonVQ * y555NortonPointQ i.succ =
      y555NortonPointQ i.succ * y555NortonVQ := by
  rw [q_mul_comm_iff]
  fin_cases i <;> decide +kernel

/-- The same commutation relation holds in the named generated group. -/
theorem monsterNortonV_commute_point_succ (i : Fin 5) :
    y555NortonV * y555NortonPoint i.succ =
      y555NortonPoint i.succ * y555NortonV := by
  change qIntoGenerated y555NortonVQ * qIntoGenerated (y555NortonPointQ i.succ) = _
  rw [← map_mul, monsterNortonVQ_commute_point_succ, map_mul]
  rfl

/-- Each odd cocode point inverts the checked source triality in actual G. -/
theorem monsterNortonPoint_succ_conjugates_triality (i : Fin 5) :
    y555NortonPoint i.succ * monsterSourceTriality *
      (y555NortonPoint i.succ)⁻¹ = monsterSourceTriality⁻¹ := by
  have h : y555NortonPoint i.succ * extraIntoGenerated *
      (y555NortonPoint i.succ)⁻¹ = extraIntoGenerated⁻¹ := by
    apply Subtype.ext
    change rhoLocal (inclQ (y555NortonPointQ i.succ)) * sExtra *
      (rhoLocal (inclQ (y555NortonPointQ i.succ)))⁻¹ = sExtra⁻¹
    rw [monsterNortonPoint_succ_cocode]
    exact cocodeQ_conjugates_sExtra_inverse _ (monsterNortonPoint_succ_odd i)
  have hi := congrArg Inv.inv h
  simpa only [monsterSourceTriality, mul_inv_rev, inv_inv, mul_assoc] using hi

/-- The genuine point-times-triality word is an involution. -/
theorem monsterNortonPoint_succ_triality_square (i : Fin 5) :
    (y555NortonPoint i.succ * monsterSourceTriality) ^ 2 = 1 := by
  have hp : (y555NortonPoint i.succ)⁻¹ = y555NortonPoint i.succ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, y555NortonPoint_sq]
  have hi := monsterNortonPoint_succ_conjugates_triality i
  rw [hp] at hi
  calc
    _ = (y555NortonPoint i.succ * monsterSourceTriality *
      y555NortonPoint i.succ) * monsterSourceTriality := by rw [pow_two]; group
    _ = 1 := by rw [hi, inv_mul_cancel]

/-- All five nonincident point/first-line parameter words have square one. -/
theorem monsterNortonPoint_succ_first_line_square (i : Fin 5) :
    (y555NortonPoint i.succ * (y555NortonLine monsterSourceTriality 0)⁻¹) ^ 2 = 1 := by
  rw [y555NortonActualLine_zero]
  have hc := monsterNortonV_commute_point_succ i
  have hw : y555NortonPoint i.succ *
      (y555NortonV * monsterSourceTriality⁻¹ * y555NortonV⁻¹)⁻¹ =
      y555NortonV * (y555NortonPoint i.succ * monsterSourceTriality) * y555NortonV⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv]
    calc
      _ = (y555NortonPoint i.succ * y555NortonV) *
        monsterSourceTriality * y555NortonV⁻¹ := by group
      _ = _ := by rw [← hc]; group
  rw [hw, conj_pow, monsterNortonPoint_succ_triality_square]
  simp

/-- The five nonincident point/first-line Coxeter relations hold in the actual wreath. -/
theorem monsterNortonCandidate_point_succ_first_line_square (i : Fin 5) :
    (y555NortonActualCandidate (y555NortonPointVertex i.succ) *
      y555NortonActualCandidate (some (0, 0))) ^ 2 = 1 := by
  apply (y555NortonCandidate_coxeter_iff _ _ _ _).mpr
  rw [y555NortonParameter_point]
  exact monsterNortonPoint_succ_first_line_square i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
