/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A genuine local centralizer witness for the first remaining Norton line-pair word. -/
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

private theorem common_point_square (p : Fin 4) (a : Fin 2) :
    (y555NortonPoint ⟨p.val + 2, by omega⟩ *
      (y555NortonLine monsterSourceTriality ⟨a.val, by omega⟩)⁻¹) ^ 2 = 1 := by
  have h := monsterNortonCandidate_point_line_coxeter ⟨p.val + 2, by omega⟩
    ⟨a.val, by omega⟩ 0
  have hn : ¬ y555Adjacent (y555NortonPointVertex ⟨p.val + 2, by omega⟩)
      (monsterNortonLineVertex ⟨a.val, by omega⟩ 0) := by
    clear h
    revert p a
    decide +kernel
  simp only [hn, ite_false] at h
  have hp := (y555NortonCandidate_coxeter_iff _ _ _ _).mp h
  rw [y555NortonParameter_point, monsterNortonParameter_line] at hp
  have hl : y555NortonLineLabels ⟨a.val, by omega⟩ 0 = (⟨a.val, by omega⟩ : Fin 13) := by
    fin_cases a <;> decide +kernel
  rw [hl] at hp
  exact hp

/-- The four common nonincident point parameters multiply to a concrete positive cocode. -/
theorem monsterNortonCommonFourPoints_Q :
    (y555NortonPointQ 2 * y555NortonPointQ 3) *
      (y555NortonPointQ 4 * y555NortonPointQ 5) =
        sourceQCocode (golayLabelCoefficients 924) := by
  apply NormalizedCocycleExtension.Extension.ext
  all_goals apply Multiplicative.toAdd.injective
  all_goals decide +kernel

/-- The actual first/second-line ratio commutes with the concrete four-point cocode. -/
theorem monsterNortonLineZeroOne_commutes_fourPoint :
    Commute (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹)
      (qIntoGenerated (sourceQCocode (golayLabelCoefficients 924))) := by
  have h23 := line_pair_commutes_points _ _ (y555NortonPoint 2) (y555NortonPoint 3)
    (y555NortonPoint_sq 2) (y555NortonPoint_sq 3)
    (common_point_square 0 0) (common_point_square 0 1)
    (common_point_square 1 0) (common_point_square 1 1)
  have h45 := line_pair_commutes_points _ _ (y555NortonPoint 4) (y555NortonPoint 5)
    (y555NortonPoint_sq 4) (y555NortonPoint_sq 5)
    (common_point_square 2 0) (common_point_square 2 1)
    (common_point_square 3 0) (common_point_square 3 1)
  have h := h23.mul_right h45
  have he : (y555NortonPoint 2 * y555NortonPoint 3) *
      (y555NortonPoint 4 * y555NortonPoint 5) =
        qIntoGenerated (sourceQCocode (golayLabelCoefficients 924)) := by
    change (qIntoGenerated (y555NortonPointQ 2) * qIntoGenerated (y555NortonPointQ 3)) *
      (qIntoGenerated (y555NortonPointQ 4) * qIntoGenerated (y555NortonPointQ 5)) = _
    rw [← map_mul, ← map_mul, ← map_mul, monsterNortonCommonFourPoints_Q]
  rw [he] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
