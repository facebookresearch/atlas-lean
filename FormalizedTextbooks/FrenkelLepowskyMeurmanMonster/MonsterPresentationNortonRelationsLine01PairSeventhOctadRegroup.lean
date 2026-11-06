/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Regrouping all actual seventh-state octad terms without dropping any coordinate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhOctadCompact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhRegroup

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private def compactOctadRawLift (d : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] ConwayRawSpace where
  toFun v := (0, (monsterNortonOctadShortCoordinates d v, 0))
  map_add' v w := by
    apply Prod.ext (zero_add _).symm
    apply Prod.ext _ (zero_add _).symm
    funext r
    rcases r with ⟨a,p⟩ | (⟨a,b⟩ | ⟨a,b⟩)
    · simp only [monsterNortonOctadShortCoordinates, Prod.fst_add, Prod.snd_add,
        Pi.add_apply, zero_add]
    · by_cases h : a = d <;> simp [monsterNortonOctadShortCoordinates, h]
    · simp only [monsterNortonOctadShortCoordinates, Prod.fst_add, Prod.snd_add,
        Pi.add_apply, zero_add]
  map_smul' c v := by
    apply Prod.ext (smul_zero _).symm
    apply Prod.ext _ (smul_zero _).symm
    funext r
    rcases r with ⟨a,p⟩ | (⟨a,b⟩ | ⟨a,b⟩)
    · exact (mul_zero c).symm
    · by_cases h : a = d <;> simp [monsterNortonOctadShortCoordinates, h]
    · exact (mul_zero c).symm

private noncomputable def compactOctadLift (d : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp (compactOctadRawLift d)



private theorem finite_group_vector {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [AddCommMonoid E] (p : ι → Prop) [DecidablePred p]
    (f : ι → κ) (v : ι → E) :
    (∑ i, if p i then v i else 0) =
      ∑ k, ∑ i, if p i ∧ f i = k then v i else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i <;> simp [h]

/-- The complete actual sixth-state coefficient, retaining both V phases. -/
noncomputable def monsterNortonLine01PairActualCoefficient (e : Fin 64) : ℝ :=
  ((monsterNortonLine01PairOctadInverseNumerator e : ℝ) / 8) *
    qSign (monsterNortonLine01PairOctadVPhase e) *
      qSign (monsterNortonLine01PairInverseVPhase e)

private theorem octadGroupedCoordinates (a : Fin 14) :
    (∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e ≠ true ∧
        monsterNortonLine01PairInverseOctadSlot e = a then
      monsterNortonLine01PairActualCoefficient e • trialityOctadAction
        (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1) else 0) =
      (fun r => (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16) := by
  funext r
  rw [← monsterNortonLine01PairSeventh_octad_data a r,
    monsterNortonLine01PairAfterSeventh, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    monsterNortonLine01PairSeventhTerm_octad]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hp : monsterNortonLine01PairInverseIsPair e = true
  · simp [hp]
  · by_cases hs : monsterNortonLine01PairInverseOctadSlot e = a
    · simp [hp, hs, monsterNortonLine01PairActualCoefficient]
    · simp [hp, hs]

/-- All actual non-pair seventh terms form exactly the fourteen entire certified octad blocks. -/
theorem monsterNortonLine01PairSeventh_octad_regroup :
    (∑ e : Fin 64, if monsterNortonLine01PairInverseIsPair e then 0 else
      monsterNortonLine01PairActualCoefficient e • monsterNortonOctadShortVector
        (monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e))
        (trialityOctadAction (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1))) =
      ∑ a : Fin 14, monsterNortonOctadShortVector (monsterNortonLine01PairBlockOctad a)
        (fun r => (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16) := by
  have hif (e : Fin 64) :
      (if monsterNortonLine01PairInverseIsPair e then (0 : GriessSpace) else
        monsterNortonLine01PairActualCoefficient e • monsterNortonOctadShortVector
          (monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e))
          (trialityOctadAction (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1))) =
      (if monsterNortonLine01PairInverseIsPair e ≠ true then
        monsterNortonLine01PairActualCoefficient e • monsterNortonOctadShortVector
          (monsterNortonLine01PairBlockOctad (monsterNortonLine01PairInverseOctadSlot e))
          (trialityOctadAction (Pi.single (monsterNortonLine01PairInverseOctadSign e) 1))
        else 0) := by
    by_cases h : monsterNortonLine01PairInverseIsPair e = true <;> simp [h]
  simp only [hif]
  rw [finite_group_vector (fun e => monsterNortonLine01PairInverseIsPair e ≠ true)
    monsterNortonLine01PairInverseOctadSlot]
  apply Finset.sum_congr rfl
  intro a _
  change _ = compactOctadLift (monsterNortonLine01PairBlockOctad a) _
  rw [← octadGroupedCoordinates a, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : monsterNortonLine01PairInverseIsPair e ≠ true ∧
      monsterNortonLine01PairInverseOctadSlot e = a
  · rw [ite_eq_left h, ite_eq_left h, h.2, map_smul]
    rfl
  · rw [ite_eq_right h, ite_eq_right h, map_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
