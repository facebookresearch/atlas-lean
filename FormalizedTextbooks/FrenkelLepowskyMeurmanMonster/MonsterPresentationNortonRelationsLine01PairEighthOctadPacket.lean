/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete grouping of the actual eighth short packet into its two original octad blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairNinthOctadTransform

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All 240 actual short summands form exactly the full original eighth packet. -/
theorem monsterNortonLine01PairEighthShortPacket_sum :
    monsterNortonLine01PairEighthShortPacket =
      ∑ k : Fin 240, ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
        monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k) :=
  (monsterNortonLine01PairEighthCoefficient_sum
    (fun k => monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k))).symm

private theorem finite_group_smul {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [AddCommMonoid E] [Module ℝ E]
    (p : ι → Prop) [DecidablePred p] (f : ι → κ) (c : ι → ℝ) (v : κ → E) :
    (∑ i, if p i then c i • v (f i) else 0) =
      ∑ k, (∑ i, if p i ∧ f i = k then c i else 0) • v k := by
  classical
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : p i
  · simp [h, ite_smul]
  · simp [h]

private theorem coefficientGrouped (a : Fin 2) (r : Fin 64) :
    (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k ≠ true ∧
      (monsterNortonLine01PairEighthOctadSlot k, monsterNortonLine01PairEighthOctadSign k) =
        (a, r) then (monsterNortonLine01PairEighthCoefficient k : ℝ) / 16 else 0) =
      (monsterNortonLine01PairEighthOctadNumerator a r : ℝ) / 16 := by
  have hi : (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k ≠ true ∧
      (monsterNortonLine01PairEighthOctadSlot k, monsterNortonLine01PairEighthOctadSign k) =
        (a, r) then monsterNortonLine01PairEighthCoefficient k else 0) =
      monsterNortonLine01PairEighthOctadNumerator a r := by
    rw [← monsterNortonLine01PairEighthOctadNumerator_certificate]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hp : monsterNortonLine01PairEighthIsPair k = true <;>
      simp [hp, Prod.mk.injEq]
  have h := congrArg (fun z : ℤ => (z : ℝ) / 16) hi
  simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, Finset.sum_div, ite_div,
    zero_div] using h

/-- The full non-pair part of the actual eighth packet is exactly its two complete octad rows. -/
theorem monsterNortonLine01PairEighth_octad_packet :
    (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then 0 else
      ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
        monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k)) =
      ∑ a : Fin 2, monsterNortonOctadShortVector (monsterNortonLine01PairEighthBlockOctad a)
        (fun r => (monsterNortonLine01PairEighthOctadNumerator a r : ℝ) / 16) := by
  have hh : (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then 0 else
      ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
        monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k)) =
      ∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k ≠ true then
        ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
          monsterNortonPureShort (Sum.inr (Sum.inl
            (monsterNortonLine01PairEighthBlockOctad (monsterNortonLine01PairEighthOctadSlot k),
              monsterNortonLine01PairEighthOctadSign k))) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    unfold monsterNortonLine01PairEighthShortOutput
    by_cases hp : monsterNortonLine01PairEighthIsPair k = true <;> simp [hp]
    rfl
  rw [hh]
  rw [finite_group_smul (fun k => monsterNortonLine01PairEighthIsPair k ≠ true)
    (fun k => (monsterNortonLine01PairEighthOctadSlot k,
      monsterNortonLine01PairEighthOctadSign k))
    (fun k => (monsterNortonLine01PairEighthCoefficient k : ℝ) / 16)
    (fun ar => monsterNortonPureShort (Sum.inr (Sum.inl
      (monsterNortonLine01PairEighthBlockOctad ar.1, ar.2))))]
  simp only [coefficientGrouped]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact (monsterNortonOctadShortVector_expansion
    (monsterNortonLine01PairEighthBlockOctad a) _).symm

/-- Inverse extra sends the whole octad part to its two original surviving short units. -/
theorem monsterNortonLine01PairNinth_octad_packet :
    sExtra.symm
      (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then 0 else
        ((monsterNortonLine01PairEighthCoefficient k : ℝ) / 16) •
          monsterNortonPureShort (monsterNortonLine01PairEighthShortOutput k)) =
      ∑ a : Fin 2, (-1 / 2 : ℝ) • monsterNortonPureShort
        (Sum.inr (Sum.inl (monsterNortonLine01PairEighthBlockOctad a,
          monsterNortonLine01PairNinthOctadTarget a))) := by
  rw [monsterNortonLine01PairEighth_octad_packet, map_sum]
  simp only [monsterNortonLine01PairNinthOctad_vector]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
