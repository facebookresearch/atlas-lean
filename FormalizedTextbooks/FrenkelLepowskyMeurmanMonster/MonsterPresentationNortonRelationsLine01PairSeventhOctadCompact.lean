/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual sixteen-unit expansion of each reached seventh-state octad block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhOctadData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadShortExpansion

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


/-- Every reached original octad block is the complete checked sixteen-unit packet. -/
theorem monsterNortonLine01PairSeventhOctad_compact (a : Fin 14) :
    monsterNortonOctadShortVector (monsterNortonLine01PairBlockOctad a)
      (fun r => (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16) =
        ∑ j : Fin 16,
          ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
            monsterNortonPureShort (Sum.inr (Sum.inl
              (monsterNortonLine01PairBlockOctad a,
                monsterNortonLine01PairSeventhOctadSupport a j))) := by
  have hv : (fun r => (monsterNortonLine01PairSeventhOctadNumerator a r : ℝ) / 16) =
      ∑ j : Fin 16,
        ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) •
          Pi.single (monsterNortonLine01PairSeventhOctadSupport a j) 1 := by
    funext r
    rw [← monsterNortonLine01PairSeventhOctadSupport_certificate a r, Int.cast_sum,
      Finset.sum_div]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Int.cast_ite, Int.cast_zero, ite_div, zero_div, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : monsterNortonLine01PairSeventhOctadSupport a j = r
    · simp only [h, ite_true]
    · have h' : r ≠ monsterNortonLine01PairSeventhOctadSupport a j := Ne.symm h
      simp only [h, h', ite_false]
  change compactOctadLift (monsterNortonLine01PairBlockOctad a) _ = _
  rw [hv, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : GriessSpace =>
    ((monsterNortonLine01PairSeventhOctadSupportCoefficient a j : ℝ) / 16) • z)
      (monsterNortonOctadShortVector_single (monsterNortonLine01PairBlockOctad a)
        (monsterNortonLine01PairSeventhOctadSupport a j) 1)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
