/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact linear expansion of an original octad block in its sixty-four short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTrialityInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private def octadRawLift (d : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] ConwayRawSpace where
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

private noncomputable def octadLift (d : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp (octadRawLift d)

private theorem finite_unit_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    v = ∑ e, v e • Pi.single e 1 := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- An entire actual octad block is exactly the displayed finite sum of original short units. -/
theorem monsterNortonOctadShortVector_expansion (d : Fin 759) (v : Fin 64 → ℝ) :
    monsterNortonOctadShortVector d v =
      ∑ e, v e • monsterNortonPureShort (Sum.inr (Sum.inl (d, e))) := by
  change octadLift d v = _
  conv_lhs => rw [finite_unit_expansion v]
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun x : GriessSpace => v e • x)
    (monsterNortonOctadShortVector_single d e 1)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
