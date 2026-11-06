/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- A typed linear inclusion of every actual original octad-coordinate block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadShortExpansion

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual raw Conway-coordinate octad inclusion as a linear map. -/
def monsterNortonOctadRawLinear (d : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] ConwayRawSpace where
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

/-- The actual full octad inclusion as a real linear map. -/
noncomputable def monsterNortonOctadShortLinear (d : Fin 759) : (Fin 64 → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp (monsterNortonOctadRawLinear d)


/-- This linear map is exactly the original Conway octad-vector inclusion. -/
theorem monsterNortonOctadShortLinear_apply (d : Fin 759) (v : Fin 64 → ℝ) :
    monsterNortonOctadShortLinear d v = monsterNortonOctadShortVector d v := by
  change griessConwayDecodeLinear (0, (monsterNortonOctadShortCoordinates d v, 0)) =
    griessConwayDecode (0, (monsterNortonOctadShortCoordinates d v, 0))
  rfl

/-- The actual octad block inclusion commutes with every real scalar. -/
theorem monsterNortonOctadShortVector_smul (d : Fin 759) (c : ℝ) (v : Fin 64 → ℝ) :
    monsterNortonOctadShortVector d (c • v) = c • monsterNortonOctadShortVector d v :=
  (monsterNortonOctadShortLinear d).map_smul c v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
