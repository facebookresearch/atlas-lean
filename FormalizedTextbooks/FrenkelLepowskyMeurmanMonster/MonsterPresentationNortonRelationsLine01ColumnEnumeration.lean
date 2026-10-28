/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact enumeration of the supported physical columns in the actual first Norton word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceDictionary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSparseTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The sixteen displayed supported physical columns are distinct. -/
theorem monsterNortonLine01ShortPhysicalColumn_injective :
    Function.Injective monsterNortonLine01ShortPhysicalColumn := by
  decide +kernel

/-- The true first physical column has exactly the displayed sixteen supported terms. -/
theorem monsterNortonLine01_supported_columns {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Fin 24 → E) :
    (∑ i : Fin 24, (monsterNortonUNumerator1 i 0 : ℝ) • f i) =
      ∑ k : Fin 16,
        (monsterNortonUNumerator1 (monsterNortonLine01ShortPhysicalColumn k) 0 : ℝ) •
          f (monsterNortonLine01ShortPhysicalColumn k) := by
  let s : Finset (Fin 24) := Finset.univ.image monsterNortonLine01ShortPhysicalColumn
  have hs : s ⊆ Finset.univ := Finset.subset_univ _
  have hz : ∀ i ∈ Finset.univ, i ∉ s → (monsterNortonUNumerator1 i 0 : ℝ) • f i = 0 := by
    intro i _ hi
    have hni : monsterNortonUNumerator1 i 0 = 0 := by
      by_contra hn
      obtain ⟨k, hk⟩ := monsterNortonLine01ShortPhysicalColumn_cover i hn
      apply hi
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
    rw [hni, Int.cast_zero, zero_smul]
  rw [← Finset.sum_subset hs hz]
  exact Finset.sum_image (fun a _ b _ hab =>
    monsterNortonLine01ShortPhysicalColumn_injective hab)

/-- The genuine integer embedding transports finite integer linear combinations to real ones. -/
theorem monsterNortonUIntegerEmbed_sum {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (v : ι → NortonUIntegerVector) :
    nortonUIntegerEmbed (∑ a : ι, c a • v a) =
      ∑ a : ι, (c a : ℝ) • nortonUIntegerEmbed (v a) := by
  funext t
  simp only [nortonUIntegerEmbed, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Int.cast_sum, Int.cast_mul]

/-- The actual rank-one tensor inclusion transports every finite integer spin sum. -/
theorem monsterNortonTensorRankOne_integer_sum {ι : Type*} [Fintype ι]
    (b : Fin 24 → ℝ) (c : ι → ℤ) (v : ι → NortonUIntegerVector) :
    monsterNortonTensorRankOne b (nortonUIntegerEmbed (∑ a : ι, c a • v a)) =
      ∑ a : ι, (c a : ℝ) • monsterNortonTensorRankOne b (nortonUIntegerEmbed (v a)) := by
  rw [monsterNortonUIntegerEmbed_sum, map_sum]
  simp only [map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
