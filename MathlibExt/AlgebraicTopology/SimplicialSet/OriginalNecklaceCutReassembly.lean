/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCutMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCategory

/-!
# Actual original necklace reassembly

The SAME two whole original cuts concatenate to the original necklace.
Both actual inverse ordinal maps retain every original vertex label,
full original joint membership and complete native simplex map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.Cut

open CategoryTheory.CoherentRealization.OriginalBeadInterval
open OriginalTwoBead.OrdinalCharts

/-- The literal whole original ordinal coordinate from the two concatenated cuts. -/
def reassemblyOperator (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    ⦋((leftData T j hj).concat (rightData T j hj)).dimension⦌ ⟶ ⦋T.dimension⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.val, by
        have hi := i.isLt
        change i.val < length 0 j + length j (Fin.last T.dimension) + 1 at hi
        rw [dimensions_sum T j] at hi
        exact hi⟩
      monotone' := fun _ _ h => h }

/-- The SAME original inverse ordinal coordinate, retaining every whole original vertex. -/
def separationOperator (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    ⦋T.dimension⦌ ⟶ ⦋((leftData T j hj).concat (rightData T j hj)).dimension⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.val, by
        change i.val < length 0 j + length j (Fin.last T.dimension) + 1
        rw [dimensions_sum]
        exact i.isLt⟩
      monotone' := fun _ _ h => h }

/-- Each SAME original first-cut vertex reads back its original coordinate. -/
theorem reassembly_prefix (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (i : Fin (length 0 j + 1)) :
    (reassemblyOperator T j hj).toOrderHom
        (prefixEmbedding (length 0 j) (length j (Fin.last T.dimension)) i) = leftEmbedding T j i :=
  by
    apply Fin.ext
    change i.val = 0 + i.val
    omega

/-- Each SAME original second-cut vertex reads back its original coordinate. -/
theorem reassembly_suffix (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (i : Fin (length j (Fin.last T.dimension) + 1)) :
    (reassemblyOperator T j hj).toOrderHom
        (suffix (length 0 j) (length j (Fin.last T.dimension)) i) = rightEmbedding T j i := by
  apply Fin.ext
  change j.val - 0 + i.val = j.val + i.val
  omega

/-- Every full original concatenated-cut joint maps to the SAME original necklace joint. -/
theorem reassembly_joint_maps (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (i : Fin (((leftData T j hj).concat (rightData T j hj)).dimension + 1))
    (hi : i ∈ ((leftData T j hj).concat (rightData T j hj)).joints) :
    (reassemblyOperator T j hj).toOrderHom i ∈ T.joints := by
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
    exact (reassembly_prefix T j hj k).symm ▸ (mem_leftJoints T j k).mp hk
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
    exact (reassembly_suffix T j hj k).symm ▸ (mem_rightJoints T j k).mp hk

/-- Every SAME original necklace joint has its actual original concatenated-cut preimage. -/
theorem reassembly_joint_preimage (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (k : Fin (T.dimension + 1)) (hk : k ∈ T.joints) :
    ∃ i ∈ ((leftData T j hj).concat (rightData T j hj)).joints,
      (reassemblyOperator T j hj).toOrderHom i = k := by
  by_cases hkj : k ≤ j
  · obtain ⟨i, hi⟩ := coverage 0 j (Fin.zero_le j) (ULift.up.{0} k)
      (by rw [lifted_zero]; exact Fin.zero_le _) (by rw [lifted_last]; exact hkj)
    have he : leftEmbedding T j i.down = k := congrArg ULift.down hi
    refine ⟨prefixEmbedding _ _ i.down, Finset.mem_union.mpr (Or.inl
      (Finset.mem_map.mpr ⟨i.down, (mem_leftJoints T j i.down).mpr (he.symm ▸ hk), rfl⟩)), ?_⟩
    exact (reassembly_prefix T j hj i.down).trans he
  · obtain ⟨i, hi⟩ := coverage j (Fin.last T.dimension) (Fin.le_last j) (ULift.up.{0} k)
      (by rw [lifted_zero]; exact (not_le.mp hkj).le) (by rw [lifted_last]; exact Fin.le_last _)
    have he : rightEmbedding T j i.down = k := congrArg ULift.down hi
    refine ⟨suffix _ _ i.down, Finset.mem_union.mpr (Or.inr
      (Finset.mem_map.mpr ⟨i.down, (mem_rightJoints T j i.down).mpr (he.symm ▸ hk), rfl⟩)), ?_⟩
    exact (reassembly_suffix T j hj i.down).trans he

/-- The genuine full native original map from the two concatenated cuts. -/
def reassemblyMorphism (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (leftData T j hj).concat (rightData T j hj) ⟶ T where
  operator := reassemblyOperator T j hj
  source := rfl
  target := by apply Fin.ext; exact dimensions_sum T j
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact map_mem_of_joints (reassemblyOperator T j hj) _ _ (reassembly_joint_preimage T j hj) s hs

/-- The SAME genuine full native original inverse map into the two concatenated cuts. -/
def separationMorphism (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    T ⟶ (leftData T j hj).concat (rightData T j hj) where
  operator := separationOperator T j hj
  source := rfl
  target := by apply Fin.ext; exact (dimensions_sum T j).symm
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    apply map_mem_of_joints (separationOperator T j hj) T.joints _ ?_ s hs
    intro i hi
    refine ⟨(reassemblyOperator T j hj).toOrderHom i, reassembly_joint_maps T j hj i hi, ?_⟩
    exact Fin.ext rfl

/-- Both SAME actual original native ordinal maps are inverse on EVERY whole original vertex. -/
def reassemblyIso (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (leftData T j hj).concat (rightData T j hj) ≅ T where
  hom := reassemblyMorphism T j hj
  inv := separationMorphism T j hj
  hom_inv_id := by
    apply SSet.OriginalNecklace.Morphism.ext
    ext i : 3
    exact Fin.ext rfl
  inv_hom_id := by
    apply SSet.OriginalNecklace.Morphism.ext
    ext i : 3
    exact Fin.ext rfl

/-- The same actual original reassembly on whole native simplicial sets. -/
def nativeReassemblyIso (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    ((leftData T j hj).concat (rightData T j hj)).object.{u} ≅ T.object :=
  SSet.OriginalNecklace.functor.mapIso (reassemblyIso T j hj)

end SSet.OriginalNecklace.Cut
