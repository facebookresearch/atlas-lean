/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCuts

/-!
# Same original complete necklace cut maps

Both full native cut inclusions retain their SAME original interval
maps and actual cut vertex. The first positive cut is the original full
bead, and both cut dimensions retain their exact original bounds.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.Cut

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- The complete original prefix cut map at the SAME actual original joint. -/
def leftMap (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (leftData T j hj).object.{u} ⟶ T.object :=
  SSet.Subcomplex.lift ((complex (leftJoints T j)).ι ≫ SSet.stdSimplex.map
    (operator 0 j (Fin.zero_le j))) (by
    rintro ⟨⟨d⟩⟩ s ⟨a, rfl⟩
    exact (left_mem_iff T j a.val).mpr a.property)

/-- The complete original suffix cut map at that SAME actual original joint. -/
def rightMap (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (rightData T j hj).object.{u} ⟶ T.object :=
  SSet.Subcomplex.lift ((complex (rightJoints T j)).ι ≫ SSet.stdSimplex.map
    (operator j (Fin.last T.dimension) (Fin.le_last j))) (by
    rintro ⟨⟨d⟩⟩ s ⟨a, rfl⟩
    exact (right_mem_iff T j a.val).mpr a.property)

/-- The whole original prefix cut map retains its exact original interval equation. -/
@[reassoc]
theorem leftMap_ι (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    leftMap.{u} T j hj ≫ (complex T.joints).ι =
      (complex (leftJoints T j)).ι ≫ SSet.stdSimplex.map (operator 0 j (Fin.zero_le j)) := rfl

/-- The whole original suffix cut map retains its exact original interval equation. -/
@[reassoc]
theorem rightMap_ι (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    rightMap.{u} T j hj ≫ (complex T.joints).ι = (complex (rightJoints T j)).ι ≫
      SSet.stdSimplex.map (operator j (Fin.last T.dimension) (Fin.le_last j)) := rfl

/-- The whole prefix cut retains every original vertex at the SAME original native coordinate. -/
theorem leftMap_vertex (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (i : Fin (length 0 j + 1)) :
    vertexMap.{u} (leftJoints T j) i ≫ leftMap T j hj =
      vertexMap T.joints (leftEmbedding T j i) := by
  apply (cancel_mono (complex.{u} T.joints).ι).1
  rw [Category.assoc, leftMap_ι, ← Category.assoc, vertexMap_ι, vertexMap_ι,
    ← SSet.stdSimplex.map_comp]
  rfl

/-- The whole suffix cut retains every original vertex at the SAME original native coordinate. -/
theorem rightMap_vertex (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints)
    (i : Fin (length j (Fin.last T.dimension) + 1)) :
    vertexMap.{u} (rightJoints T j) i ≫ rightMap T j hj =
      vertexMap T.joints (rightEmbedding T j i) := by
  apply (cancel_mono (complex.{u} T.joints).ι).1
  rw [Category.assoc, rightMap_ι, ← Category.assoc, vertexMap_ι, vertexMap_ι,
    ← SSet.stdSimplex.map_comp]
  rfl

/-- The whole actual prefix retains the SAME original source endpoint. -/
theorem leftMap_source (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (leftData T j hj).source.{u} ≫ leftMap T j hj = T.source := by
  change vertexMap (leftJoints T j) 0 ≫ leftMap T j hj = vertexMap T.joints 0
  rw [leftMap_vertex, embedding_zero]

/-- The whole actual prefix retains the SAME original terminal cut joint. -/
theorem leftMap_target (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (leftData T j hj).target.{u} ≫ leftMap T j hj = vertexMap T.joints j := by
  change vertexMap (leftJoints T j) (Fin.last (length 0 j)) ≫ leftMap T j hj = _
  rw [leftMap_vertex, embedding_last]

/-- The whole actual suffix retains that SAME original initial cut joint. -/
theorem rightMap_source (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (rightData T j hj).source.{u} ≫ rightMap T j hj = vertexMap T.joints j := by
  change vertexMap (rightJoints T j) 0 ≫ rightMap T j hj = _
  rw [rightMap_vertex, embedding_zero]

/-- The whole actual suffix retains the SAME original terminal endpoint. -/
theorem rightMap_target (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (rightData T j hj).target.{u} ≫ rightMap T j hj = T.target := by
  change vertexMap (rightJoints T j) (Fin.last (length j (Fin.last T.dimension))) ≫ rightMap T j hj =
    vertexMap T.joints (Fin.last T.dimension)
  rw [rightMap_vertex, embedding_last]

/-- The two whole actual cuts agree at their SAME original endpoint point. -/
theorem cut_square (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) :
    (leftData T j hj).target.{u} ≫ leftMap T j hj =
      (rightData T j hj).source ≫ rightMap T j hj := by
  rw [leftMap_target, rightMap_source]

/-- A first actual positive cut has precisely the original full bead joint set. -/
theorem leftJoints_of_first_bead {T : Data} {j : Fin (T.dimension + 1)} (h : IsBead T 0 j) :
    leftJoints T j = {0, Fin.last (length 0 j)} := by
  ext i
  rw [mem_leftJoints]
  constructor
  · intro hi
    rcases h.consecutive (leftEmbedding T j i) hi with hz | hj
    · have he : leftEmbedding T j i = 0 := le_antisymm hz (Fin.zero_le _)
      have hi0 : i = 0 := (leftEmbedding T j).injective (he.trans (embedding_zero 0 j (Fin.zero_le j)).symm)
      exact Finset.mem_insert.mpr (Or.inl hi0)
    · have he : leftEmbedding T j i = j := le_antisymm
        (by have ht := (leftEmbedding T j).monotone (Fin.le_last i); rw [embedding_last] at ht; exact ht) hj
      have hiLast : i = Fin.last (length 0 j) := (leftEmbedding T j).injective
        (he.trans (embedding_last 0 j (Fin.zero_le j)).symm)
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hiLast))
  · intro hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [embedding_zero]
      exact h.source
    · have hi := Finset.mem_singleton.mp hi
      subst i
      rw [embedding_last]
      exact h.target

/-- Both original cut dimensions retain their literal sum, with no replacement of original vertices. -/
theorem dimensions_sum (T : Data) (j : Fin (T.dimension + 1)) :
    length 0 j + length j (Fin.last T.dimension) = T.dimension := by
  change j.val - 0 + (T.dimension - j.val) = T.dimension
  have hj := j.isLt
  omega

/-- The genuine positive original cut strictly reduces the suffix dimension. -/
theorem rightDimension_lt (T : Data) (j : Fin (T.dimension + 1)) (hj : 0 < j) :
    length j (Fin.last T.dimension) < T.dimension := by
  change T.dimension - j.val < T.dimension
  change 0 < j.val at hj
  have := j.isLt
  omega

end SSet.OriginalNecklace.Cut
