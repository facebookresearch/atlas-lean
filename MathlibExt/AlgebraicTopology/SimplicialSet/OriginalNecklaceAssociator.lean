/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceConcatenationMap

/-!
# The actual native original necklace associator

The same three complete original necklaces concatenate with either
parenthesization. The full native associator retains every ordinal
vertex, all original joints and both original endpoints. Its two actual
native maps are inverse in every coefficient universe.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace

open OriginalTwoBead.OrdinalCharts

/-- The SAME original associativity ordinal, preserving every full vertex value. -/
def associatorOperator (T U V : Data) :
    ⦋((T.concat U).concat V).dimension⦌ ⟶ ⦋(T.concat (U.concat V)).dimension⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.val, by
        have hi := i.isLt
        change i.val < T.dimension + (U.dimension + V.dimension) + 1
        change i.val < (T.dimension + U.dimension) + V.dimension + 1 at hi
        omega⟩
      monotone' := fun _ _ h => h }

/-- The SAME original inverse ordinal, preserving every original vertex value. -/
def associatorInverseOperator (T U V : Data) :
    ⦋(T.concat (U.concat V)).dimension⦌ ⟶ ⦋((T.concat U).concat V).dimension⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨i.val, by
        have hi := i.isLt
        change i.val < (T.dimension + U.dimension) + V.dimension + 1
        change i.val < T.dimension + (U.dimension + V.dimension) + 1 at hi
        omega⟩
      monotone' := fun _ _ h => h }

/-- Every SAME original target joint has its actual joint before reassociation. -/
theorem associator_joint_preimage (T U V : Data)
    (j : Fin ((T.concat (U.concat V)).dimension + 1))
    (hj : j ∈ (T.concat (U.concat V)).joints) :
    ∃ i ∈ ((T.concat U).concat V).joints, (associatorOperator T U V).toOrderHom i = j := by
  rcases Finset.mem_union.mp hj with hj | hj
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    refine ⟨prefixEmbedding (T.dimension + U.dimension) V.dimension
      (prefixEmbedding T.dimension U.dimension k), Finset.mem_union.mpr (Or.inl
        (Finset.mem_map.mpr ⟨_, Finset.mem_union.mpr (Or.inl
          (Finset.mem_map.mpr ⟨k, hk, rfl⟩)), rfl⟩)), Fin.ext rfl⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hk
      refine ⟨prefixEmbedding (T.dimension + U.dimension) V.dimension
        (suffix T.dimension U.dimension l), Finset.mem_union.mpr (Or.inl
          (Finset.mem_map.mpr ⟨_, Finset.mem_union.mpr (Or.inr
            (Finset.mem_map.mpr ⟨l, hl, rfl⟩)), rfl⟩)), Fin.ext rfl⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hk
      refine ⟨suffix (T.dimension + U.dimension) V.dimension l,
        Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr ⟨l, hl, rfl⟩)), ?_⟩
      apply Fin.ext
      change T.dimension + U.dimension + l.val = T.dimension + (U.dimension + l.val)
      omega

/-- Every SAME original source joint has its actual joint after reassociation. -/
theorem associatorInverse_joint_preimage (T U V : Data)
    (j : Fin (((T.concat U).concat V).dimension + 1))
    (hj : j ∈ ((T.concat U).concat V).joints) :
    ∃ i ∈ (T.concat (U.concat V)).joints, (associatorInverseOperator T U V).toOrderHom i = j := by
  rcases Finset.mem_union.mp hj with hj | hj
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hk
      exact ⟨prefixEmbedding T.dimension (U.dimension + V.dimension) l,
        Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨l, hl, rfl⟩)), Fin.ext rfl⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hk
      refine ⟨suffix T.dimension (U.dimension + V.dimension)
        (prefixEmbedding U.dimension V.dimension l), Finset.mem_union.mpr (Or.inr
          (Finset.mem_map.mpr ⟨_, Finset.mem_union.mpr (Or.inl
            (Finset.mem_map.mpr ⟨l, hl, rfl⟩)), rfl⟩)), Fin.ext rfl⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    refine ⟨suffix T.dimension (U.dimension + V.dimension) (suffix U.dimension V.dimension k),
      Finset.mem_union.mpr (Or.inr (Finset.mem_map.mpr ⟨_, Finset.mem_union.mpr (Or.inr
        (Finset.mem_map.mpr ⟨k, hk, rfl⟩)), rfl⟩)), ?_⟩
    apply Fin.ext
    change T.dimension + (U.dimension + k.val) = T.dimension + U.dimension + k.val
    omega

/-- The full SAME original native associator map on the entire three-piece necklace. -/
def associatorMorphism (T U V : Data) : (T.concat U).concat V ⟶ T.concat (U.concat V) where
  operator := associatorOperator T U V
  source := rfl
  target := by apply Fin.ext; exact Nat.add_assoc _ _ _
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact map_mem_of_joints (associatorOperator T U V) _ _ (associator_joint_preimage T U V) s hs

/-- The full SAME original native inverse associator map. -/
def associatorInverseMorphism (T U V : Data) : T.concat (U.concat V) ⟶ (T.concat U).concat V where
  operator := associatorInverseOperator T U V
  source := rfl
  target := by apply Fin.ext; exact (Nat.add_assoc _ _ _).symm
  lands := by
    rintro ⟨⟨d⟩⟩ s hs
    exact map_mem_of_joints (associatorInverseOperator T U V) _ _
      (associatorInverse_joint_preimage T U V) s hs

/-- The SAME complete original associator with both genuine original inverse maps. -/
def associatorIso (T U V : Data) : (T.concat U).concat V ≅ T.concat (U.concat V) where
  hom := associatorMorphism T U V
  inv := associatorInverseMorphism T U V
  hom_inv_id := by
    apply Morphism.ext
    ext i : 3
    exact Fin.ext rfl
  inv_hom_id := by
    apply Morphism.ext
    ext i : 3
    exact Fin.ext rfl

/-- The SAME full native associator is a genuine simplicial-set isomorphism in every universe. -/
def nativeAssociatorIso (T U V : Data) :
    ((T.concat U).concat V).object.{u} ≅ (T.concat (U.concat V)).object :=
  functor.mapIso (associatorIso T U V)

end SSet.OriginalNecklace
