/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Horn-RLP transport across the realization/singular adjunction

This file is part of the KQ3 layer. A map in `TopCat` with the right lifting
property against all realized horn inclusions is sent by the singular
functor `TopCat.toSSet` to a map with the right lifting property against
`SSet.modelCategoryQuillen.J`, and conversely. For a simplicial horn
generator, the adjunction lemma `sSetTopAdj.hasLiftingProperty_iff` moves the
lifting problem across the adjunction, where
`TopCat.horn_mem_realizedHornInclusions` and
`SSet.modelCategoryQuillen.horn_ι_mem_J` apply.

This proves only the formal KQ3 transport isolated by `v0974`. It does not
place `SSet.modelCategoryQuillen.J.rlp` maps in `SSet.KanComplex.W`, claims no
weak-equivalence result, no model structure, and no TopCat cross inclusion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Morphism-level forward transport: the singular image of a horn-RLP map
lifts against every simplicial horn generator. -/
theorem hornRLP_toSSet_mem_J_rlp {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : realizedHornInclusions.rlp f) {A B : SSet.{u}} {i : A ⟶ B}
    (hi : SSet.modelCategoryQuillen.J i) :
    HasLiftingProperty i (toSSet.map f) := by
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨idx⟩⟩ := hi
  have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.horn (n + 1) idx).ι f).mp
    (hf _ (horn_mem_realizedHornInclusions (n + 1) idx))

/-- Morphism-level reverse transport: a map whose singular image lifts against
all simplicial horn generators is a horn-RLP map. -/
theorem mem_hornRLP_of_toSSet_mem_J_rlp {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : SSet.modelCategoryQuillen.J.rlp (toSSet.map f)) :
    realizedHornInclusions.rlp f := by
  intro A B g hg
  simp only [realizedHornInclusions, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨idx⟩⟩ := hg
  have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.horn (n + 1) idx).ι f).mpr
    (hf _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) idx))

/-- Morphism-level equivalence: horn-RLP maps are exactly those whose singular
image lifts against all simplicial horn generators. -/
theorem hornRLP_iff_toSSet_mem_J_rlp {X Y : TopCat.{u}} {f : X ⟶ Y} :
    realizedHornInclusions.rlp f ↔
      SSet.modelCategoryQuillen.J.rlp (toSSet.map f) :=
  ⟨fun hf _ _ _ hi => hornRLP_toSSet_mem_J_rlp hf hi,
    mem_hornRLP_of_toSSet_mem_J_rlp⟩

/-- Property-level equality: realized-horn RLP maps are the inverse image of
`SSet.modelCategoryQuillen.J.rlp` under `TopCat.toSSet`. -/
theorem hornRLP_eq_inverseImage_J_rlp :
    realizedHornInclusions.rlp =
      (SSet.modelCategoryQuillen.J.rlp).inverseImage toSSet := by
  apply le_antisymm
  · intro X Y f hf A B i hi
    exact hornRLP_toSSet_mem_J_rlp hf hi
  · intro X Y f hf A B g hg
    exact mem_hornRLP_of_toSSet_mem_J_rlp hf _ hg

end TopCat
