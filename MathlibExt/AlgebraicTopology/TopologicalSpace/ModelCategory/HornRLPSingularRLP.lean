/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGenerators

/-!
# Horn lifting under realization and the singular functor

A topological map lifts against all realized simplicial horn inclusions exactly
when its singular image lifts against all simplicial horn inclusions. The
realization–singular adjunction transports these lifting squares in both directions,
giving equality of the corresponding right lifting classes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/--
If a topological map lifts against all realized horns, its singular image lifts
against every simplicial horn generator.
-/
theorem hornRLP_toSSet_mem_J_rlp {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : realizedHornInclusions.rlp f) {A B : SSet.{u}} {i : A ⟶ B}
    (hi : SSet.modelCategoryQuillen.J i) :
    HasLiftingProperty i (toSSet.map f) := by
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨idx⟩⟩ := hi
  have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.horn (n + 1) idx).ι f).mp
    (hf _ (horn_mem_realizedHornInclusions (n + 1) idx))

/--
If the singular image of a topological map lifts against all simplicial horn
generators, the map lifts against all realized horn inclusions.
-/
theorem mem_hornRLP_of_toSSet_mem_J_rlp {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : SSet.modelCategoryQuillen.J.rlp (toSSet.map f)) :
    realizedHornInclusions.rlp f := by
  intro A B g hg
  simp only [realizedHornInclusions, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨idx⟩⟩ := hg
  have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  exact (sSetTopAdj.hasLiftingProperty_iff (SSet.horn (n + 1) idx).ι f).mpr
    (hf _ (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) idx))

/--
A topological map has realized-horn right lifting exactly when its singular
image has simplicial-horn right lifting.
-/
theorem hornRLP_iff_toSSet_mem_J_rlp {X Y : TopCat.{u}} {f : X ⟶ Y} :
    realizedHornInclusions.rlp f ↔
      SSet.modelCategoryQuillen.J.rlp (toSSet.map f) :=
  ⟨fun hf _ _ _ hi => hornRLP_toSSet_mem_J_rlp hf hi,
    mem_hornRLP_of_toSSet_mem_J_rlp⟩

/--
The realized-horn right lifting class equals the singular inverse image of
the simplicial-horn right lifting class.
-/
theorem hornRLP_eq_inverseImage_J_rlp :
    realizedHornInclusions.rlp =
      (SSet.modelCategoryQuillen.J.rlp).inverseImage toSSet := by
  apply le_antisymm
  · intro X Y f hf A B i hi
    exact hornRLP_toSSet_mem_J_rlp hf hi
  · intro X Y f hf A B g hg
    exact mem_hornRLP_of_toSSet_mem_J_rlp hf _ hg

end TopCat
