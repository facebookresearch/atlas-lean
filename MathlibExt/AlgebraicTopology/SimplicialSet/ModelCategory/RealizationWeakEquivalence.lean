/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Realization-based weak equivalences of simplicial sets

A morphism of simplicial sets is a `realizationWeakEquivalence` when applying
geometric realization and then the singular-complex functor produces a
`SSet.KanComplex.W` morphism. Unlike `KanComplex.W` itself, this property is
defined on arbitrary simplicial sets: singular complexes of realizations are
Kan, so the property contains every identity.

This file defines only the explicit morphism property and its formal closure
properties. It installs no category with weak equivalences, model category, or
Quillen instance.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/-- Realization weak equivalences contain identities because the singular
complex of every topological space is Kan. -/
instance realizationWeakEquivalences_containsIdentities :
    realizationWeakEquivalences.{u}.ContainsIdentities where
  id_mem X := by
    have hK : KanComplex (TopCat.toSSet.obj (SSet.toTop.obj X)) :=
      TopCat.toSSet_obj_kanComplex _
    change KanComplex.W ((SSet.toTop ⋙ TopCat.toSSet).map (𝟙 X))
    exact @KanComplex.W.ofIso _ _ (asIso _) hK hK

instance realizationWeakEquivalences_hasTwoOutOfThreeProperty :
    realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstanceAs
    ((KanComplex.W.inverseImage
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})).HasTwoOutOfThreeProperty)

instance realizationWeakEquivalences_isStableUnderRetracts :
    realizationWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs
    ((KanComplex.W.inverseImage
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})).IsStableUnderRetracts)

instance realizationWeakEquivalences_respectsIso :
    realizationWeakEquivalences.{u}.RespectsIso :=
  inferInstanceAs
    ((KanComplex.W.inverseImage
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})).RespectsIso)

/-- At universe zero, realization weak equivalences are the inverse image of
TopCat weak homotopy equivalences under geometric realization. -/
theorem realizationWeakEquivalences_zero_eq :
    realizationWeakEquivalences.{0} =
      TopCat.weakHomotopyEquivalences.inverseImage SSet.toTop :=
  (MorphismProperty.inverseImage_inverseImage
    (KanComplex.W : MorphismProperty SSet.{0}) SSet.toTop TopCat.toSSet).symm

/-- Pointwise form of `realizationWeakEquivalences_zero_eq`. -/
theorem mem_realizationWeakEquivalences_zero_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    realizationWeakEquivalences f ↔
      TopCat.weakHomotopyEquivalences (SSet.toTop.map f) := by
  rw [realizationWeakEquivalences_zero_eq,
    MorphismProperty.inverseImage_iff]

end SSet
