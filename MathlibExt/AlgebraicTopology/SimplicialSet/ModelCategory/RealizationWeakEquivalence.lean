/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Closure of realization-based weak equivalences

A simplicial map is a realization weak equivalence when applying geometric realization followed
by singular complexes gives a Kan weak equivalence. Since singular complexes are Kan, this
defines a class on arbitrary simplicial sets in every universe u.

The class contains identities, has two-of-three, is stable under arrow retracts and respects
isomorphisms. In universe zero it agrees with the inverse image of topological weak homotopy
equivalences under realization.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/-- For any simplicial sets, put U(X)=Sing(|X|). A realization weak equivalence f means U(f) is a
Kan weak equivalence: its fundamental-groupoid map is an equivalence and every based homotopy
map is bijective. Every identity belongs to this class because U(X) is always Kan. -/
instance realizationWeakEquivalences_containsIdentities :
    realizationWeakEquivalences.{u}.ContainsIdentities where
  id_mem X := by
    have hK : KanComplex (TopCat.toSSet.obj (SSet.toTop.obj X)) :=
      TopCat.toSSet_obj_kanComplex _
    change KanComplex.W ((SSet.toTop ⋙ TopCat.toSSet).map (𝟙 X))
    exact @KanComplex.W.ofIso _ _ (asIso _) hK hK

/-- For any simplicial sets, put U(X)=Sing(|X|). A realization weak equivalence f means U(f) is a
Kan weak equivalence: its fundamental-groupoid map is an equivalence and every based homotopy
map is bijective. For composable f,g, membership of any two of f,g,f≫g implies membership of the
third. -/
instance realizationWeakEquivalences_hasTwoOutOfThreeProperty :
    realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty :=
  inferInstanceAs
    ((KanComplex.W.inverseImage
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})).HasTwoOutOfThreeProperty)

/-- For any simplicial sets, put U(X)=Sing(|X|). A realization weak equivalence f means U(f) is a
Kan weak equivalence: its fundamental-groupoid map is an equivalence and every based homotopy
map is bijective. A retract in the arrow category of a realization weak equivalence is again a
realization weak equivalence. -/
instance realizationWeakEquivalences_isStableUnderRetracts :
    realizationWeakEquivalences.{u}.IsStableUnderRetracts :=
  inferInstanceAs
    ((KanComplex.W.inverseImage
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})).IsStableUnderRetracts)

/-- For any simplicial sets, put U(X)=Sing(|X|). A realization weak equivalence f means U(f) is a
Kan weak equivalence: its fundamental-groupoid map is an equivalence and every based homotopy
map is bijective. Replacing the source or target by an isomorphic simplicial set preserves this
weak-equivalence class. -/
instance realizationWeakEquivalences_respectsIso :
    realizationWeakEquivalences.{u}.RespectsIso :=
  inferInstanceAs
    ((KanComplex.W.inverseImage
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u})).RespectsIso)

/-- In universe zero, the realization-based weak-equivalence property equals the inverse image of
TopCat weak homotopy equivalences under geometric realization. -/
theorem realizationWeakEquivalences_zero_eq :
    realizationWeakEquivalences.{0} =
      TopCat.weakHomotopyEquivalences.inverseImage SSet.toTop :=
  (MorphismProperty.inverseImage_inverseImage
    (KanComplex.W : MorphismProperty SSet.{0}) SSet.toTop TopCat.toSSet).symm

/-- For f:X→Y between universe-zero simplicial sets, f is a realization weak equivalence exactly
when |f| is a topological weak homotopy equivalence. -/
theorem mem_realizationWeakEquivalences_zero_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    realizationWeakEquivalences f ↔
      TopCat.weakHomotopyEquivalences (SSet.toTop.map f) := by
  rw [realizationWeakEquivalences_zero_eq,
    MorphismProperty.inverseImage_iff]

end SSet
