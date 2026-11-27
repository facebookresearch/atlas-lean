/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialObjectHomotopy
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Realization of combinatorial simplicial homotopy equivalences

Two simplicial maps whose composites are combinatorially homotopic to the respective
identities realize to a topological homotopy equivalence. The forward and inverse
continuous maps are the realizations of the supplied simplicial maps.

In particular, an augmented simplicial set with an extra degeneracy has a
realization weak-equivalence augmentation, through its simplicial contraction.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MorphismProperty

universe u

namespace SSet

/--
Maps `f : X → Y` and `g : Y → X` with combinatorial simplicial homotopies
`f ≫ g ~ id_X` and `g ≫ f ~ id_Y` determine a topological homotopy equivalence
between their geometric realizations.
-/
noncomputable def realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) :=
  SSet.realizedHomotopyEquiv X Y f g
    Hfg.toSSetHomotopy Hgf.toSSetHomotopy

/--
The forward continuous map of the realized homotopy equivalence is the geometric
realization of the specified simplicial map `f`.
-/
@[simp]
theorem realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv_toFun
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y)) :
    (realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
      X Y f g Hfg Hgf).toFun = (SSet.toTop.map f).hom :=
  rfl

/--
A simplicial map admitting an inverse up to the two specified combinatorial
homotopies is a realization weak equivalence.
-/
theorem realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv
    {X Y : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y)) :
    SSet.realizationWeakEquivalences f := by
  let e := realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
    X Y f g Hfg Hgf
  change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
  exact TopCat.mem_of_eq_toFun e rfl

end SSet

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

/--
The augmentation of a Type-valued augmented simplicial object with an extra
degeneracy is a realization weak equivalence.
-/
theorem hom_mem_realizationWeakEquivalences
    {A : SimplicialObject.Augmented (Type u)}
    (ed : A.ExtraDegeneracy) :
    SSet.realizationWeakEquivalences A.hom := by
  apply SSet.realizationWeakEquivalences_of_simplicialObjectHomotopyEquiv
    A.hom ed.section_
  · exact ed.homotopy
  · simpa only [ed.section_comp_hom] using
      SimplicialObject.Homotopy.refl
        (𝟙 ((SimplicialObject.const (Type u)).obj A.right))

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

end
