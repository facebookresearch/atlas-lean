/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

Mutually inverse simplicial-set maps up to combinatorial
`SimplicialObject.Homotopy` realize to a topological homotopy equivalence.
The construction uses the reverse cylinder adapter and has the literal
realization of the supplied forward map as its forward map.

As a reusable corollary, the augmentation of a Type-valued augmented
simplicial object with an extra degeneracy is a realization weak equivalence.
All witnesses are theorem-valued; this file installs no global instance and
makes no edgewise, iterated-realization, Fubini, model-category, or Q/S claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MorphismProperty

universe u

namespace SSet

/-- A combinatorial simplicial homotopy equivalence realizes to a topological
homotopy equivalence. -/
noncomputable def realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) :=
  SSet.realizedHomotopyEquiv X Y f g
    Hfg.toSSetHomotopy Hgf.toSSetHomotopy

/-- The forward map is literally the realization of `f`. -/
@[simp]
theorem realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv_toFun
    (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hfg : SimplicialObject.Homotopy (f ≫ g) (𝟙 X))
    (Hgf : SimplicialObject.Homotopy (g ≫ f) (𝟙 Y)) :
    (realizedHomotopyEquivOfSimplicialObjectHomotopyEquiv
      X Y f g Hfg Hgf).toFun = (SSet.toTop.map f).hom :=
  rfl

/-- The forward map of a combinatorial simplicial homotopy equivalence is a
realization weak equivalence. -/
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

/-- The augmentation of a Type-valued augmented simplicial object with an
extra degeneracy is a realization weak equivalence. -/
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
