/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Homotopy invariance of topological weak homotopy equivalences

Homotopic continuous maps are weak homotopy equivalences simultaneously.
The proof uses the singular simplicial homotopy and Kan weak equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u
namespace TopCat

/-! ## Homotopy invariance of topological weak equivalences -/

/-- Homotopic maps of spaces are weak homotopy equivalences simultaneously. -/
theorem weakHomotopyEquivalences_iff_of_homotopy
    {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    weakHomotopyEquivalences f ↔ weakHomotopyEquivalences g := by
  rw [TopCat.mem_weakHomotopyEquivalences_iff,
    TopCat.mem_weakHomotopyEquivalences_iff]
  let Hsing : SSet.Homotopy
      (TopCat.toSSet.map f) (TopCat.toSSet.map g) :=
    TopCat.Homotopy.toSSet H
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
    TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex Y
  exact SSet.KanComplex.W.iff_of_homotopy Hsing

/-- Actual continuous inverse homotopies give a weak equivalence of the
same original map. The singular Kan structures and both native inverse
homotopies are derived from the original continuous data. -/
theorem weakHomotopyEquivalences.of_homotopyInverse
    {X Y : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hY : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    weakHomotopyEquivalences f := by
  let e : ContinuousMap.HomotopyEquiv X Y :=
    { toFun := f.hom
      invFun := g.hom
      left_inv := ⟨hX.cast (TopCat.hom_comp f g) (TopCat.hom_id (X := X))⟩
      right_inv := ⟨hY.cast (TopCat.hom_comp g f) (TopCat.hom_id (X := Y))⟩ }
  apply TopCat.mem_of_eq_toFun e
  rfl

end TopCat

end
