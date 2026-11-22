/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFreeFiller

/-!
# Original unit and full indexed cells of the selected auxiliary step
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFreeFiller

open SSet SSet.joyalInterval

/-- The selected unit is an actual natural transformation into the original left class. -/
theorem unit_naturality {X Y : SSet.{u}} (m : X ⟶ Y) :
    auxiliaryAnodyneExtensions (auxiliaryFreeFillerUnit.app X) ∧
      m ≫ auxiliaryFreeFillerUnit.app Y =
        auxiliaryFreeFillerUnit.app X ≫ auxiliaryFreeFiller.map m := by
  exact ⟨auxiliaryFreeFillerUnit_mem X, auxiliaryFreeFillerUnit.naturality m⟩

/-- Every original indexed cell keeps its entire prescribed boundary and its label under maps. -/
theorem indexed_cell {X Y : SSet.{u}} (m : X ⟶ Y) (i : AuxiliaryGeneratorIndex.{u})
    (a : (auxiliaryGeneratorArrow i).left ⟶ X) :
    (auxiliaryGeneratorArrow i).hom ≫
        labelledFreeFiller.cell
          (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i a =
      a ≫ auxiliaryFreeFillerUnit.app X ∧
        labelledFreeFiller.cell
          (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i a ≫
          auxiliaryFreeFiller.map m =
            labelledFreeFiller.cell
              (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom)
                i (a ≫ m) := by
  constructor
  · change (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i ≫
        labelledFreeFiller.cell
          (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i a =
      a ≫ (labelledFreeFiller.unit
        (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom)).app X
    exact labelledFreeFiller.cell_boundary
      (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i a
  · change labelledFreeFiller.cell
        (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i a ≫
        (labelledFreeFiller
          (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom)).map m = _
    exact labelledFreeFiller.cell_naturality
      (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) m i a

end MathlibExtTest.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalFreeFiller
