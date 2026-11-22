/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.LabelledFreeFiller
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalGeneratorProperties
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalAnodyneClass

/-!
# The selected labelled auxiliary attachment step

The chosen functor and its natural unit use the original explicit family of
inner horns and finite-interval endpoint corners, with every original label.
The generic labelled attachment theorem places each unit in the actual
auxiliary anodyne class. No iteration or fibrancy conclusion is asserted.

This is Cisinski's Construction 2.4.36 specialized to Remark 3.3.4.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet.joyalInterval

/-- The generic labelled attachment functor for the original auxiliary family. -/
noncomputable def auxiliaryFreeFiller : SSet.{u} ⥤ SSet.{u} :=
  labelledFreeFiller
    (fun i : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow i).hom)

/-- The original natural unit for that same labelled family. -/
noncomputable def auxiliaryFreeFillerUnit : 𝟭 SSet.{u} ⟶ auxiliaryFreeFiller :=
  labelledFreeFiller.unit
    (fun i : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow i).hom)

/-- Every selected unit lies in the double lifting closure of the original family. -/
theorem auxiliaryFreeFillerUnit_mem (X : SSet.{u}) :
    auxiliaryAnodyneExtensions (auxiliaryFreeFillerUnit.app X) := by
  change auxiliaryGenerators.rlp.llp _
  rw [auxiliaryGenerators_eq_ofHoms]
  exact labelledFreeFiller.unit_mem
    (fun i : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow i).hom) X

end SSet.joyalInterval
