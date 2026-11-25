/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.Image

set_option autoImplicit false
noncomputable section
universe w vC vD uC uD
open CategoryTheory Limits

namespace MathlibExtTest.SmallObjectImage

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  (P : MorphismProperty C) (Q : MorphismProperty D) (F : C ⥤ D)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [P.IsCardinalForSmallObjectArgument κ] [Q.IsStableUnderRetracts]

-- The actual caller arrow is mapped; no full/faithful functor or target model is required.
example
    (hCells : ∀ {X Y : C} (f : X ⟶ Y),
      HomotopicalAlgebra.RelativeCellComplex.{w}
        (fun (_ : κ.ord.ToType) => P.homFamily) f → Q (F.map f))
    {X Y : C} (f : X ⟶ Y) (hf : P.rlp.llp f) : Q (F.map f) :=
  P.rlp_llp_le_inverseImage_of_cardinal_cells Q F κ hCells f hf

-- Only the actual source cardinal shape is preserved, with no target colimit hypothesis.
example
    [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape κ.ord.ToType F]
    [PreservesWellOrderContinuousOfShape κ.ord.ToType F]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hGenerators : P ≤ Q.inverseImage F) {X Y : C} (f : X ⟶ Y)
    (hf : P.rlp.llp f) : Q (F.map f) :=
  P.rlp_llp_le_inverseImage_of_cardinal_closure Q F κ hGenerators f hf

#check @MorphismProperty.rlp_llp_le_inverseImage_of_cardinal_cells
#check @MorphismProperty.rlp_llp_le_inverseImage_of_cardinal_closure
#print axioms MorphismProperty.rlp_llp_le_inverseImage_of_cardinal_cells
#print axioms MorphismProperty.rlp_llp_le_inverseImage_of_cardinal_closure

end MathlibExtTest.SmallObjectImage
