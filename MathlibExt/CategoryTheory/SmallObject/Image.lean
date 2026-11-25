/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.Closure
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Images of generated left classes from actual cell complexes

The original small-object left factor and its mapped retract prove membership
in a retract-closed target property. No target model or lifting structure is
assumed. The cardinal, caller ordinal bottom, and actual endpoint map remain
explicit.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w vC vD uC uD

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  (P : MorphismProperty C) (Q : MorphismProperty D) (F : C ⥤ D)
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [P.IsCardinalForSmallObjectArgument κ] [Q.IsStableUnderRetracts]

/-- Images of the actual cardinal cell endpoints determine the generated left-class image. -/
theorem rlp_llp_le_inverseImage_of_cardinal_cells
    (hCells : ∀ {X Y : C} (f : X ⟶ Y),
      HomotopicalAlgebra.RelativeCellComplex.{w}
        (fun (_ : κ.ord.ToType) => P.homFamily) f → Q (F.map f)) :
    P.rlp.llp ≤ Q.inverseImage F := by
  intro X Y f hf
  let c := SmallObject.relativeCellComplexιObj P κ f
  have hLeft : Q (F.map (SmallObject.ιObj P κ f)) := hCells _ c
  let _ : HasLiftingProperty f (SmallObject.πObj P κ f) :=
    hf _ (SmallObject.rlp_πObj P κ f)
  let retract : RetractArrow f (SmallObject.ιObj P κ f) :=
    RetractArrow.ofLeftLiftingProperty (SmallObject.ιObj_πObj P κ f)
  exact Q.of_retract (retract.map F) hLeft

/-- Generator images and the used colimit/closure properties determine the whole left class. -/
theorem rlp_llp_le_inverseImage_of_cardinal_closure
    [PreservesColimitsOfSize.{w, w} F]
    [PreservesColimitsOfShape κ.ord.ToType F]
    [PreservesWellOrderContinuousOfShape κ.ord.ToType F]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (hGenerators : P ≤ Q.inverseImage F) :
    P.rlp.llp ≤ Q.inverseImage F := by
  apply rlp_llp_le_inverseImage_of_cardinal_cells P Q F κ
  intro X Y f c
  exact c.map_mem_of_le F P Q hGenerators

end CategoryTheory.MorphismProperty
