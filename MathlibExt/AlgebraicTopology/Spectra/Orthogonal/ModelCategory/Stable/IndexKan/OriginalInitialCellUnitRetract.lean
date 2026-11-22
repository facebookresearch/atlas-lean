/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.ModelCategory.Stable.IndexKan.NativeStableIndexComparisons
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IndexUnitCellularClosure
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# The original initial I-cell factorization and its full unit retract

At the actual realized generator cardinal, factor the original initial arrow
of a cofibrant symmetric spectrum by the original I-family. Its lifting
property supplies the actual source retract. The original Kan-unit natural
transformation then supplies both full unit-arrow maps, both naturality squares
and both splitting equations. No unit weakness or stable model is an input.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra.EnrichedProjective
open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.NativeIndexKanComposition
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan.OriginalInitialCellUnitRetract

private abbrev C := Actual.SymmetricCarrier.{u, v}
private abbrev I : MorphismProperty C.{u, v} := NativeK.levelI

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private instance originalCardinalRegular : Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal⟩

private instance originalCardinalForI :
    I.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  Native.generatorsI_isCardinalForSmallObjectArgument

/-- The intermediate spectrum of the original initial I-cell factorization. -/
def initialCellObject (X : C.{u, v}) : C.{u, v} :=
  SmallObject.obj I realizedGeneratorCardinal (Diagrams.zeroTo X)

/-- The whole original first factor from the actual initial spectrum. -/
def initialCellInclusion (X : C.{u, v}) : Diagrams.zeroDiagram ⟶ initialCellObject X :=
  SmallObject.ιObj I realizedGeneratorCardinal (Diagrams.zeroTo X)

/-- The whole original second factor to the unchanged caller spectrum. -/
def initialCellProjection (X : C.{u, v}) : initialCellObject X ⟶ X :=
  SmallObject.πObj I realizedGeneratorCardinal (Diagrams.zeroTo X)

/-- Both original factors compose to the same full initial arrow. -/
theorem initialCell_factor (X : C.{u, v}) :
    initialCellInclusion X ≫ initialCellProjection X = Diagrams.zeroTo X :=
  SmallObject.ιObj_πObj I realizedGeneratorCardinal (Diagrams.zeroTo X)

/-- The original full I-cell history at the actual realized cardinal. -/
def initialCellComplex (X : C.{u, v}) :
    RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => I.{u, v}.homFamily)
      (initialCellInclusion X) :=
  SmallObject.relativeCellComplexιObj I realizedGeneratorCardinal (Diagrams.zeroTo X)

/-- Cofibrancy lifts the original initial arrow against its genuine second factor. -/
def initialArrowRetract (X : C.{u, v}) [IsCofibrant X] :
    RetractArrow (Diagrams.zeroTo X) (initialCellInclusion X) := by
  have hLeft : I.{u, v}.rlp.llp (Diagrams.zeroTo X) := by
    have hCof : cofibrations C.{u, v} (Diagrams.zeroTo X) :=
      (HomotopicalAlgebra.cofibration_iff _).mp
        ((isCofibrant_iff_of_isInitial (Diagrams.zeroTo X) Diagrams.zeroDiagramIsInitial).mp
          inferInstance)
    rwa [Native.cofibrations_eq] at hCof
  let _ : HasLiftingProperty (Diagrams.zeroTo X) (initialCellProjection X) :=
    hLeft _ (SmallObject.rlp_πObj I realizedGeneratorCardinal (Diagrams.zeroTo X))
  exact RetractArrow.ofLeftLiftingProperty (initialCell_factor X)

/-- The retract retains the original projection and both initial identities. -/
theorem initialArrowRetract_maps (X : C.{u, v}) [IsCofibrant X] :
    (initialArrowRetract X).i.left = 𝟙 Diagrams.zeroDiagram ∧
      (initialArrowRetract X).r.left = 𝟙 Diagrams.zeroDiagram ∧
      (initialArrowRetract X).r.right = initialCellProjection X :=
  ⟨rfl, rfl, rfl⟩

/-- The actual caller spectrum is a retract of its original whole I-cell object. -/
def initialSourceRetract (X : C.{u, v}) [IsCofibrant X] : Retract X (initialCellObject X) :=
  { i := (initialArrowRetract X).i.right
    r := (initialArrowRetract X).r.right
    retract := by simp }

/-- Both full original Kan-unit arrows inherit the actual source retract. -/
def initialUnitArrowRetract (X : C.{u, v}) [IsCofibrant X] :
    RetractArrow (symmetricOrthogonalAdjunction.unit.app X)
      (symmetricOrthogonalAdjunction.unit.app (initialCellObject X)) :=
  IndexUnitCellularClosure.unitRetractArrow
    CategoryTheory.Spectra.SpectrumIndexMaps.symmetricOrthogonalOperatorIndexFunctor
    (initialSourceRetract X)

/-- The unit retract retains both original source maps and both full UP images. -/
theorem initialUnitArrowRetract_maps (X : C.{u, v}) [IsCofibrant X] :
    (initialUnitArrowRetract X).i.left = (initialArrowRetract X).i.right ∧
      (initialUnitArrowRetract X).i.right =
        (symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map
          (initialArrowRetract X).i.right ∧
      (initialUnitArrowRetract X).r.left = initialCellProjection X ∧
      (initialUnitArrowRetract X).r.right =
        (symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map (initialCellProjection X) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both actual unit naturality squares and both original splitting equations. -/
theorem initialUnitArrowRetract_squares_and_splits (X : C.{u, v}) [IsCofibrant X] :
    (initialArrowRetract X).i.right ≫ symmetricOrthogonalAdjunction.unit.app (initialCellObject X) =
        symmetricOrthogonalAdjunction.unit.app X ≫
          (symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map
            (initialArrowRetract X).i.right ∧
      initialCellProjection X ≫ symmetricOrthogonalAdjunction.unit.app X =
        symmetricOrthogonalAdjunction.unit.app (initialCellObject X) ≫
          (symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map (initialCellProjection X) ∧
      (initialArrowRetract X).i.right ≫ initialCellProjection X = 𝟙 X ∧
      (symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map (initialArrowRetract X).i.right ≫
          (symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).map (initialCellProjection X) =
        𝟙 ((symmetricOrthogonalLan ⋙ symmetricOrthogonalRestriction).obj X) :=
  IndexUnitCellularClosure.unitRetractArrow_squares_and_splits
    CategoryTheory.Spectra.SpectrumIndexMaps.symmetricOrthogonalOperatorIndexFunctor
    (initialSourceRetract X)

end PointedCGWH.Spectra.Orthogonal.IndexKan.OriginalInitialCellUnitRetract
