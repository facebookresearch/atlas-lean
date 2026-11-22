/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.FunctionIteration
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalLoopTailAllPointComparison

/-!
# All physical points of the actual function-lambda telescope

The actual function evaluation supplies both next-level loop maps. The original
input-lambda diagrams, cylinder projections and cocones give both comparison
maps at each physical point, both input naturalities and both stage-leg equations.
The original integer-pi comparison with this raw predecessor map is separate.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open CategoryTheory.Spectra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionTelescopePi

open FunctionIteration

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.PointedAtGeometry.pointedNatColimits
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The literal function functor has the original next-level loop evaluation in both directions. -/
def stepEvaluation (m : ℕ) :
    stabilizationFunction.{u, v} ⋙ IterationMaps.level m ≅
      IterationMaps.level (m + 1) ⋙ PointedCGWH.loop :=
  Functor.isoWhiskerRight stabilizationFunctionIso (IterationMaps.level m) ≪≫
    IterationMaps.stepEvaluation m

/-- Its forward map retains the complete original function comparison at this level. -/
theorem stepEvaluation_hom_app (m : ℕ) (X : Carrier.{u, v}) :
    (stepEvaluation m).hom.app X =
      (IterationMaps.level m).map (stabilizationFunctionIso.hom.app X) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Its inverse retains the inverse of that same complete original function comparison. -/
theorem stepEvaluation_inv_app (m : ℕ) (X : Carrier.{u, v}) :
    (stepEvaluation m).inv.app X =
      (IterationMaps.level m).map (stabilizationFunctionIso.inv.app X) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The actual predecessor homotopy diagram retains every original input-lambda transition. -/
abbrev rawPiDiagram (X : Carrier.{u, v}) (m k : ℕ) :=
  (Functor.Iteration.inputDiagram lambdaStar X ⋙ IterationMaps.level (m + 1)) ⋙
    PointedCGWH.piNFunctor (k + 1)

/-- Its literal input map is the original iterated function map followed by actual positive pi. -/
abbrev rawPiDiagramMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m k : ℕ) :
    rawPiDiagram X m k ⟶ rawPiDiagram Y m k :=
  Functor.whiskerRight
    (Functor.whiskerRight (Functor.Iteration.inputDiagramMap lambdaStar f)
      (IterationMaps.level (m + 1))) (PointedCGWH.piNFunctor (k + 1))

/-- The chosen Type colimit map is induced by those complete original input maps. -/
abbrev rawPiColimitMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m k : ℕ) :
    colimit (rawPiDiagram X m k) ⟶ colimit (rawPiDiagram Y m k) :=
  colim.map (rawPiDiagramMap f m k)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual stage-cylinder point is the same original point used by the lambda telescope. -/
abbrev CylinderPoint (X : Carrier.{u, v}) (m r : ℕ) :=
  OriginalLoopTailAllPointComparison.CylinderPoint lambdaStar X m r

/-- Its physical image is the image under the original positive-stage colimit leg. -/
abbrev PhysicalPoint (X : Carrier.{u, v}) (m r : ℕ) (p : CylinderPoint X m r) :=
  OriginalLoopTailAllPointComparison.PhysicalPoint lambdaStar X m r p

/-- Both actual comparison maps use the true function functor and its original lambda. -/
def physicalTypeIso (X : Carrier.{u, v}) (m r k : ℕ) (p : CylinderPoint X m r) :
    (PointedCGWH.piNFunctor k).obj (PhysicalPoint X m r p) ≅
      colimit (rawPiDiagram X m k) :=
  OriginalLoopTailAllPointComparison.physicalTypeIso lambdaStar stepEvaluation X m r k p

/-- The actual physical-point arrow keeps the original telescope map and original image point. -/
abbrev physicalMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint X m r) :
    PhysicalPoint X m r p ⟶
      PhysicalPoint Y m r (OriginalLoopTailAllPointComparison.stageImagePoint lambdaStar f m r p) :=
  OriginalLoopTailAllPointComparison.physicalMap lambdaStar f m r p

/-- Every actual spectrum map retains the complete physical/raw predecessor square. -/
theorem physicalTypeIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint X m r) :
    (PointedCGWH.piNFunctor k).map (physicalMap f m r p) ≫
      (physicalTypeIso Y m r k
        (OriginalLoopTailAllPointComparison.stageImagePoint lambdaStar f m r p)).hom =
    (physicalTypeIso X m r k p).hom ≫ rawPiColimitMap f m k :=
  OriginalLoopTailAllPointComparison.physicalTypeIso_input_naturality
    lambdaStar stepEvaluation f m r k p

/-- Both inverse comparisons retain the same original spectrum-map square. -/
theorem physicalTypeIso_inv_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint X m r) :
    rawPiColimitMap f m k ≫
      (physicalTypeIso Y m r k
        (OriginalLoopTailAllPointComparison.stageImagePoint lambdaStar f m r p)).inv =
    (physicalTypeIso X m r k p).inv ≫
      (PointedCGWH.piNFunctor k).map (physicalMap f m r p) :=
  OriginalLoopTailAllPointComparison.physicalTypeIso_inv_input_naturality
    lambdaStar stepEvaluation f m r k p

/-- The literal physical pi map is the original raw map conjugated by both original comparisons. -/
theorem physicalMap_pi_word {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint X m r) :
    (PointedCGWH.piNFunctor k).map (physicalMap f m r p) =
      (physicalTypeIso X m r k p).hom ≫ rawPiColimitMap f m k ≫
        (physicalTypeIso Y m r k
          (OriginalLoopTailAllPointComparison.stageImagePoint lambdaStar f m r p)).inv :=
  OriginalLoopTailAllPointComparison.physicalMap_pi_word lambdaStar stepEvaluation f m r k p

/-- Every original cylinder leg retains the complete forward physical/raw comparison. -/
theorem physicalTypeIso_hom_leg (X : Carrier.{u, v}) (m r k n : ℕ)
    (p : CylinderPoint X m r) :
    (PointedCGWH.piNFunctor k).map
      ((EnrichedCoaugmentationTelescope.basedTailCocone lambdaStar X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p).ι.app n) ≫
        (physicalTypeIso X m r k p).hom =
      (OriginalLoopTailAllPointComparison.cylinderTailTypeIso
        lambdaStar stepEvaluation X m r k p).hom.app n ≫
          colimit.ι (rawPiDiagram X m k) (r + n) :=
  OriginalLoopTailAllPointComparison.physicalTypeIso_hom_leg
    lambdaStar stepEvaluation X m r k n p

/-- The inverse comparison retains that same literal cylinder leg and predecessor index. -/
theorem physicalTypeIso_inv_leg (X : Carrier.{u, v}) (m r k n : ℕ)
    (p : CylinderPoint X m r) :
    (OriginalLoopTailAllPointComparison.cylinderTailTypeIso
      lambdaStar stepEvaluation X m r k p).hom.app n ≫
        colimit.ι (rawPiDiagram X m k) (r + n) ≫ (physicalTypeIso X m r k p).inv =
      (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone lambdaStar X
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p).ι.app n) :=
  OriginalLoopTailAllPointComparison.physicalTypeIso_inv_leg
    lambdaStar stepEvaluation X m r k n p

omit B in
/-- The physical-point map retains the entire original underlying telescope map. -/
theorem physicalMap_right {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint X m r) :
    (physicalMap f m r p).right =
      (component ((EnrichedCoaugmentationTelescope.telescopeFunctor lambdaStar).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right :=
  OriginalLoopTailAllPointComparison.physicalMap_right lambdaStar f m r p

end PointedCGWH.Spectra.Orthogonal.MMSSStabilization.OriginalFunctionTelescopePi
