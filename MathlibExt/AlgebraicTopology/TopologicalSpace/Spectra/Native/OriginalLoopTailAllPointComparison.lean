/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.LoopTailAllPointComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.IterationMaps

/-!
# Original Orthogonal loop tails at every physical telescope point

The original Orthogonal API specializes the indexed loop-tail construction at
its actual operator dimension. It retains the original input coaugmentation,
step evaluation, cylinder points, and both comparison maps in every degree.
The shared indexed implementation proves the physical-point and telescope
statements once, including degree zero and all loop components.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open CategoryTheory.Spectra HomotopicalAlgebra.EnrichedProjective.Native
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalLoopTailAllPointComparison

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.PointedAtGeometry.pointedNatColimits

section NativeOriginalLoop

open PointedCGWH.Spectra.Orthogonal.MMSSStabilization

/-- The unchanged native orthogonal carrier, including all original enriched actions. -/
abbrev Carrier := IterationMaps.Carrier.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {F : Carrier.{u, v} ⥤ Carrier.{u, v}}
  (η : 𝟭 Carrier.{u, v} ⟶ F)
  (step : ∀ m : ℕ, F ⋙ IterationMaps.level m ≅ IterationMaps.level (m + 1) ⋙ PointedCGWH.loop)

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The original positive raw tail starts at the actual index r + 1. -/
def positiveRawDiagram (X : Carrier.{u, v}) (m r : ℕ) : ℕ ⥤ PointedCGWH.{u, v} :=
  LoopTailAllPointComparison.positiveRawDiagram
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r

/-- The predecessor tail retains its original input transitions and original next-level index. -/
def predecessorDiagram (X : Carrier.{u, v}) (m r : ℕ) : ℕ ⥤ PointedCGWH.{u, v} :=
  LoopTailAllPointComparison.predecessorDiagram
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r

/-- Both single-step evaluation maps are the original shifted-loop evaluation comparison. -/
def inputNextEvaluationIso (X : Carrier.{u, v}) (m : ℕ) :
    (nextIndex ⋙ Functor.Iteration.inputDiagram η X) ⋙ IterationMaps.level m ≅
      (Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)) ⋙ PointedCGWH.loop :=
  LoopTailAllPointComparison.inputNextEvaluationIso
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m

/-- Both whole raw-tail maps are constructed from the original index, input and loop comparisons. -/
def positiveRawLoopIso (X : Carrier.{u, v}) (m r : ℕ) :
    positiveRawDiagram η X m r ≅ predecessorDiagram η X m r ⋙ PointedCGWH.loop :=
  LoopTailAllPointComparison.positiveRawLoopIso
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r

/-- Every positive stage retains the arithmetic transport of the original complete iterate. -/
def positiveStageIso (m r n : ℕ) :
    Functor.Iteration.iterate F (r + 1 + n) ⋙ IterationMaps.level m ≅
      (Functor.Iteration.iterate F (r + n) ⋙
        IterationMaps.level (m + 1)) ⋙ PointedCGWH.loop :=
  LoopTailAllPointComparison.positiveStageIso
    LoopTailAllPointComparison.orthogonalIndex.{u, v} step m r n

omit B in
/-- Every one-step forward component is the actual shifted-loop evaluation map. -/
theorem inputNextEvaluationIso_hom_app (X : Carrier.{u, v}) (m n : ℕ) :
    (inputNextEvaluationIso η step X m).hom.app n =
      (step m).hom.app
        ((Functor.Iteration.iterate F n).obj X) :=
  LoopTailAllPointComparison.inputNextEvaluationIso_hom_app
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m n

omit B in
/-- Each full raw-tail component retains the original arithmetic transport and loop comparison. -/
theorem positiveRawLoopIso_hom_app (X : Carrier.{u, v}) (m r n : ℕ) :
    (positiveRawLoopIso η step X m r).hom.app n = (positiveStageIso step m r n).hom.app X :=
  LoopTailAllPointComparison.positiveRawLoopIso_hom_app
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r n

omit B in
/-- Both full raw-tail components are the same original complete stage comparison. -/
theorem positiveRawLoopIso_app (X : Carrier.{u, v}) (m r n : ℕ) :
    (positiveRawLoopIso η step X m r).app n = (positiveStageIso step m r n).app X :=
  LoopTailAllPointComparison.positiveRawLoopIso_app
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r n

omit B in
/-- Every inverse raw-tail component keeps the same original inverse arithmetic and loop maps. -/
theorem positiveRawLoopIso_inv_app (X : Carrier.{u, v}) (m r n : ℕ) :
    (positiveRawLoopIso η step X m r).inv.app n = (positiveStageIso step m r n).inv.app X :=
  LoopTailAllPointComparison.positiveRawLoopIso_inv_app
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r n

/-- The actual positive raw input map retains every original iterated native input component. -/
def positiveRawMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ) :
    positiveRawDiagram η X m r ⟶ positiveRawDiagram η Y m r :=
  LoopTailAllPointComparison.positiveRawMap
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r

/--
The actual predecessor input map is the same original input iterate at its original next
level.
-/
def predecessorMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ) :
    predecessorDiagram η X m r ⟶ predecessorDiagram η Y m r :=
  LoopTailAllPointComparison.predecessorMap
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r

/-- The original raw input transformation retains every whole underlying component. -/
def rawUnderlyingMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ) :
    positiveRawDiagram η X m r ⋙ PointedCGWH.pointedToCGWH ⟶
      positiveRawDiagram η Y m r ⋙ PointedCGWH.pointedToCGWH :=
  LoopTailAllPointComparison.rawUnderlyingMap
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r

omit B in
/-- Original projection naturality retains both complete pointed component maps. -/
theorem projection_component_input_square {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m n : ℕ) :
    component ((EnrichedCoaugmentationTelescope.stage η n).functor.map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) ≫
      component ((EnrichedCoaugmentationTelescope.projection η n).app Y)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) =
      component ((EnrichedCoaugmentationTelescope.projection η n).app X)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) ≫
      component ((Functor.Iteration.iterate F n).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) :=
  LoopTailAllPointComparison.projection_component_input_square
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m n

omit B in
/-- All original input arrows commute with the exact full cylinder projection. -/
theorem projectionTailUnderlying_input_square {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r : ℕ) :
    EnrichedCoaugmentationTelescope.underlyingTailMap η f
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) ≫
      EnrichedCoaugmentationTelescope.projectionTailUnderlying η Y
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) =
      EnrichedCoaugmentationTelescope.projectionTailUnderlying η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) ≫ rawUnderlyingMap η f m r :=
  LoopTailAllPointComparison.projectionTailUnderlying_input_square
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r

omit B in
/-- All original input maps commute with the complete positive raw-loop comparison. -/
theorem positiveRawLoopIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r : ℕ) :
    positiveRawMap η f m r ≫ (positiveRawLoopIso η step Y m r).hom =
      (positiveRawLoopIso η step X m r).hom ≫
        Functor.whiskerRight (predecessorMap η f m r) PointedCGWH.loop :=
  LoopTailAllPointComparison.positiveRawLoopIso_input_naturality
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r

omit B in
/-- Both inverse raw-loop maps retain the same complete original input-map square. -/
theorem positiveRawLoopIso_input_inv_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r : ℕ) :
    Functor.whiskerRight (predecessorMap η f m r) PointedCGWH.loop ≫
        (positiveRawLoopIso η step Y m r).inv =
      (positiveRawLoopIso η step X m r).inv ≫ positiveRawMap η f m r :=
  LoopTailAllPointComparison.positiveRawLoopIso_input_inv_naturality
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r

omit B in
/-- Every complete positive-tail ordered arrow is conjugate to the genuine predecessor loop map. -/
theorem positiveRawLoopIso_map_word (X : Carrier.{u, v}) (m r : ℕ)
    {i j : ℕ} (f : i ⟶ j) :
    (positiveRawDiagram η X m r).map f =
      (positiveRawLoopIso η step X m r).hom.app i ≫
        PointedCGWH.loop.map ((predecessorDiagram η X m r).map f) ≫
          (positiveRawLoopIso η step X m r).inv.app j :=
  LoopTailAllPointComparison.positiveRawLoopIso_map_word
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r f

/-- The exact positive cylinder-stage point uses the original stage and the original level. -/
abbrev CylinderPoint (X : Carrier.{u, v}) (m r : ℕ) :=
  LoopTailAllPointComparison.CylinderPoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r

/-- The chosen raw point is the actual zero component of the original cylinder projection. -/
def projectedRawPoint (X : Carrier.{u, v}) (m r : ℕ) (p : CylinderPoint η X m r) :
    ((positiveRawDiagram η X m r).obj 0).right :=
  LoopTailAllPointComparison.projectedRawPoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r p

/-- Every actual source point is carried by the entire original cylinder-stage map. -/
def stageImagePoint {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint η X m r) : CylinderPoint η Y m r :=
  LoopTailAllPointComparison.stageImagePoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r p

omit B in
/-- Its projected raw point is the exact original raw-map image, without a new choice. -/
theorem projectedRawPoint_image {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint η X m r) :
    (rawUnderlyingMap η f m r).app 0 (projectedRawPoint η X m r p) =
      projectedRawPoint η Y m r (stageImagePoint η f m r p) :=
  LoopTailAllPointComparison.projectedRawPoint_image
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r p

/-- The full original raw-map diagram is based at the actual projection image points. -/
def rawBasedMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint η X m r) :
    EnrichedCoaugmentationTelescope.iterationTailBasedDiagram η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p ⟶
      EnrichedCoaugmentationTelescope.iterationTailBasedDiagram η Y
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) (stageImagePoint η f m r p) :=
  LoopTailAllPointComparison.rawBasedMap
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r p

omit B in
/-- Both original based input maps keep the same full projection square at every stage. -/
theorem basedTailProjection_input_square {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint η X m r) :
    EnrichedCoaugmentationTelescope.basedTailMap η f
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p ≫
      EnrichedCoaugmentationTelescope.basedTailProjection η Y
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) (stageImagePoint η f m r p) =
      EnrichedCoaugmentationTelescope.basedTailProjection η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p ≫ rawBasedMap η f m r p :=
  LoopTailAllPointComparison.basedTailProjection_input_square
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r p

/-- Each original raw-tail point is transported through the same complete raw input arrow. -/
def rawTailPoint (X : Carrier.{u, v}) (m r : ℕ) (p : CylinderPoint η X m r) (n : ℕ) :
    ((positiveRawDiagram η X m r).obj n).right :=
  LoopTailAllPointComparison.rawTailPoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r p n

omit B in
/-- Projection of every actual cylinder-tail point is exactly its original raw-tail point. -/
theorem projected_rawTailPoint (X : Carrier.{u, v}) (m r n : ℕ)
    (p : CylinderPoint η X m r) :
    (EnrichedCoaugmentationTelescope.projectionTailUnderlying η X
      (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1)).app n
      (PointedCGWH.PointedAtGeometry.diagramPoint
        (NatTail.tailFunctor (r + 1) ⋙
          (EnrichedCoaugmentationTelescope.evaluatedDiagram η X
            (OrthogonalOperatorIndex.ofIndex.{u, v} m) ⋙ PointedCGWH.pointedToCGWH)) p n) =
      rawTailPoint η X m r p n :=
  LoopTailAllPointComparison.projected_rawTailPoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r n p

/-- Both actual raw-loop comparison functions retain all original underlying carrier maps. -/
def underlyingRawLoopIso (X : Carrier.{u, v}) (m r : ℕ) :
    positiveRawDiagram η X m r ⋙ PointedCGWH.pointedToCGWH ≅
      (predecessorDiagram η X m r ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH :=
  LoopTailAllPointComparison.underlyingRawLoopIso
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r

omit B in
/-- Every original input map preserves both whole underlying raw-loop comparisons. -/
theorem underlyingRawLoopIso_input_square {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r : ℕ) :
    rawUnderlyingMap η f m r ≫ (underlyingRawLoopIso η step Y m r).hom =
      (underlyingRawLoopIso η step X m r).hom ≫
        Functor.whiskerRight (Functor.whiskerRight (predecessorMap η f m r) PointedCGWH.loop)
          PointedCGWH.pointedToCGWH :=
  LoopTailAllPointComparison.underlyingRawLoopIso_input_square
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r

/-- The actual predecessor-loop point is the image of the original projected zero-stage point. -/
def predecessorLoopPoint (X : Carrier.{u, v}) (m r : ℕ) (p : CylinderPoint η X m r) :
    (PointedCGWH.loop.obj ((predecessorDiagram η X m r).obj 0)).right :=
  LoopTailAllPointComparison.predecessorLoopPoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r p

omit B in
/-- Every raw-tail point follows the same actual predecessor loop-map point transport. -/
theorem rawTailPoint_loop_image (X : Carrier.{u, v}) (m r n : ℕ)
    (p : CylinderPoint η X m r) :
    (underlyingRawLoopIso η step X m r).hom.app n (rawTailPoint η X m r p n) =
      loopDiagramPoint (predecessorDiagram η X m r) (predecessorLoopPoint η step X m r p) n :=
  LoopTailAllPointComparison.rawTailPoint_loop_image
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r n p

/-- Both all-degree raw comparisons are built at the actual projection image point. -/
def rawTailTypeIso (X : Carrier.{u, v}) (m r k : ℕ) (p : CylinderPoint η X m r) :
    EnrichedCoaugmentationTelescope.iterationTailBasedDiagram η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p ⋙ PointedCGWH.piNFunctor k ≅
      predecessorDiagram η X m r ⋙ PointedCGWH.piNFunctor (k + 1) :=
  LoopTailAllPointComparison.rawTailTypeIso
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k p

omit B in
/-- The full arbitrary-point raw-tail comparisons are natural on every original input arrow. -/
theorem rawTailTypeIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r k : ℕ)
    (p : CylinderPoint η X m r) :
    Functor.whiskerRight (rawBasedMap η f m r p) (PointedCGWH.piNFunctor k) ≫
        (rawTailTypeIso η step Y m r k (stageImagePoint η f m r p)).hom =
      (rawTailTypeIso η step X m r k p).hom ≫
        Functor.whiskerRight (predecessorMap η f m r) (PointedCGWH.piNFunctor (k + 1)) :=
  LoopTailAllPointComparison.rawTailTypeIso_input_naturality
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p

/-- Original cylinder projection Type maps preserve the exact input and image-point square. -/
theorem basedTailProjectionTypeIso_input_naturality {X Y : Carrier.{u, v}}
    (f : X ⟶ Y) (m r k : ℕ) (p : CylinderPoint η X m r) :
    Functor.whiskerRight
        (EnrichedCoaugmentationTelescope.basedTailMap η f
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p) (PointedCGWH.piNFunctor k) ≫
      (EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso η Y
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) k
          (stageImagePoint η f m r p)).hom =
      (EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) k p).hom ≫
        Functor.whiskerRight (rawBasedMap η f m r p) (PointedCGWH.piNFunctor k) :=
  LoopTailAllPointComparison.basedTailProjectionTypeIso_input_naturality (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r k p

/--
The complete cylinder comparison retains its actual projection followed by the original loop
shift.
-/
def cylinderTailTypeIso (X : Carrier.{u, v}) (m r k : ℕ) (p : CylinderPoint η X m r) :
    EnrichedCoaugmentationTelescope.basedTailDiagram η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p ⋙ PointedCGWH.piNFunctor k ≅
      predecessorDiagram η X m r ⋙ PointedCGWH.piNFunctor (k + 1) :=
  LoopTailAllPointComparison.cylinderTailTypeIso (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k p

/-- Every complete original cylinder input map preserves the two actual Type comparison factors. -/
theorem cylinderTailTypeIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r) :
    Functor.whiskerRight
        (EnrichedCoaugmentationTelescope.basedTailMap η f
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p) (PointedCGWH.piNFunctor k) ≫
      (cylinderTailTypeIso η step Y m r k (stageImagePoint η f m r p)).hom =
      (cylinderTailTypeIso η step X m r k p).hom ≫
        Functor.whiskerRight (predecessorMap η f m r) (PointedCGWH.piNFunctor (k + 1)) :=
  LoopTailAllPointComparison.cylinderTailTypeIso_input_naturality (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p

/-- The explicit original associator aligns the predecessor pi diagram with the literal tail. -/
def predecessorPiTailIso (X : Carrier.{u, v}) (m r k : ℕ) :
    predecessorDiagram η X m r ⋙ PointedCGWH.piNFunctor (k + 1) ≅
      NatTail.tailFunctor r ⋙
        ((Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)) ⋙
          PointedCGWH.piNFunctor (k + 1)) :=
  LoopTailAllPointComparison.predecessorPiTailIso
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r k

omit B in
/-- Every forward predecessor/tail component is the same actual original pi object identity. -/
theorem predecessorPiTailIso_hom_app (X : Carrier.{u, v}) (m r k n : ℕ) :
    (predecessorPiTailIso η X m r k).hom.app n =
      𝟙 ((PointedCGWH.piNFunctor (k + 1)).obj
        ((Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)).obj (r + n))) :=
  LoopTailAllPointComparison.predecessorPiTailIso_hom_app
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r k n

omit B in
/-- Its original input square retains all actual predecessor and full tail maps. -/
theorem predecessorPiTailIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) :
    Functor.whiskerRight (predecessorMap η f m r) (PointedCGWH.piNFunctor (k + 1)) ≫
        (predecessorPiTailIso η Y m r k).hom =
      (predecessorPiTailIso η X m r k).hom ≫
        Functor.whiskerLeft (NatTail.tailFunctor r)
          (Functor.whiskerRight
            (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
              (IterationMaps.level (m + 1))) (PointedCGWH.piNFunctor (k + 1))) :=
  LoopTailAllPointComparison.predecessorPiTailIso_input_naturality
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r k

/-- Both full original cylinder comparisons land in the literal cofinal tail diagram. -/
def completedCylinderTailTypeIso (X : Carrier.{u, v}) (m r k : ℕ)
    (p : CylinderPoint η X m r) :
    EnrichedCoaugmentationTelescope.basedTailDiagram η X
        (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p ⋙ PointedCGWH.piNFunctor k ≅
      NatTail.tailFunctor r ⋙
        ((Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)) ⋙
          PointedCGWH.piNFunctor (k + 1)) :=
  LoopTailAllPointComparison.completedCylinderTailTypeIso (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k p

/-- The associator changes no original forward stage component of the complete comparison. -/
theorem completedCylinderTailTypeIso_hom_app (X : Carrier.{u, v}) (m r k n : ℕ)
    (p : CylinderPoint η X m r) :
    (completedCylinderTailTypeIso η step X m r k p).hom.app n =
      (cylinderTailTypeIso η step X m r k p).hom.app n :=
  LoopTailAllPointComparison.completedCylinderTailTypeIso_hom_app (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k n p

/-- All original input maps retain the complete literal cylinder/tail comparison square. -/
theorem completedCylinderTailTypeIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r) :
    Functor.whiskerRight
        (EnrichedCoaugmentationTelescope.basedTailMap η f
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p) (PointedCGWH.piNFunctor k) ≫
      (completedCylinderTailTypeIso η step Y m r k (stageImagePoint η f m r p)).hom =
      (completedCylinderTailTypeIso η step X m r k p).hom ≫
        Functor.whiskerLeft (NatTail.tailFunctor r)
          (Functor.whiskerRight
            (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
              (IterationMaps.level (m + 1))) (PointedCGWH.piNFunctor (k + 1))) :=
  LoopTailAllPointComparison.completedCylinderTailTypeIso_input_naturality (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p

/-- The physical telescope point is the image under the original positive-stage colimit leg. -/
abbrev PhysicalPoint (X : Carrier.{u, v}) (m r : ℕ) (p : CylinderPoint η X m r) :=
  LoopTailAllPointComparison.PhysicalPoint
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m r p

/--
Both physical-point comparison maps retain the original closed-cylinder and actual final-tail
cocones.
-/
def physicalTypeIso (X : Carrier.{u, v}) (m r k : ℕ) (p : CylinderPoint η X m r) :
    (PointedCGWH.piNFunctor k).obj (PhysicalPoint η X m r p) ≅
      colimit ((Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)) ⋙
        PointedCGWH.piNFunctor (k + 1)) :=
  LoopTailAllPointComparison.physicalTypeIso (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k p

/-- The physical-point map is the original telescope map with its actual image point. -/
def physicalMap {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint η X m r) :
    PhysicalPoint η X m r p ⟶ PhysicalPoint η Y m r (stageImagePoint η f m r p) :=
  LoopTailAllPointComparison.physicalMap
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r p

/-- All original physical input points retain the complete telescope/raw predecessor square. -/
theorem physicalTypeIso_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r) :
    (PointedCGWH.piNFunctor k).map (physicalMap η f m r p) ≫
        (physicalTypeIso η step Y m r k (stageImagePoint η f m r p)).hom =
      (physicalTypeIso η step X m r k p).hom ≫
        colim.map (Functor.whiskerRight
          (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
            (IterationMaps.level (m + 1)))
          (PointedCGWH.piNFunctor (k + 1))) :=
  LoopTailAllPointComparison.physicalTypeIso_input_naturality (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p

/-- Both inverse physical comparisons keep the same full original input-map square. -/
theorem physicalTypeIso_inv_input_naturality {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r) :
    colim.map (Functor.whiskerRight
        (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (IterationMaps.level (m + 1)))
        (PointedCGWH.piNFunctor (k + 1))) ≫
      (physicalTypeIso η step Y m r k (stageImagePoint η f m r p)).inv =
      (physicalTypeIso η step X m r k p).inv ≫
        (PointedCGWH.piNFunctor k).map (physicalMap η f m r p) :=
  LoopTailAllPointComparison.physicalTypeIso_inv_input_naturality (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p

/--
The actual physical-point homotopy map is the original raw map conjugated by both comparisons.
-/
theorem physicalMap_pi_word {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r) :
    (PointedCGWH.piNFunctor k).map (physicalMap η f m r p) =
      (physicalTypeIso η step X m r k p).hom ≫
        colim.map (Functor.whiskerRight
          (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
            (IterationMaps.level (m + 1)))
          (PointedCGWH.piNFunctor (k + 1))) ≫
        (physicalTypeIso η step Y m r k (stageImagePoint η f m r p)).inv :=
  LoopTailAllPointComparison.physicalMap_pi_word (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p

include step in
/-- An isomorphism of the original raw predecessor colimit map gives the actual all-point pi map. -/
theorem physicalMap_pi_isIso_of_raw {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r)
    (h : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (IterationMaps.level (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    IsIso ((PointedCGWH.piNFunctor k).map (physicalMap η f m r p)) :=
  LoopTailAllPointComparison.physicalMap_pi_isIso_of_raw (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p h

include step in
/--
Both actual physical-point homotopy functions are bijective from the original raw colimit map.
-/
theorem physicalMap_pi_bijective_of_raw {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint η X m r)
    (h : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (IterationMaps.level (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    Function.Bijective ((PointedCGWH.piNFunctor k).map (physicalMap η f m r p)) :=
  LoopTailAllPointComparison.physicalMap_pi_bijective_of_raw (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m r k p h

/--
Every actual stage leg retains the complete forward physical comparison and selected
predecessor leg.
-/
theorem physicalTypeIso_hom_leg (X : Carrier.{u, v}) (m r k n : ℕ)
    (p : CylinderPoint η X m r) :
    (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone η X
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p).ι.app n) ≫
      (physicalTypeIso η step X m r k p).hom =
        (cylinderTailTypeIso η step X m r k p).hom.app n ≫
          colimit.ι
            ((Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)) ⋙
              PointedCGWH.piNFunctor (k + 1)) (r + n) :=
  LoopTailAllPointComparison.physicalTypeIso_hom_leg (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k n p

/--
Every inverse physical comparison retains the same literal cylinder leg and predecessor index.
-/
theorem physicalTypeIso_inv_leg (X : Carrier.{u, v}) (m r k n : ℕ)
    (p : CylinderPoint η X m r) :
    (cylinderTailTypeIso η step X m r k p).hom.app n ≫
        colimit.ι
          ((Functor.Iteration.inputDiagram η X ⋙ IterationMaps.level (m + 1)) ⋙
            PointedCGWH.piNFunctor (k + 1)) (r + n) ≫
          (physicalTypeIso η step X m r k p).inv =
      (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone η X
          (OrthogonalOperatorIndex.ofIndex.{u, v} m) (r + 1) p).ι.app n) :=
  LoopTailAllPointComparison.physicalTypeIso_inv_leg (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step X m r k n p

omit B in
/--
Every physical telescope point has an original positive-stage representative after any
requested bound.
-/
theorem exists_positive_stage_point_after (X : Carrier.{u, v}) (m n₀ : ℕ)
    (x : ((EnrichedCoaugmentationTelescope.telescope η X).toEnrichedFunctor.obj
      (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right) :
    ∃ (r : ℕ), n₀ ≤ r + 1 ∧
      ∃ p : CylinderPoint η X m r,
        (component (EnrichedCoaugmentationTelescope.leg η X (r + 1))
          (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right p = x :=
  LoopTailAllPointComparison.exists_positive_stage_point_after
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η X m n₀ x

omit B in
/-- Each physical-point comparison uses the entire original evaluated telescope map. -/
theorem physicalMap_right {X Y : Carrier.{u, v}} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint η X m r) :
    (physicalMap η f m r p).right =
      (component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right :=
  LoopTailAllPointComparison.physicalMap_right
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η f m r p

include step in
/-- An original raw colimit isomorphism gives the pi map at every physical telescope point. -/
theorem telescopeMap_point_pi_isIso_of_raw {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (m k : ℕ)
    (x : (((EnrichedCoaugmentationTelescope.telescopeFunctor η).obj X).toEnrichedFunctor.obj
      (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right)
    (hRaw : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (IterationMaps.level (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    IsIso ((PointedCGWH.piNFunctor k).map (PointedCGWH.pointedAtMap
      (component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right x
      ((component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
        (OrthogonalOperatorIndex.ofIndex.{u, v} m)).right x) rfl)) :=
  LoopTailAllPointComparison.telescopeMap_point_pi_isIso_of_raw (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step f m k x hRaw

include step in
/-- The full original raw predecessor pi maps detect the actual telescope's level weak class. -/
theorem telescopeMap_weak_of_raw_colimit_isIso {X Y : Carrier.{u, v}} (f : X ⟶ Y)
    (hRaw : ∀ m k : ℕ, IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (IterationMaps.level (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    weakEquivalences Carrier.{u, v}
      ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f) :=
  LoopTailAllPointComparison.telescopeMap_weak_of_raw_colimit_isIso (B := B)
    LoopTailAllPointComparison.orthogonalIndex.{u, v} η step
    LoopTailAllPointComparison.orthogonalIndex_surjective.{u, v} f hRaw

end NativeOriginalLoop

end PointedCGWH.Spectra.OriginalLoopTailAllPointComparison
