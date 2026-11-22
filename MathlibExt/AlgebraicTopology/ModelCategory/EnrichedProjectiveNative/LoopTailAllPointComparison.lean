/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.LoopTailPointComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeModel
import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeWeakDetection
import MathlibExt.AlgebraicTopology.Spectra.Sequential.EnrichedIndex
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex

/-!
# Original physical loop tails on an indexed enriched carrier

The original carrier, its actual evaluations, every iterated input map and both
physical-point comparisons are retained. Structural evaluations come from the
supplied original index presentation. The final level-weak conclusion uses its
actual surjectivity and the genuine predecessor Type-colimit map isomorphisms.
This is the shared implementation for every supplied index presentation.
The separate native integer calculation supplies the original colimit-map isomorphisms.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open CategoryTheory.Spectra
open PointedCGWH
open PointedCGWH.Spectra.OriginalLoopTailAllPointComparison
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.LoopTailAllPointComparison

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
  PointedCGWH.PointedAtGeometry.pointedNatColimits

section NativeOriginalLoop


variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

/-- The original enriched carrier keeps all actual enriched objects and maps. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

variable (index : ℕ → I)

/-- Evaluation uses the supplied original object at each original natural index. -/
abbrev level (m : ℕ) : Carrier (I := I) ⥤ PointedCGWH.{u, v} :=
  evaluation (V := PointedCGWH.{u, v}) (index m)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {F : (Carrier.{u, v} (I := I)) ⥤ (Carrier.{u, v} (I := I))}
  (η : 𝟭 (Carrier.{u, v} (I := I)) ⟶ F)
  (step : ∀ m : ℕ, F ⋙ level index m ≅ level index (m + 1) ⋙ PointedCGWH.loop)

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The original positive raw tail starts at the actual index r + 1. -/
def positiveRawDiagram (X : (Carrier.{u, v} (I := I))) (m r : ℕ) : ℕ ⥤ PointedCGWH.{u, v} :=
  NatTail.tailFunctor (r + 1) ⋙ (Functor.Iteration.inputDiagram η X ⋙ level index m)

/-- The predecessor tail retains its original input transitions and original next-level index. -/
def predecessorDiagram (X : (Carrier.{u, v} (I := I))) (m r : ℕ) : ℕ ⥤ PointedCGWH.{u, v} :=
  NatTail.tailFunctor r ⋙ (Functor.Iteration.inputDiagram η X ⋙ level index (m + 1))

/-- Both single-step evaluation maps are the original shifted-loop evaluation comparison. -/
def inputNextEvaluationIso (X : (Carrier.{u, v} (I := I))) (m : ℕ) :
    (nextIndex ⋙ Functor.Iteration.inputDiagram η X) ⋙ level index m ≅
      (Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙ PointedCGWH.loop :=
  evaluatedDiagramIso (nextIndex ⋙ Functor.Iteration.inputDiagram η X)
    (Functor.Iteration.inputDiagram η X) F
    (level index m) (level index (m + 1)) PointedCGWH.loop
    (inputNextIso η X) (step m)

/-- Both whole raw-tail maps are constructed from the original index, input and loop comparisons. -/
def positiveRawLoopIso (X : (Carrier.{u, v} (I := I))) (m r : ℕ) :
    positiveRawDiagram index η X m r ≅ predecessorDiagram index η X m r ⋙ PointedCGWH.loop :=
  positiveDiagramIso (Functor.Iteration.inputDiagram η X) F
    (level index m) (level index (m + 1)) PointedCGWH.loop
    (inputNextIso η X) (step m) r

/-- Every positive stage retains the arithmetic transport of the original complete iterate. -/
def positiveStageIso (m r n : ℕ) :
    Functor.Iteration.iterate F (r + 1 + n) ⋙ level index m ≅
      (Functor.Iteration.iterate F (r + n) ⋙
        level index (m + 1)) ⋙ PointedCGWH.loop :=
  evaluatedDiagramIso (Functor.Iteration.iterate F (r + 1 + n))
    (Functor.Iteration.iterate F (r + n)) F
    (level index m) (level index (m + 1)) PointedCGWH.loop
    (eqToIso (congrArg (Functor.Iteration.iterate F)
      (Nat.add_right_comm r 1 n))) (step m)

omit B in
/-- Every one-step forward component is the actual shifted-loop evaluation map. -/
theorem inputNextEvaluationIso_hom_app (X : (Carrier.{u, v} (I := I))) (m n : ℕ) :
    (inputNextEvaluationIso index η step X m).hom.app n =
      (step m).hom.app
        ((Functor.Iteration.iterate F n).obj X) := by
  let D := Functor.Iteration.inputDiagram η X
  let Z := F.obj ((Functor.Iteration.iterate F n).obj X)
  let s := (step m).hom.app
    ((Functor.Iteration.iterate F n).obj X)
  have h0 : (inputNextEvaluationIso index η step X m).hom.app n =
      (level index m).map (𝟙 Z) ≫ s :=
    (evaluatedDiagramIso_hom_app (nextIndex ⋙ D) D F
      (level index m) (level index (m + 1)) PointedCGWH.loop
      (inputNextIso η X) (step m) n).trans
        (congrArg (fun z => (level index m).map z ≫ s) (inputNextIso_hom_app η X n))
  exact h0.trans
    ((congrArg (fun z => z ≫ s) ((level index m).map_id Z)).trans (Category.id_comp s))

omit B in
/-- Each full raw-tail component retains the original arithmetic transport and loop comparison. -/
theorem positiveRawLoopIso_hom_app (X : (Carrier.{u, v} (I := I))) (m r n : ℕ) :
    (positiveRawLoopIso index η step X m r).hom.app n =
      (positiveStageIso index step m r n).hom.app X := by
  let D := Functor.Iteration.inputDiagram η X
  let s := (step m).hom.app
    ((Functor.Iteration.iterate F (r + n)).obj X)
  have h0 : (positiveRawLoopIso index η step X m r).hom.app n =
      (D ⋙ level index m).map ((nextTailIso r).hom.app n) ≫ s :=
    (positiveDiagramIso_hom_app D F (level index m)
      (level index (m + 1)) PointedCGWH.loop (inputNextIso η X)
      (step m) r n).trans
        (congrArg (fun z => (D ⋙ level index m).map ((nextTailIso r).hom.app n) ≫ z)
          (inputNextEvaluationIso_hom_app index η step X m (r + n)))
  have hm : (D ⋙ level index m).map ((nextTailIso r).hom.app n) =
      (level index m).map
        ((eqToHom (congrArg (Functor.Iteration.iterate F)
          (Nat.add_right_comm r 1 n))).app X) :=
    (level index m).congr_map
      (inputDiagram_map_eqToHom η X (Nat.add_right_comm r 1 n))
  have h1 := evaluatedDiagramIso_hom_app
    (Functor.Iteration.iterate F (r + 1 + n))
    (Functor.Iteration.iterate F (r + n)) F
    (level index m) (level index (m + 1)) PointedCGWH.loop
    (eqToIso (congrArg (Functor.Iteration.iterate F)
      (Nat.add_right_comm r 1 n))) (step m) X
  exact h0.trans ((congrArg (fun z => z ≫ s) hm).trans h1.symm)

omit B in
/-- Both full raw-tail components are the same original complete stage comparison. -/
theorem positiveRawLoopIso_app (X : (Carrier.{u, v} (I := I))) (m r n : ℕ) :
    (positiveRawLoopIso index η step X m r).app n = (positiveStageIso index step m r n).app X :=
  Iso.ext (positiveRawLoopIso_hom_app index η step X m r n)

omit B in
/-- Every inverse raw-tail component keeps the same original inverse arithmetic and loop maps. -/
theorem positiveRawLoopIso_inv_app (X : (Carrier.{u, v} (I := I))) (m r n : ℕ) :
    (positiveRawLoopIso index η step X m r).inv.app n =
      (positiveStageIso index step m r n).inv.app X :=
  congrArg Iso.inv (positiveRawLoopIso_app index η step X m r n)

/-- The actual positive raw input map retains every original iterated native input component. -/
def positiveRawMap {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ) :
    positiveRawDiagram index η X m r ⟶ positiveRawDiagram index η Y m r :=
  Functor.whiskerLeft (NatTail.tailFunctor (r + 1))
    (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index m))

/--
The actual predecessor input map is the same original input iterate at its original next
level.
-/
def predecessorMap {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ) :
    predecessorDiagram index η X m r ⟶ predecessorDiagram index η Y m r :=
  Functor.whiskerLeft (NatTail.tailFunctor r)
    (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))

/-- The original raw input transformation retains every whole underlying component. -/
def rawUnderlyingMap {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ) :
    positiveRawDiagram index η X m r ⋙ PointedCGWH.pointedToCGWH ⟶
      positiveRawDiagram index η Y m r ⋙ PointedCGWH.pointedToCGWH :=
  Functor.whiskerRight (positiveRawMap index η f m r) PointedCGWH.pointedToCGWH

omit B in
/-- Original projection naturality retains both complete pointed component maps. -/
theorem projection_component_input_square {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m n : ℕ) :
    component ((EnrichedCoaugmentationTelescope.stage η n).functor.map f)
        (index m) ≫
      component ((EnrichedCoaugmentationTelescope.projection η n).app Y)
        (index m) =
      component ((EnrichedCoaugmentationTelescope.projection η n).app X)
        (index m) ≫
      component ((Functor.Iteration.iterate F n).map f)
        (index m) :=
  (component_comp ((EnrichedCoaugmentationTelescope.stage η n).functor.map f)
    ((EnrichedCoaugmentationTelescope.projection η n).app Y)
    (index m)).symm.trans
      ((congrArg (fun t => component t (index m))
        ((EnrichedCoaugmentationTelescope.projection η n).naturality f)).trans
        (component_comp ((EnrichedCoaugmentationTelescope.projection η n).app X)
          ((Functor.Iteration.iterate F n).map f)
          (index m)))

omit B in
/-- All original input arrows commute with the exact full cylinder projection. -/
theorem projectionTailUnderlying_input_square {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r : ℕ) :
    EnrichedCoaugmentationTelescope.underlyingTailMap η f
        (index m) (r + 1) ≫
      EnrichedCoaugmentationTelescope.projectionTailUnderlying η Y
        (index m) (r + 1) =
      EnrichedCoaugmentationTelescope.projectionTailUnderlying η X
        (index m) (r + 1) ≫ rawUnderlyingMap index η f m r := by
  apply NatTrans.ext
  funext n
  change
    (component ((EnrichedCoaugmentationTelescope.stage η (r + 1 + n)).functor.map f)
      (index m)).right ≫
      (component ((EnrichedCoaugmentationTelescope.projection η (r + 1 + n)).app Y)
        (index m)).right =
    (component ((EnrichedCoaugmentationTelescope.projection η (r + 1 + n)).app X)
      (index m)).right ≫
      (component ((Functor.Iteration.iterate F (r + 1 + n)).map f)
        (index m)).right
  let a := index m
  let u := component ((EnrichedCoaugmentationTelescope.stage η (r + 1 + n)).functor.map f) a
  let v := component ((EnrichedCoaugmentationTelescope.projection η (r + 1 + n)).app Y) a
  let w := component ((EnrichedCoaugmentationTelescope.projection η (r + 1 + n)).app X) a
  let z := component ((Functor.Iteration.iterate F (r + 1 + n)).map f) a
  exact (PointedCGWH.pointedToCGWH.map_comp u v).symm.trans
    ((PointedCGWH.pointedToCGWH.congr_map
      (projection_component_input_square index η f m (r + 1 + n))).trans
      (PointedCGWH.pointedToCGWH.map_comp w z))

omit B in
/-- All original input maps commute with the complete positive raw-loop comparison. -/
theorem positiveRawLoopIso_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r : ℕ) :
    positiveRawMap index η f m r ≫ (positiveRawLoopIso index η step Y m r).hom =
      (positiveRawLoopIso index η step X m r).hom ≫
        Functor.whiskerRight (predecessorMap index η f m r) PointedCGWH.loop := by
  apply NatTrans.ext
  funext n
  change (level index m).map
      ((Functor.Iteration.iterate F (r + 1 + n)).map f) ≫
        (positiveRawLoopIso index η step Y m r).hom.app n =
      (positiveRawLoopIso index η step X m r).hom.app n ≫
        PointedCGWH.loop.map ((level index (m + 1)).map
          ((Functor.Iteration.iterate F (r + n)).map f))
  rw [positiveRawLoopIso_hom_app index, positiveRawLoopIso_hom_app index]
  exact (positiveStageIso index step m r n).hom.naturality f

omit B in
/-- Both inverse raw-loop maps retain the same complete original input-map square. -/
theorem positiveRawLoopIso_input_inv_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r : ℕ) :
    Functor.whiskerRight (predecessorMap index η f m r) PointedCGWH.loop ≫
        (positiveRawLoopIso index η step Y m r).inv =
      (positiveRawLoopIso index η step X m r).inv ≫ positiveRawMap index η f m r :=
  (CommSq.vert_inv (g := positiveRawLoopIso index η step X m r)
    (h := positiveRawLoopIso index η step Y m r)
    ⟨positiveRawLoopIso_input_naturality index η step f m r⟩).w

omit B in
/-- Every complete positive-tail ordered arrow is conjugate to the genuine predecessor loop map. -/
theorem positiveRawLoopIso_map_word (X : (Carrier.{u, v} (I := I))) (m r : ℕ)
    {i j : ℕ} (f : i ⟶ j) :
    (positiveRawDiagram index η X m r).map f =
      (positiveRawLoopIso index η step X m r).hom.app i ≫
        PointedCGWH.loop.map ((predecessorDiagram index η X m r).map f) ≫
          (positiveRawLoopIso index η step X m r).inv.app j := by
  have h := congrArg (fun g => g ≫ (positiveRawLoopIso index η step X m r).inv.app j)
    ((positiveRawLoopIso index η step X m r).hom.naturality f)
  have hi := (positiveRawLoopIso index η step X m r).hom_inv_id_app j
  have hLeft : ((positiveRawDiagram index η X m r).map f ≫
      (positiveRawLoopIso index η step X m r).hom.app j) ≫
        (positiveRawLoopIso index η step X m r).inv.app j =
      (positiveRawDiagram index η X m r).map f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => (positiveRawDiagram index η X m r).map f ≫ z) hi).trans
        (Category.comp_id _))
  exact hLeft.symm.trans (h.trans (Category.assoc _ _ _))

/-- The exact positive cylinder-stage point uses the original stage and the original level. -/
abbrev CylinderPoint (X : (Carrier.{u, v} (I := I))) (m r : ℕ) :=
  (((EnrichedCoaugmentationTelescope.stage η (r + 1)).functor.obj X).toEnrichedFunctor.obj
    (index m)).right

/-- The chosen raw point is the actual zero component of the original cylinder projection. -/
def projectedRawPoint (X : (Carrier.{u, v} (I := I))) (m r : ℕ) (p : CylinderPoint index η X m r) :
    ((positiveRawDiagram index η X m r).obj 0).right :=
  (EnrichedCoaugmentationTelescope.projectionTailUnderlying η X
    (index m) (r + 1)).app 0 p

/-- Every actual source point is carried by the entire original cylinder-stage map. -/
def stageImagePoint {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint index η X m r) : CylinderPoint index η Y m r :=
  (component ((EnrichedCoaugmentationTelescope.stage η (r + 1)).functor.map f)
    (index m)).right p

omit B in
/-- Its projected raw point is the exact original raw-map image, without a new choice. -/
theorem projectedRawPoint_image {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint index η X m r) :
    (rawUnderlyingMap index η f m r).app 0 (projectedRawPoint index η X m r p) =
      projectedRawPoint index η Y m r (stageImagePoint index η f m r p) := by
  let a := index m
  let u := component ((EnrichedCoaugmentationTelescope.stage η (r + 1)).functor.map f) a
  let v := component ((EnrichedCoaugmentationTelescope.projection η (r + 1)).app Y) a
  let w := component ((EnrichedCoaugmentationTelescope.projection η (r + 1)).app X) a
  let z := component ((Functor.Iteration.iterate F (r + 1)).map f) a
  have h := (PointedCGWH.pointedToCGWH.map_comp u v).symm.trans
    ((PointedCGWH.pointedToCGWH.congr_map
      (projection_component_input_square index η f m (r + 1))).trans
      (PointedCGWH.pointedToCGWH.map_comp w z))
  have h' := ConcreteCategory.congr_hom h p
  change (component ((Functor.Iteration.iterate F (r + 1)).map f)
      (index m)).right
        ((component ((EnrichedCoaugmentationTelescope.projection η (r + 1)).app X)
          (index m)).right p) =
    (component ((EnrichedCoaugmentationTelescope.projection η (r + 1)).app Y)
      (index m)).right
        ((component ((EnrichedCoaugmentationTelescope.stage η (r + 1)).functor.map f)
          (index m)).right p)
  exact h'.symm

/-- The full original raw-map diagram is based at the actual projection image points. -/
def rawBasedMap {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint index η X m r) :
    EnrichedCoaugmentationTelescope.iterationTailBasedDiagram η X
        (index m) (r + 1) p ⟶
      EnrichedCoaugmentationTelescope.iterationTailBasedDiagram η Y
        (index m) (r + 1) (stageImagePoint index η f m r p) :=
  basedDiagramMap (rawUnderlyingMap index η f m r)
    (projectedRawPoint index η X m r p)
    (projectedRawPoint index η Y m r (stageImagePoint index η f m r p))
    (projectedRawPoint_image index η f m r p)

omit B in
/-- Both original based input maps keep the same full projection square at every stage. -/
theorem basedTailProjection_input_square {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint index η X m r) :
    EnrichedCoaugmentationTelescope.basedTailMap η f
        (index m) (r + 1) p ≫
      EnrichedCoaugmentationTelescope.basedTailProjection η Y
        (index m) (r + 1) (stageImagePoint index η f m r p) =
      EnrichedCoaugmentationTelescope.basedTailProjection η X
        (index m) (r + 1) p ≫ rawBasedMap index η f m r p := by
  apply NatTrans.ext
  funext n
  apply PointedCGWH.pointedToCGWH.map_injective
  exact NatTrans.congr_app (projectionTailUnderlying_input_square index η f m r) n

/-- Each original raw-tail point is transported through the same complete raw input arrow. -/
def rawTailPoint (X : (Carrier.{u, v} (I := I))) (m r : ℕ)
    (p : CylinderPoint index η X m r) (n : ℕ) :
    ((positiveRawDiagram index η X m r).obj n).right :=
  PointedCGWH.PointedAtGeometry.diagramPoint
    (positiveRawDiagram index η X m r ⋙ PointedCGWH.pointedToCGWH)
    (projectedRawPoint index η X m r p) n

omit B in
/-- Projection of every actual cylinder-tail point is exactly its original raw-tail point. -/
theorem projected_rawTailPoint (X : (Carrier.{u, v} (I := I))) (m r n : ℕ)
    (p : CylinderPoint index η X m r) :
    (EnrichedCoaugmentationTelescope.projectionTailUnderlying η X
      (index m) (r + 1)).app n
      (PointedCGWH.PointedAtGeometry.diagramPoint
        (NatTail.tailFunctor (r + 1) ⋙
          (EnrichedCoaugmentationTelescope.evaluatedDiagram η X
            (index m) ⋙ PointedCGWH.pointedToCGWH)) p n) =
      rawTailPoint index η X m r p n :=
  PointedCGWH.PointedAtGeometry.diagramPoint_map
    (EnrichedCoaugmentationTelescope.projectionTailUnderlying η X
      (index m) (r + 1)) p n

/-- Both actual raw-loop comparison functions retain all original underlying carrier maps. -/
def underlyingRawLoopIso (X : (Carrier.{u, v} (I := I))) (m r : ℕ) :
    positiveRawDiagram index η X m r ⋙ PointedCGWH.pointedToCGWH ≅
      (predecessorDiagram index η X m r ⋙ PointedCGWH.loop) ⋙ PointedCGWH.pointedToCGWH :=
  Functor.isoWhiskerRight (positiveRawLoopIso index η step X m r) PointedCGWH.pointedToCGWH

omit B in
/-- Every original input map preserves both whole underlying raw-loop comparisons. -/
theorem underlyingRawLoopIso_input_square {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r : ℕ) :
    rawUnderlyingMap index η f m r ≫ (underlyingRawLoopIso index η step Y m r).hom =
      (underlyingRawLoopIso index η step X m r).hom ≫
        Functor.whiskerRight (Functor.whiskerRight (predecessorMap index η f m r) PointedCGWH.loop)
          PointedCGWH.pointedToCGWH := by
  apply NatTrans.ext
  funext n
  change PointedCGWH.pointedToCGWH.map ((positiveRawMap index η f m r).app n) ≫
      PointedCGWH.pointedToCGWH.map ((positiveRawLoopIso index η step Y m r).hom.app n) =
    PointedCGWH.pointedToCGWH.map ((positiveRawLoopIso index η step X m r).hom.app n) ≫
      PointedCGWH.pointedToCGWH.map
        (PointedCGWH.loop.map ((predecessorMap index η f m r).app n))
  let u := (positiveRawMap index η f m r).app n
  let v := (positiveRawLoopIso index η step Y m r).hom.app n
  let w := (positiveRawLoopIso index η step X m r).hom.app n
  let z := PointedCGWH.loop.map ((predecessorMap index η f m r).app n)
  have h : u ≫ v = w ≫ z :=
    NatTrans.congr_app (positiveRawLoopIso_input_naturality index η step f m r) n
  exact (PointedCGWH.pointedToCGWH.map_comp u v).symm.trans
    ((PointedCGWH.pointedToCGWH.congr_map h).trans
      (PointedCGWH.pointedToCGWH.map_comp w z))

/-- The actual predecessor-loop point is the image of the original projected zero-stage point. -/
def predecessorLoopPoint (X : (Carrier.{u, v} (I := I))) (m r : ℕ)
    (p : CylinderPoint index η X m r) :
    (PointedCGWH.loop.obj ((predecessorDiagram index η X m r).obj 0)).right :=
  (underlyingRawLoopIso index η step X m r).hom.app 0 (projectedRawPoint index η X m r p)

omit B in
/-- Every raw-tail point follows the same actual predecessor loop-map point transport. -/
theorem rawTailPoint_loop_image (X : (Carrier.{u, v} (I := I))) (m r n : ℕ)
    (p : CylinderPoint index η X m r) :
    (underlyingRawLoopIso index η step X m r).hom.app n (rawTailPoint index η X m r p n) =
      loopDiagramPoint (predecessorDiagram index η X m r)
        (predecessorLoopPoint index η step X m r p) n :=
  PointedCGWH.PointedAtGeometry.diagramPoint_map
    (underlyingRawLoopIso index η step X m r).hom (projectedRawPoint index η X m r p) n

/-- Both all-degree raw comparisons are built at the actual projection image point. -/
def rawTailTypeIso (X : (Carrier.{u, v} (I := I))) (m r k : ℕ) (p : CylinderPoint index η X m r) :
    EnrichedCoaugmentationTelescope.iterationTailBasedDiagram η X
        (index m) (r + 1) p ⋙ PointedCGWH.piNFunctor k ≅
      predecessorDiagram index η X m r ⋙ PointedCGWH.piNFunctor (k + 1) :=
  loopIsoTypeComparison (underlyingRawLoopIso index η step X m r)
    (projectedRawPoint index η X m r p) k

omit B in
/-- The full arbitrary-point raw-tail comparisons are natural on every original input arrow. -/
theorem rawTailTypeIso_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r k : ℕ)
    (p : CylinderPoint index η X m r) :
    Functor.whiskerRight (rawBasedMap index η f m r p) (PointedCGWH.piNFunctor k) ≫
        (rawTailTypeIso index η step Y m r k (stageImagePoint index η f m r p)).hom =
      (rawTailTypeIso index η step X m r k p).hom ≫
        Functor.whiskerRight (predecessorMap index η f m r) (PointedCGWH.piNFunctor (k + 1)) :=
  loopIsoTypeComparison_input_naturality
    (underlyingRawLoopIso index η step X m r) (underlyingRawLoopIso index η step Y m r)
    (rawUnderlyingMap index η f m r) (predecessorMap index η f m r)
    (underlyingRawLoopIso_input_square index η step f m r)
    (projectedRawPoint index η X m r p)
    (projectedRawPoint index η Y m r (stageImagePoint index η f m r p))
    (projectedRawPoint_image index η f m r p) k

/-- Original cylinder projection Type maps preserve the exact input and image-point square. -/
theorem basedTailProjectionTypeIso_input_naturality {X Y : (Carrier.{u, v} (I := I))}
    (f : X ⟶ Y) (m r k : ℕ) (p : CylinderPoint index η X m r) :
    Functor.whiskerRight
        (EnrichedCoaugmentationTelescope.basedTailMap η f
          (index m) (r + 1) p) (PointedCGWH.piNFunctor k) ≫
      (EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso η Y
        (index m) (r + 1) k
          (stageImagePoint index η f m r p)).hom =
      (EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso η X
        (index m) (r + 1) k p).hom ≫
        Functor.whiskerRight (rawBasedMap index η f m r p) (PointedCGWH.piNFunctor k) := by
  rw [EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso_hom,
    EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso_hom]
  apply NatTrans.ext
  funext n
  let a := index m
  let pY := stageImagePoint index η f m r p
  let u := (EnrichedCoaugmentationTelescope.basedTailMap η f a (r + 1) p).app n
  let v := (EnrichedCoaugmentationTelescope.basedTailProjection η Y a (r + 1) pY).app n
  let w := (EnrichedCoaugmentationTelescope.basedTailProjection η X a (r + 1) p).app n
  let z := (rawBasedMap index η f m r p).app n
  have h : u ≫ v = w ≫ z := NatTrans.congr_app (basedTailProjection_input_square index η f m r p) n
  exact ((PointedCGWH.piNFunctor k).map_comp u v).symm.trans
    (((PointedCGWH.piNFunctor k).congr_map h).trans
      ((PointedCGWH.piNFunctor k).map_comp w z))

/--
The complete cylinder comparison retains its actual projection followed by the original loop
shift.
-/
def cylinderTailTypeIso (X : (Carrier.{u, v} (I := I))) (m r k : ℕ)
    (p : CylinderPoint index η X m r) :
    EnrichedCoaugmentationTelescope.basedTailDiagram η X
        (index m) (r + 1) p ⋙ PointedCGWH.piNFunctor k ≅
      predecessorDiagram index η X m r ⋙ PointedCGWH.piNFunctor (k + 1) :=
  EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso η X
    (index m) (r + 1) k p ≪≫
      rawTailTypeIso index η step X m r k p

/-- Every complete original cylinder input map preserves the two actual Type comparison factors. -/
theorem cylinderTailTypeIso_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r) :
    Functor.whiskerRight
        (EnrichedCoaugmentationTelescope.basedTailMap η f
          (index m) (r + 1) p) (PointedCGWH.piNFunctor k) ≫
      (cylinderTailTypeIso index η step Y m r k (stageImagePoint index η f m r p)).hom =
      (cylinderTailTypeIso index η step X m r k p).hom ≫
        Functor.whiskerRight (predecessorMap index η f m r) (PointedCGWH.piNFunctor (k + 1)) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫
      (rawTailTypeIso index η step Y m r k (stageImagePoint index η f m r p)).hom)
      (basedTailProjectionTypeIso_input_naturality index η f m r k p)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z =>
          (EnrichedCoaugmentationTelescope.basedTailProjectionTypeIso η X
            (index m) (r + 1) k p).hom ≫ z)
          (rawTailTypeIso_input_naturality index η step f m r k p)).trans
          (Category.assoc _ _ _).symm)))

/-- The explicit original associator aligns the predecessor pi diagram with the literal tail. -/
def predecessorPiTailIso (X : (Carrier.{u, v} (I := I))) (m r k : ℕ) :
    predecessorDiagram index η X m r ⋙ PointedCGWH.piNFunctor (k + 1) ≅
      NatTail.tailFunctor r ⋙
        ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
          PointedCGWH.piNFunctor (k + 1)) :=
  Functor.associator (NatTail.tailFunctor r)
    (Functor.Iteration.inputDiagram η X ⋙ level index (m + 1))
    (PointedCGWH.piNFunctor (k + 1))

omit B in
/-- Every forward predecessor/tail component is the same actual original pi object identity. -/
theorem predecessorPiTailIso_hom_app (X : (Carrier.{u, v} (I := I))) (m r k n : ℕ) :
    (predecessorPiTailIso index η X m r k).hom.app n =
      𝟙 ((PointedCGWH.piNFunctor (k + 1)).obj
        ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)).obj (r + n))) := rfl

omit B in
/-- Its original input square retains all actual predecessor and full tail maps. -/
theorem predecessorPiTailIso_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) :
    Functor.whiskerRight (predecessorMap index η f m r) (PointedCGWH.piNFunctor (k + 1)) ≫
        (predecessorPiTailIso index η Y m r k).hom =
      (predecessorPiTailIso index η X m r k).hom ≫
        Functor.whiskerLeft (NatTail.tailFunctor r)
          (Functor.whiskerRight
            (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
              (level index (m + 1))) (PointedCGWH.piNFunctor (k + 1))) := by
  apply NatTrans.ext
  funext n
  change (PointedCGWH.piNFunctor (k + 1)).map
      ((level index (m + 1)).map
        ((Functor.Iteration.iterate F (r + n)).map f)) ≫ 𝟙 _ =
    𝟙 _ ≫ (PointedCGWH.piNFunctor (k + 1)).map
      ((level index (m + 1)).map
        ((Functor.Iteration.iterate F (r + n)).map f))
  rw [Category.comp_id, Category.id_comp]

/-- Both full original cylinder comparisons land in the literal cofinal tail diagram. -/
def completedCylinderTailTypeIso (X : (Carrier.{u, v} (I := I))) (m r k : ℕ)
    (p : CylinderPoint index η X m r) :
    EnrichedCoaugmentationTelescope.basedTailDiagram η X
        (index m) (r + 1) p ⋙ PointedCGWH.piNFunctor k ≅
      NatTail.tailFunctor r ⋙
        ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
          PointedCGWH.piNFunctor (k + 1)) :=
  cylinderTailTypeIso index η step X m r k p ≪≫ predecessorPiTailIso index η X m r k

/-- The associator changes no original forward stage component of the complete comparison. -/
theorem completedCylinderTailTypeIso_hom_app (X : (Carrier.{u, v} (I := I))) (m r k n : ℕ)
    (p : CylinderPoint index η X m r) :
    (completedCylinderTailTypeIso index η step X m r k p).hom.app n =
      (cylinderTailTypeIso index η step X m r k p).hom.app n := by
  change (cylinderTailTypeIso index η step X m r k p).hom.app n ≫ _ = _
  exact (congrArg (fun z => (cylinderTailTypeIso index η step X m r k p).hom.app n ≫ z)
    (predecessorPiTailIso_hom_app index η X m r k n)).trans
      (Category.comp_id ((cylinderTailTypeIso index η step X m r k p).hom.app n))

/-- All original input maps retain the complete literal cylinder/tail comparison square. -/
theorem completedCylinderTailTypeIso_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r) :
    Functor.whiskerRight
        (EnrichedCoaugmentationTelescope.basedTailMap η f
          (index m) (r + 1) p) (PointedCGWH.piNFunctor k) ≫
      (completedCylinderTailTypeIso index η step Y m r k (stageImagePoint index η f m r p)).hom =
      (completedCylinderTailTypeIso index η step X m r k p).hom ≫
        Functor.whiskerLeft (NatTail.tailFunctor r)
          (Functor.whiskerRight
            (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
              (level index (m + 1))) (PointedCGWH.piNFunctor (k + 1))) := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (predecessorPiTailIso index η Y m r k).hom)
      (cylinderTailTypeIso_input_naturality index η step f m r k p)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (cylinderTailTypeIso index η step X m r k p).hom ≫ z)
          (predecessorPiTailIso_input_naturality index η f m r k)).trans
          (Category.assoc _ _ _).symm)))

/-- The physical telescope point is the image under the original positive-stage colimit leg. -/
abbrev PhysicalPoint (X : (Carrier.{u, v} (I := I))) (m r : ℕ) (p : CylinderPoint index η X m r) :=
  (EnrichedCoaugmentationTelescope.basedTailCocone η X
    (index m) (r + 1) p).pt

/--
Both physical-point comparison maps retain the original closed-cylinder and actual final-tail
cocones.
-/
def physicalTypeIso (X : (Carrier.{u, v} (I := I))) (m r k : ℕ) (p : CylinderPoint index η X m r) :
    (PointedCGWH.piNFunctor k).obj (PhysicalPoint index η X m r p) ≅
      colimit ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
        PointedCGWH.piNFunctor (k + 1)) :=
  (EnrichedCoaugmentationTelescope.basedTailTypeIso η X
      (index m) (r + 1) k p).symm ≪≫
    colim.mapIso (completedCylinderTailTypeIso index η step X m r k p) ≪≫
    NatTail.typeTailIso
      ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
        PointedCGWH.piNFunctor (k + 1)) r

/-- The physical-point map is the original telescope map with its actual image point. -/
def physicalMap {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint index η X m r) :
    PhysicalPoint index η X m r p ⟶ PhysicalPoint index η Y m r (stageImagePoint index η f m r p) :=
  EnrichedCoaugmentationTelescope.basedTailCoconeMap η f
    (index m) (r + 1) p

/-- All original physical input points retain the complete telescope/raw predecessor square. -/
theorem physicalTypeIso_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r) :
    (PointedCGWH.piNFunctor k).map (physicalMap index η f m r p) ≫
        (physicalTypeIso index η step Y m r k (stageImagePoint index η f m r p)).hom =
      (physicalTypeIso index η step X m r k p).hom ≫
        colim.map (Functor.whiskerRight
          (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
            (level index (m + 1)))
          (PointedCGWH.piNFunctor (k + 1))) := by
  let a := index m
  let pY := stageImagePoint index η f m r p
  let xT := (EnrichedCoaugmentationTelescope.basedTailTypeIso η X a (r + 1) k p).inv
  let yT := (EnrichedCoaugmentationTelescope.basedTailTypeIso η Y a (r + 1) k pY).inv
  let xC := colim.map (completedCylinderTailTypeIso index η step X m r k p).hom
  let yC := colim.map (completedCylinderTailTypeIso index η step Y m r k pY).hom
  let bC := colim.map (Functor.whiskerRight
    (EnrichedCoaugmentationTelescope.basedTailMap η f a (r + 1) p) (PointedCGWH.piNFunctor k))
  let β := Functor.whiskerRight
    (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
    (PointedCGWH.piNFunctor (k + 1))
  let βF := colim.map β
  let βT := colim.map (Functor.whiskerLeft (NatTail.tailFunctor r) β)
  let xTail := (NatTail.typeTailIso
    ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
      PointedCGWH.piNFunctor (k + 1)) r).hom
  let yTail := (NatTail.typeTailIso
    ((Functor.Iteration.inputDiagram η Y ⋙ level index (m + 1)) ⋙
      PointedCGWH.piNFunctor (k + 1)) r).hom
  let tF := (PointedCGWH.piNFunctor k).map (physicalMap index η f m r p)
  have h1 : tF ≫ yT = xT ≫ bC :=
    EnrichedCoaugmentationTelescope.basedTailTypeIso_inv_naturality η f a (r + 1) k p
  have h2 : bC ≫ yC = xC ≫ βT := by
    let u := Functor.whiskerRight
      (EnrichedCoaugmentationTelescope.basedTailMap η f a (r + 1) p) (PointedCGWH.piNFunctor k)
    let v := (completedCylinderTailTypeIso index η step Y m r k pY).hom
    let w := (completedCylinderTailTypeIso index η step X m r k p).hom
    let z := Functor.whiskerLeft (NatTail.tailFunctor r) β
    have h : u ≫ v = w ≫ z := completedCylinderTailTypeIso_input_naturality index η step f m r k p
    exact (colim.map_comp u v).symm.trans
      ((colim.congr_map h).trans (colim.map_comp w z))
  have h3 : βT ≫ yTail = xTail ≫ βF := NatTail.typeTailIso_hom_naturality r β
  change tF ≫ (yT ≫ (yC ≫ yTail)) = (xT ≫ (xC ≫ xTail)) ≫ βF
  calc
    tF ≫ (yT ≫ (yC ≫ yTail)) = (tF ≫ yT) ≫ (yC ≫ yTail) :=
      (Category.assoc _ _ _).symm
    _ = (xT ≫ bC) ≫ (yC ≫ yTail) := congrArg (fun z => z ≫ (yC ≫ yTail)) h1
    _ = xT ≫ ((bC ≫ yC) ≫ yTail) :=
      (Category.assoc xT bC (yC ≫ yTail)).trans
        (congrArg (fun z => xT ≫ z) (Category.assoc bC yC yTail).symm)
    _ = xT ≫ ((xC ≫ βT) ≫ yTail) := congrArg (fun z => xT ≫ (z ≫ yTail)) h2
    _ = xT ≫ (xC ≫ (βT ≫ yTail)) := congrArg (fun z => xT ≫ z) (Category.assoc _ _ _)
    _ = xT ≫ (xC ≫ (xTail ≫ βF)) := congrArg (fun z => xT ≫ (xC ≫ z)) h3
    _ = (xT ≫ (xC ≫ xTail)) ≫ βF :=
      (congrArg (fun z => xT ≫ z) (Category.assoc xC xTail βF).symm).trans
        (Category.assoc xT (xC ≫ xTail) βF).symm

/-- Both inverse physical comparisons keep the same full original input-map square. -/
theorem physicalTypeIso_inv_input_naturality {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r) :
    colim.map (Functor.whiskerRight
        (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
        (PointedCGWH.piNFunctor (k + 1))) ≫
      (physicalTypeIso index η step Y m r k (stageImagePoint index η f m r p)).inv =
      (physicalTypeIso index η step X m r k p).inv ≫
        (PointedCGWH.piNFunctor k).map (physicalMap index η f m r p) :=
  (CommSq.vert_inv (g := physicalTypeIso index η step X m r k p)
    (h := physicalTypeIso index η step Y m r k (stageImagePoint index η f m r p))
      ⟨physicalTypeIso_input_naturality index η step f m r k p⟩).w

/--
The actual physical-point homotopy map is the original raw map conjugated by both comparisons.
-/
theorem physicalMap_pi_word {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r) :
    (PointedCGWH.piNFunctor k).map (physicalMap index η f m r p) =
      (physicalTypeIso index η step X m r k p).hom ≫
        colim.map (Functor.whiskerRight
          (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f)
            (level index (m + 1)))
          (PointedCGWH.piNFunctor (k + 1))) ≫
        (physicalTypeIso index η step Y m r k (stageImagePoint index η f m r p)).inv := by
  apply (cancel_mono (physicalTypeIso index η step Y m r k (stageImagePoint index η f m r p)).hom).1
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact physicalTypeIso_input_naturality index η step f m r k p

include step in
/-- An isomorphism of the original raw predecessor colimit map gives the actual all-point pi map. -/
theorem physicalMap_pi_isIso_of_raw {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r)
    (h : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    IsIso ((PointedCGWH.piNFunctor k).map (physicalMap index η f m r p)) := by
  rw [physicalMap_pi_word index η step f m r k p]
  let _ : IsIso (colim.map (Functor.whiskerRight
    (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
    (PointedCGWH.piNFunctor (k + 1)))) := h
  infer_instance

include step in
/--
Both actual physical-point homotopy functions are bijective from the original raw colimit map.
-/
theorem physicalMap_pi_bijective_of_raw {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m r k : ℕ) (p : CylinderPoint index η X m r)
    (h : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    Function.Bijective ((PointedCGWH.piNFunctor k).map (physicalMap index η f m r p)) :=
  (CategoryTheory.isIso_iff_bijective _).mp
    (physicalMap_pi_isIso_of_raw index η step f m r k p h)

/--
Every actual stage leg retains the complete forward physical comparison and selected
predecessor leg.
-/
theorem physicalTypeIso_hom_leg (X : (Carrier.{u, v} (I := I))) (m r k n : ℕ)
    (p : CylinderPoint index η X m r) :
    (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone η X
          (index m) (r + 1) p).ι.app n) ≫
      (physicalTypeIso index η step X m r k p).hom =
        (cylinderTailTypeIso index η step X m r k p).hom.app n ≫
          colimit.ι
            ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
              PointedCGWH.piNFunctor (k + 1)) (r + n) := by
  let D := EnrichedCoaugmentationTelescope.basedTailDiagram η X
    (index m) (r + 1) p ⋙ PointedCGWH.piNFunctor k
  rw [← completedCylinderTailTypeIso_hom_app index η step X m r k n p]
  let T := completedCylinderTailTypeIso index η step X m r k p
  let E := (Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
    PointedCGWH.piNFunctor (k + 1)
  change _ ≫
    (EnrichedCoaugmentationTelescope.basedTailTypeIso η X
      (index m) (r + 1) k p).inv ≫
      colim.map T.hom ≫ (NatTail.typeTailIso E r).hom =
    T.hom.app n ≫ colimit.ι E (r + n)
  have h0 := EnrichedCoaugmentationTelescope.basedTailTypeIso_inv_leg η X
    (index m) (r + 1) k n p
  have h1 := colimit.ι_map T.hom n
  calc
    _ = ((PointedCGWH.piNFunctor k).map
          ((EnrichedCoaugmentationTelescope.basedTailCocone η X
            (index m) (r + 1) p).ι.app n) ≫
        (EnrichedCoaugmentationTelescope.basedTailTypeIso η X
          (index m) (r + 1) k p).inv) ≫
          colim.map T.hom ≫ (NatTail.typeTailIso E r).hom := by simp only [Category.assoc]
    _ = colimit.ι D n ≫ colim.map T.hom ≫ (NatTail.typeTailIso E r).hom := by rw [h0]
    _ = T.hom.app n ≫ colimit.ι (NatTail.tailFunctor r ⋙ E) n ≫
        (NatTail.typeTailIso E r).hom := (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (NatTail.typeTailIso E r).hom) h1).trans
            (Category.assoc _ _ _))
    _ = T.hom.app n ≫ colimit.ι E (r + n) :=
      congrArg (fun z => T.hom.app n ≫ z) (NatTail.typeTailIso_hom_ι E r n)

/--
Every inverse physical comparison retains the same literal cylinder leg and predecessor index.
-/
theorem physicalTypeIso_inv_leg (X : (Carrier.{u, v} (I := I))) (m r k n : ℕ)
    (p : CylinderPoint index η X m r) :
    (cylinderTailTypeIso index η step X m r k p).hom.app n ≫
        colimit.ι
          ((Functor.Iteration.inputDiagram η X ⋙ level index (m + 1)) ⋙
            PointedCGWH.piNFunctor (k + 1)) (r + n) ≫
          (physicalTypeIso index η step X m r k p).inv =
      (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone η X
          (index m) (r + 1) p).ι.app n) := by
  have h := congrArg (fun z => z ≫ (physicalTypeIso index η step X m r k p).inv)
    (physicalTypeIso_hom_leg index η step X m r k n p)
  have hLeft : ((PointedCGWH.piNFunctor k).map
      ((EnrichedCoaugmentationTelescope.basedTailCocone η X
        (index m) (r + 1) p).ι.app n) ≫
      (physicalTypeIso index η step X m r k p).hom) ≫ (physicalTypeIso index η step X m r k p).inv =
      (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone η X
          (index m) (r + 1) p).ι.app n) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => (PointedCGWH.piNFunctor k).map
        ((EnrichedCoaugmentationTelescope.basedTailCocone η X
          (index m) (r + 1) p).ι.app n) ≫ z)
        (physicalTypeIso index η step X m r k p).hom_inv_id).trans (Category.comp_id _))
  exact h.symm.trans hLeft

omit B in
/--
Every physical telescope point has an original positive-stage representative after any
requested bound.
-/
theorem exists_positive_stage_point_after (X : (Carrier.{u, v} (I := I))) (m n₀ : ℕ)
    (x : ((EnrichedCoaugmentationTelescope.telescope η X).toEnrichedFunctor.obj
      (index m)).right) :
    ∃ (r : ℕ), n₀ ≤ r + 1 ∧
      ∃ p : CylinderPoint index η X m r,
        (component (EnrichedCoaugmentationTelescope.leg η X (r + 1))
          (index m)).right p = x := by
  obtain ⟨n, hn, p, hp⟩ :=
    EnrichedCoaugmentationTelescope.exists_stage_point_after η X
      (index m) x (n₀ + 1)
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero n₀ hn)
  | succ r => exact ⟨r, Nat.le_trans (Nat.le_succ n₀) hn, p, hp⟩

omit B in
/-- Each physical-point comparison uses the entire original evaluated telescope map. -/
theorem physicalMap_right {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y) (m r : ℕ)
    (p : CylinderPoint index η X m r) :
    (physicalMap index η f m r p).right =
      (component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
        (index m)).right :=
  EnrichedCoaugmentationTelescope.basedTailCoconeMap_right η f
    (index m) (r + 1) p

include step in
/-- An original raw colimit isomorphism gives the pi map at every physical telescope point. -/
theorem telescopeMap_point_pi_isIso_of_raw {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (m k : ℕ)
    (x : (((EnrichedCoaugmentationTelescope.telescopeFunctor η).obj X).toEnrichedFunctor.obj
      (index m)).right)
    (hRaw : IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    IsIso ((PointedCGWH.piNFunctor k).map (PointedCGWH.pointedAtMap
      (component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
        (index m)).right x
      ((component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
        (index m)).right x) rfl)) := by
  obtain ⟨r, _, p, hx⟩ := exists_positive_stage_point_after index η X m 0 x
  let a := index m
  let A := ((EnrichedCoaugmentationTelescope.telescopeFunctor η).obj X).toEnrichedFunctor.obj a
  let D := ((EnrichedCoaugmentationTelescope.telescopeFunctor η).obj Y).toEnrichedFunctor.obj a
  let t := component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f) a
  let pY := stageImagePoint index η f m r p
  let xP := (component (EnrichedCoaugmentationTelescope.leg η X (r + 1)) a).right p
  let yP := (component (EnrichedCoaugmentationTelescope.leg η Y (r + 1)) a).right pY
  have hImage : t.right x = yP := by
    have hn := ConcreteCategory.congr_hom
      (PointedCGWH.pointedToCGWH.congr_map
        (EnrichedCoaugmentationTelescope.evaluatedCocone_naturality η f a (r + 1))) p
    exact (congrArg t.right hx).symm.trans hn
  let eX : PointedCGWH.pointedAt A.right x ≅ PhysicalPoint index η X m r p :=
    carrierPointIso (Iso.refl A.right) x xP hx.symm
  let eY : PointedCGWH.pointedAt D.right (t.right x) ≅ PhysicalPoint index η Y m r pY :=
    carrierPointIso (Iso.refl D.right) (t.right x) yP hImage
  let g := PointedCGWH.pointedAtMap t.right x (t.right x) rfl
  have hs : g ≫ eY.hom = eX.hom ≫ physicalMap index η f m r p := by
    apply PointedCGWH.pointedToCGWH.map_injective
    change t.right ≫ 𝟙 D.right = 𝟙 A.right ≫ (physicalMap index η f m r p).right
    exact (Category.comp_id t.right).trans
      ((Category.id_comp t.right).symm.trans
        (congrArg (fun z => 𝟙 A.right ≫ z) (physicalMap_right index η f m r p).symm))
  let iX := (PointedCGWH.piNFunctor k).mapIso eX
  let iY := (PointedCGWH.piNFunctor k).mapIso eY
  have hπ : (PointedCGWH.piNFunctor k).map g ≫ iY.hom =
      iX.hom ≫ (PointedCGWH.piNFunctor k).map (physicalMap index η f m r p) := by
    exact ((PointedCGWH.piNFunctor k).map_comp g eY.hom).symm.trans
      (((PointedCGWH.piNFunctor k).congr_map hs).trans
        ((PointedCGWH.piNFunctor k).map_comp eX.hom (physicalMap index η f m r p)))
  have hWord : (PointedCGWH.piNFunctor k).map g =
      iX.hom ≫ (PointedCGWH.piNFunctor k).map (physicalMap index η f m r p) ≫ iY.inv := by
    have hh := congrArg (fun z => z ≫ iY.inv) hπ
    have hLeft : ((PointedCGWH.piNFunctor k).map g ≫ iY.hom) ≫ iY.inv =
        (PointedCGWH.piNFunctor k).map g :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => (PointedCGWH.piNFunctor k).map g ≫ z) iY.hom_inv_id).trans
          (Category.comp_id _))
    exact hLeft.symm.trans (hh.trans (Category.assoc _ _ _))
  let _ : IsIso ((PointedCGWH.piNFunctor k).map (physicalMap index η f m r p)) :=
    physicalMap_pi_isIso_of_raw index η step f m r k p hRaw
  change IsIso ((PointedCGWH.piNFunctor k).map g)
  rw [hWord]
  infer_instance

include step in
/-- The full original raw predecessor pi maps detect the actual telescope's level weak class. -/
theorem telescopeMap_weak_of_raw_colimit_isIso (hIndex : Function.Surjective index)
    {X Y : (Carrier.{u, v} (I := I))} (f : X ⟶ Y)
    (hRaw : ∀ m k : ℕ, IsIso (colim.map (Functor.whiskerRight
      (Functor.whiskerRight (Functor.Iteration.inputDiagramMap η f) (level index (m + 1)))
      (PointedCGWH.piNFunctor (k + 1))))) :
    weakEquivalences (Carrier.{u, v} (I := I))
      ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f) := by
  rw [EnrichedCoaugmentationTelescope.weakEquivalences_iff_components]
  intro a
  obtain ⟨m, rfl⟩ := hIndex a
  let A := ((EnrichedCoaugmentationTelescope.telescopeFunctor η).obj X).toEnrichedFunctor.obj
    (index m)
  let t := component ((EnrichedCoaugmentationTelescope.telescopeFunctor η).map f)
    (index m)
  let x := PointedCGWH.basepoint A
  let g := PointedCGWH.pointedAtMap t.right x (t.right x) rfl
  have h0 : Function.Bijective (PointedCGWH.piNMap 0 g) :=
    (CategoryTheory.isIso_iff_bijective _).mp
      (telescopeMap_point_pi_isIso_of_raw index η step f m 0 x (hRaw m 0))
  have hπ : ∀ (z : (PointedCGWH.pointedAt A.right x).right) (n : ℕ),
      Function.Bijective (PointedCGWH.piNMap (n + 1)
        (PointedCGWH.pointedAtMap g.right z (g.right z) rfl)) := by
    intro z n
    exact (CategoryTheory.isIso_iff_bijective _).mp
      (telescopeMap_point_pi_isIso_of_raw index η step f m (n + 1) z (hRaw m (n + 1)))
  exact PointedCGWH.NativeAllPointWeakDetectionGeometry.weak_of_component_and_all_point_pi g h0 hπ

end NativeOriginalLoop

section ActualIndexPresentations

/-- The actual original sequential dimension is the original degree object. -/
abbrev sequentialIndex (n : ℕ) :
    CategoryTheory.SequentialSpectrum.EnrichedIndex.Index PointedCGWH.sphereOne.{u, v} :=
  CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n

/-- Every original sequential index is its actual degree object. -/
theorem sequentialIndex_surjective : Function.Surjective sequentialIndex.{u, v} := by
  intro a
  exact ⟨a.degree, rfl⟩

/-- The actual symmetric object retains the complete original finite-index copower tag. -/
abbrev symmetricIndex (n : ℕ) : PointedCGWH.SymmetricOperatorIndex.{u, v} :=
  PointedCGWH.symmetricOperatorObj ⟨FintypeCat.Skeleton.mk n⟩

/-- Every original symmetric operator object is its actual finite dimension object. -/
theorem symmetricIndex_surjective : Function.Surjective symmetricIndex.{u, v} := by
  rintro ⟨⟨⟨a⟩⟩⟩
  exact ⟨a, rfl⟩

/-- The original orthogonal dimension keeps its actual full operator tag. -/
abbrev orthogonalIndex (n : ℕ) : OrthogonalOperatorIndex.{u, v} :=
  OrthogonalOperatorIndex.ofIndex n

/-- Every original orthogonal operator object is its actual dimension object. -/
theorem orthogonalIndex_surjective : Function.Surjective orthogonalIndex.{u, v} := by
  rintro ⟨a⟩
  exact ⟨a, rfl⟩

end ActualIndexPresentations

end HomotopicalAlgebra.EnrichedProjective.Native.LoopTailAllPointComparison
