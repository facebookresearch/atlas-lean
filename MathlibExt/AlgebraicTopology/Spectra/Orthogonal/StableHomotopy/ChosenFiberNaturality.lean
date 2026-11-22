/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerFiberNaturality

/-!
# Original connecting morphisms and arbitrary chosen orthogonal fiber maps

The same original Arrow square acts on the caller's unchanged native chosen
fiber. Every actual singular comparison, positive group comparison and
original group quotient square is retained. The connecting map is natural
through those whole comparisons in every integer degree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.ChosenFiberNaturality

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
  OrthogonalIntegerHomotopy
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.FiberGeometry
open PointedCGWH.Spectra.Orthogonal.ChosenFiberTransport
open PointedCGWH.Spectra.Orthogonal.ChosenFiberTests
open PointedCGWH.Spectra.Orthogonal.IntegerFiberNaturality
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedLevelSequences
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupSequence
open PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedGroupComparison
open PointedCGWH.SequentialSpectrum.StableHomotopy.DiagonalFiberSequence
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIterationHomotopyGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.CubeSingularGeometry
open PointedCGWH.SingularHomotopyGeometry
  (singularFunctor singularPoint_naturality)
open SSet.FibrationSequence.Geometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev C := OrthogonalCarrier.{u, v}
private abbrev iterate (n : ℕ) := PointedCGWH.SequentialSpectrum.OrderedLoop.iterate.{u, v} n
private abbrev evaluation (m : ℕ) := PointedCGWH.SequentialSpectrum.evaluation.{u, v} m

variable {X Y X' Y' : C.{u, v}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c)
  (d : PullbackCone p' (Diagrams.zeroTo Y')) (hd : IsLimit d)
  (hp : (NativeK.generators orthogonalFamily).rlp p)
  (hp' : (NativeK.generators orthogonalFamily).rlp p')

private abbrev fiberIso (n m : ℕ) :=
  chosenLoopedSequenceFiberIso (underlyingSequential.map p) (originalLevelFibrations p hp) m
    (underlyingChosenCone p c) (underlyingChosenConeIsLimit p c hc) n

/-- The actual singular chosen-fiber comparison retains the entire
original native Arrow square and its caller's chosen fiber map. -/
theorem chosenSequenceFiberIso_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    singularFunctor.map ((evaluation m).map ((iterate n).map
        (underlyingSequential.map (chosenFiberMap q c d hd)))) ≫
        (fiberIso d hd hp' n m).hom =
      (fiberIso c hc hp n m).hom ≫ (sequenceMap hp hp' q n m).fiberMap := by
  let F : C.{u, v} ⥤ PointedCGWH.{u, v} :=
    underlyingSequential ⋙ iterate n ⋙ evaluation m
  have h : F.map (chosenFiberMap q c d hd) ≫ F.map d.fst =
      F.map c.fst ≫ F.map q.left :=
    (F.map_comp _ _).symm.trans
      ((F.congr_map (chosenFiberMap_fst q c d hd)).trans (F.map_comp _ _))
  apply (cancel_mono
    (iterationLevelSerreSequence (underlyingSequential.map p')
      (originalLevelFibrations p' hp') n m).fiberIncl).mp
  rw [Category.assoc, chosenLoopedSequenceFiberIso_hom_projection,
    Category.assoc, SSet.FibrationSequenceHom.fiberMap_ι, ← Category.assoc,
    chosenLoopedSequenceFiberIso_hom_projection]
  change singularFunctor.map (F.map (chosenFiberMap q c d hd)) ≫
      singularFunctor.map (F.map d.fst) =
    singularFunctor.map (F.map c.fst) ≫ singularFunctor.map (F.map q.left)
  exact (singularFunctor.map_comp _ _).symm.trans
    ((singularFunctor.congr_map h).trans (singularFunctor.map_comp _ _))

/-- The inverse comparison keeps that same complete chosen-fiber
naturality square in the opposite direction. -/
theorem chosenSequenceFiberIso_inv_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (n m : ℕ) :
    (sequenceMap hp hp' q n m).fiberMap ≫ (fiberIso d hd hp' n m).inv =
      (fiberIso c hc hp n m).inv ≫
        singularFunctor.map ((evaluation m).map ((iterate n).map
          (underlyingSequential.map (chosenFiberMap q c d hd)))) := by
  apply (cancel_epi (fiberIso c hc hp n m).hom).mp
  rw [← Category.assoc, ← chosenSequenceFiberIso_naturality c hc d hd hp hp' q,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Every actual positive cube-group comparison retains the same
native chosen-fiber square before passing to the original quotient. -/
theorem chosenFiberMulEquiv_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (n m k : ℕ)
    (x : PointedCGWH.piN (k + 1) (((iterate n).obj (underlyingSequential.obj c.pt)).level m)) :
    chosenLoopedFiberMulEquiv (underlyingSequential.map p') (originalLevelFibrations p' hp')
        m k (underlyingChosenCone p' d) (underlyingChosenConeIsLimit p' d hd) n
        (PointedCGWH.piNMap (k + 1) ((evaluation m).map ((iterate n).map
          (underlyingSequential.map (chosenFiberMap q c d hd)))) x) =
      SSet.KanComplex.π.map (sequenceMap hp hp' q n m).fiberMap
        (sequenceMap hp hp' q n m).fiberMap_app_basePoint (k + 1)
          (chosenLoopedFiberMulEquiv (underlyingSequential.map p)
            (originalLevelFibrations p hp) m k (underlyingChosenCone p c)
              (underlyingChosenConeIsLimit p c hc) n x) :=
  (congrArg (SSet.KanComplex.π.map (fiberIso d hd hp' n m).hom
      (chosenLoopedSequenceFiberIso_hom_point (underlyingSequential.map p')
        (originalLevelFibrations p' hp') m (underlyingChosenCone p' d)
          (underlyingChosenConeIsLimit p' d hd) n) (k + 1))
    (cubeSingularMulEquiv_naturality k ((evaluation m).map ((iterate n).map
      (underlyingSequential.map (chosenFiberMap q c d hd)))) x)).trans
    (SSet.KanComplex.π.map_square (fiberIso c hc hp n m).hom (fiberIso d hd hp' n m).hom
      (singularFunctor.map ((evaluation m).map ((iterate n).map
        (underlyingSequential.map (chosenFiberMap q c d hd)))))
      (sequenceMap hp hp' q n m).fiberMap
      (chosenSequenceFiberIso_naturality c hc d hd hp hp' q n m)
      (chosenLoopedSequenceFiberIso_hom_point (underlyingSequential.map p)
        (originalLevelFibrations p hp) m (underlyingChosenCone p c)
          (underlyingChosenConeIsLimit p c hc) n)
      (chosenLoopedSequenceFiberIso_hom_point (underlyingSequential.map p')
        (originalLevelFibrations p' hp') m (underlyingChosenCone p' d)
          (underlyingChosenConeIsLimit p' d hd) n)
      (singularPoint_naturality ((evaluation m).map ((iterate n).map
        (underlyingSequential.map (chosenFiberMap q c d hd)))))
      (sequenceMap hp hp' q n m).fiberMap_app_basePoint (k + 1) _)

/-- The full original iteration-group comparison is natural under all
original Arrow squares between arbitrary caller-chosen fibers. -/
theorem fiberGroupComparison_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (groupIterationDiagramFunctor m k).map
        (underlyingSequential.map (chosenFiberMap q c d hd)) ≫
        (loopedFiberGroupNatIso (underlyingSequential.map p') (originalLevelFibrations p' hp')
          m k (underlyingChosenCone p' d) (underlyingChosenConeIsLimit p' d hd)).hom =
      (loopedFiberGroupNatIso (underlyingSequential.map p) (originalLevelFibrations p hp)
        m k (underlyingChosenCone p c) (underlyingChosenConeIsLimit p c hc)).hom ≫
          fiberGroupMap hp hp' q m k := by
  apply NatTrans.ext
  funext n
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  change chosenLoopedFiberMulEquiv (underlyingSequential.map p')
      (originalLevelFibrations p' hp') m k (underlyingChosenCone p' d)
      (underlyingChosenConeIsLimit p' d hd) n
      ((PointedCGWH.piNPositiveMap k ((evaluation m).map ((iterate n).map
        (underlyingSequential.map (chosenFiberMap q c d hd))))).hom x) = _
  rw [PointedCGWH.piNPositiveMap_apply]
  exact chosenFiberMulEquiv_naturality c hc d hd hp hp' q n m k x

/-- Both full diagonal total-group comparisons retain the unchanged
original total component of every native Arrow square. -/
theorem diagonalTotalGroup_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalFunctor m k).map q.left ≫
        (diagonalTotalGroupNatIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom =
      (diagonalTotalGroupNatIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom ≫ totalGroupMap hp hp' q m k := by
  change (diagonalDiagramFunctor m k).map (underlyingSequential.map q.left) ≫
      ((iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj X') ≫
        (loopedTotalGroupNatIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom) =
    ((iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj X) ≫
      (loopedTotalGroupNatIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom) ≫ _
  have h : (diagonalDiagramFunctor m k).map (underlyingSequential.map q.left) ≫
      (iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj X') =
    (iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj X) ≫
      (groupIterationDiagramFunctor m k).map (underlyingSequential.map q.left) :=
    (iterationDiagonalNatIso m k).inv.naturality (underlyingSequential.map q.left)
  rw [← Category.assoc, h,
    Category.assoc, totalGroupComparison_naturality hp hp' q m k, ← Category.assoc]

/-- Both full diagonal base-group functions keep the complete original
base component and every original loop comparison. -/
theorem diagonalBaseGroup_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalFunctor m k).map q.right ≫
        (diagonalBaseGroupNatIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom =
      (diagonalBaseGroupNatIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom ≫ baseGroupMap hp hp' q m k := by
  change (diagonalDiagramFunctor m k).map (underlyingSequential.map q.right) ≫
      ((iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj Y') ≫
        (loopedBaseGroupNatIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom) =
    ((iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj Y) ≫
      (loopedBaseGroupNatIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom) ≫ _
  have h : (diagonalDiagramFunctor m k).map (underlyingSequential.map q.right) ≫
      (iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj Y') =
    (iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj Y) ≫
      (groupIterationDiagramFunctor m k).map (underlyingSequential.map q.right) :=
    (iterationDiagonalNatIso m k).inv.naturality (underlyingSequential.map q.right)
  rw [← Category.assoc, h,
    Category.assoc, baseGroupComparison_naturality hp hp' q m k, ← Category.assoc]

/-- All original chosen-fiber diagonal comparison functions are natural
in every native Arrow square, including arbitrary changes of chosen cone. -/
theorem diagonalFiberGroup_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalFunctor m k).map (chosenFiberMap q c d hd) ≫
        (diagonalFiberGroupNatIso (underlyingSequential.map p') (underlyingChosenCone p' d)
          (underlyingChosenConeIsLimit p' d hd) (originalLevelFibrations p' hp') m k).hom =
      (diagonalFiberGroupNatIso (underlyingSequential.map p) (underlyingChosenCone p c)
        (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k).hom ≫
          fiberGroupMap hp hp' q m k := by
  change (diagonalDiagramFunctor m k).map
      (underlyingSequential.map (chosenFiberMap q c d hd)) ≫
      ((iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj d.pt) ≫
        (loopedFiberGroupNatIso (underlyingSequential.map p') (originalLevelFibrations p' hp')
          m k (underlyingChosenCone p' d) (underlyingChosenConeIsLimit p' d hd)).hom) =
    ((iterationDiagonalNatIso m k).inv.app (underlyingSequential.obj c.pt) ≫
      (loopedFiberGroupNatIso (underlyingSequential.map p) (originalLevelFibrations p hp)
        m k (underlyingChosenCone p c) (underlyingChosenConeIsLimit p c hc)).hom) ≫ _
  rw [← Category.assoc, (iterationDiagonalNatIso m k).inv.naturality,
    Category.assoc, fiberGroupComparison_naturality c hc d hd hp hp' q m k,
    ← Category.assoc]

/-- Every full original total quotient comparison keeps the same
complete native total component. -/
theorem diagonalTotalColimit_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalPiFunctor m k).map q.left ≫
        (diagonalTotalColimitIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom =
      (diagonalTotalColimitIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom ≫
          GrpCat.FilteredColimits.colimitMap (totalGroupMap hp hp' q m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalTotalGroup_naturality hp hp' q m k)).trans (Q.map_comp _ _))

/-- The actual original quotient functor retains both whole base
comparison maps and every original source map. -/
theorem diagonalBaseColimit_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalPiFunctor m k).map q.right ≫
        (diagonalBaseColimitIso (underlyingSequential.map p')
          (originalLevelFibrations p' hp') m k).hom =
      (diagonalBaseColimitIso (underlyingSequential.map p)
        (originalLevelFibrations p hp) m k).hom ≫
          GrpCat.FilteredColimits.colimitMap (baseGroupMap hp hp' q m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalBaseGroup_naturality hp hp' q m k)).trans (Q.map_comp _ _))

/-- The actual chosen-fiber quotient square retains both full
comparisons and the caller's entire original fiber map. -/
theorem diagonalFiberColimit_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalPiFunctor m k).map (chosenFiberMap q c d hd) ≫
        (diagonalFiberColimitIso (underlyingSequential.map p') (underlyingChosenCone p' d)
          (underlyingChosenConeIsLimit p' d hd) (originalLevelFibrations p' hp') m k).hom =
      (diagonalFiberColimitIso (underlyingSequential.map p) (underlyingChosenCone p c)
        (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k).hom ≫
          GrpCat.FilteredColimits.colimitMap (fiberGroupMap hp hp' q m k) := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := GrpCat.FilteredColimits.colimitFunctor
  exact (Q.map_comp _ _).symm.trans
    ((Q.congr_map (diagonalFiberGroup_naturality c hc d hd hp hp' q m k)).trans
      (Q.map_comp _ _))

/-- The inverse original chosen-fiber quotient maps keep the same
complete square needed by the original connecting function. -/
theorem diagonalFiberColimit_inv_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    GrpCat.FilteredColimits.colimitMap (fiberGroupMap hp hp' q m k) ≫
        (diagonalFiberColimitIso (underlyingSequential.map p') (underlyingChosenCone p' d)
          (underlyingChosenConeIsLimit p' d hd) (originalLevelFibrations p' hp') m k).inv =
      (diagonalFiberColimitIso (underlyingSequential.map p) (underlyingChosenCone p c)
        (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k).inv ≫
          (diagonalPiFunctor m k).map (chosenFiberMap q c d hd) := by
  apply (cancel_epi (diagonalFiberColimitIso (underlyingSequential.map p)
    (underlyingChosenCone p c) (underlyingChosenConeIsLimit p c hc)
      (originalLevelFibrations p hp) m k).hom).mp
  rw [← Category.assoc, ← diagonalFiberColimit_naturality c hc d hd hp hp' q m k,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Every full original diagonal connecting map is natural under every
native Arrow square between arbitrary caller-chosen fiber cones. -/
theorem diagonalConnecting_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (m k : ℕ) :
    (diagonalPiFunctor m (k + 1)).map q.right ≫ diagonalConnecting p' d hd hp' m k =
      diagonalConnecting p c hc hp m k ≫
        (diagonalPiFunctor m k).map (chosenFiberMap q c d hd) := by
  change (diagonalPiFunctor m (k + 1)).map q.right ≫
      ((diagonalBaseColimitIso (underlyingSequential.map p')
        (originalLevelFibrations p' hp') m (k + 1)).hom ≫
          GrpCat.FilteredColimits.colimitMap
            (loopedConnectingGroupMap (underlyingSequential.map p')
              (originalLevelFibrations p' hp') m k) ≫
          (diagonalFiberColimitIso (underlyingSequential.map p') (underlyingChosenCone p' d)
            (underlyingChosenConeIsLimit p' d hd) (originalLevelFibrations p' hp') m k).inv) =
    ((diagonalBaseColimitIso (underlyingSequential.map p)
      (originalLevelFibrations p hp) m (k + 1)).hom ≫
        GrpCat.FilteredColimits.colimitMap
          (loopedConnectingGroupMap (underlyingSequential.map p)
            (originalLevelFibrations p hp) m k) ≫
        (diagonalFiberColimitIso (underlyingSequential.map p) (underlyingChosenCone p c)
          (underlyingChosenConeIsLimit p c hc) (originalLevelFibrations p hp) m k).inv) ≫ _
  rw [← Category.assoc, diagonalBaseColimit_naturality hp hp' q m (k + 1),
    Category.assoc, ← Category.assoc
      (GrpCat.FilteredColimits.colimitMap (baseGroupMap hp hp' q m (k + 1))),
    connectingColimitMap_naturality hp hp' q m k, Category.assoc,
    diagonalFiberColimit_inv_naturality c hc d hd hp hp' q m k, ← Category.assoc,
    ← Category.assoc]
  exact congrArg (fun f => f ≫ (diagonalPiFunctor m k).map (chosenFiberMap q c d hd))
    (Category.assoc _ _ _)

/-- The original consecutive integer connecting morphisms keep the
entire original native Arrow square and its same chosen fiber map. -/
theorem integerConnecting_naturality (q : Arrow.mk p ⟶ Arrow.mk p') (j : ℤ) :
    (integerPiFunctor (j + 1)).map q.right ≫
        IntegerFiberSequence.connectingMap p' d hd hp' j =
      IntegerFiberSequence.connectingMap p c hc hp j ≫
        (integerPiFunctor j).map (chosenFiberMap q c d hd) := by
  let a := (IntegerFiberSequence.successorComparison j).inv.app Y
  let a' := (IntegerFiberSequence.successorComparison j).inv.app Y'
  let f := (integerPiFunctor (j + 1)).map q.right
  let f' := (diagonalPiFunctor (integerTailLevel j) (integerTailPositiveIndex j + 1)).map q.right
  let e := (integerPiFunctor j).map (chosenFiberMap q c d hd)
  let b := diagonalConnecting p c hc hp (integerTailLevel j) (integerTailPositiveIndex j)
  let b' := diagonalConnecting p' d hd hp' (integerTailLevel j) (integerTailPositiveIndex j)
  have h₁ : f ≫ a' = a ≫ f' :=
    IntegerFiberSequence.successorComparison_inv_naturality j q.right
  have h₂ : f' ≫ b' = b ≫ e :=
    diagonalConnecting_naturality c hc d hd hp hp' q
      (integerTailLevel j) (integerTailPositiveIndex j)
  change f ≫ (a' ≫ b') = (a ≫ b) ≫ e
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ b') h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => a ≫ t) h₂).trans (Category.assoc _ _ _).symm)))

section Choices

variable {X₀ Y₀ : C.{u, v}} (p₀ : X₀ ⟶ Y₀)
  (c₀ : PullbackCone p₀ (Diagrams.zeroTo Y₀)) (hc₀ : IsLimit c₀)
  (d₀ : PullbackCone p₀ (Diagrams.zeroTo Y₀)) (hd₀ : IsLimit d₀)

/-- Both full original native chosen-fiber comparisons give the actual
change of caller cone, with the same total and zero endpoint maps. -/
def choiceIso : c₀.pt ≅ d₀.pt :=
  chosenFiberIso p₀ c₀ hc₀ ≪≫ (chosenFiberIso p₀ d₀ hd₀).symm

omit B in
/-- The complete forward change of caller cone is exactly the native
chosen map of the unchanged identity Arrow square. -/
theorem choiceIso_hom_map :
    (choiceIso p₀ c₀ hc₀ d₀ hd₀).hom = chosenFiberMap (𝟙 (Arrow.mk p₀)) c₀ d₀ hd₀ := by
  apply PullbackCone.IsLimit.hom_ext hd₀
  · change ((chosenFiberIso p₀ c₀ hc₀).hom ≫ (chosenFiberIso p₀ d₀ hd₀).inv) ≫ d₀.fst = _
    rw [Category.assoc, chosenFiberIso_inv_fst, chosenFiberIso_hom_fst,
      chosenFiberMap_fst]
    change c₀.fst = c₀.fst ≫ 𝟙 X₀
    exact (Category.comp_id _).symm
  · change ((chosenFiberIso p₀ c₀ hc₀).hom ≫ (chosenFiberIso p₀ d₀ hd₀).inv) ≫ d₀.snd = _
    rw [Category.assoc, chosenFiberIso_inv_snd, chosenFiberIso_hom_snd, chosenFiberMap_snd]

omit B in
/-- Its complete inverse is the same original identity-square map from
the second caller cone to the first. -/
theorem choiceIso_inv_map :
    (choiceIso p₀ c₀ hc₀ d₀ hd₀).inv = chosenFiberMap (𝟙 (Arrow.mk p₀)) d₀ c₀ hc₀ :=
  choiceIso_hom_map p₀ d₀ hd₀ c₀ hc₀

variable (hp₀ : (NativeK.generators orthogonalFamily).rlp p₀)

/-- Every integer connecting function keeps the actual full forward
change of chosen cone, with its unchanged original source group. -/
theorem integerConnecting_choice_hom (j : ℤ) :
    IntegerFiberSequence.connectingMap p₀ c₀ hc₀ hp₀ j ≫
        (integerPiFunctor j).map (choiceIso p₀ c₀ hc₀ d₀ hd₀).hom =
      IntegerFiberSequence.connectingMap p₀ d₀ hd₀ hp₀ j := by
  have h := integerConnecting_naturality c₀ hc₀ d₀ hd₀ hp₀ hp₀ (𝟙 (Arrow.mk p₀)) j
  change (integerPiFunctor (j + 1)).map (𝟙 Y₀) ≫
      IntegerFiberSequence.connectingMap p₀ d₀ hd₀ hp₀ j =
    IntegerFiberSequence.connectingMap p₀ c₀ hc₀ hp₀ j ≫
      (integerPiFunctor j).map (chosenFiberMap (𝟙 (Arrow.mk p₀)) c₀ d₀ hd₀) at h
  rw [(integerPiFunctor (j + 1)).map_id, Category.id_comp] at h
  exact (congrArg (fun t => IntegerFiberSequence.connectingMap p₀ c₀ hc₀ hp₀ j ≫ t)
    ((integerPiFunctor j).congr_map (choiceIso_hom_map p₀ c₀ hc₀ d₀ hd₀))).trans h.symm

/-- The entire inverse change of chosen fiber retains the same original
integer connecting map in the opposite direction. -/
theorem integerConnecting_choice_inv (j : ℤ) :
    IntegerFiberSequence.connectingMap p₀ d₀ hd₀ hp₀ j ≫
        (integerPiFunctor j).map (choiceIso p₀ c₀ hc₀ d₀ hd₀).inv =
      IntegerFiberSequence.connectingMap p₀ c₀ hc₀ hp₀ j :=
  integerConnecting_choice_hom p₀ d₀ hd₀ c₀ hc₀ hp₀ j

end Choices

section Families

variable (a : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

private abbrev KArrows := NativeK.OriginalFiberComparison.rightArrowProperty
  orthogonalFamily.{u, v}

/-- All original chosen connecting maps form one whole natural
transformation on the complete original K-right Arrow category. -/
def connectingNatTrans (j : ℤ) :
    KArrows.ι ⋙ Arrow.rightFunc ⋙ integerPiFunctor (j + 1) ⟶
      KArrows.ι ⋙ chosenFiberFunctor a ha ⋙ integerPiFunctor j where
  app F := IntegerFiberSequence.connectingMap F.obj.hom (a F.obj) (ha F.obj) F.property j
  naturality {F G} q :=
    integerConnecting_naturality (a F.obj) (ha F.obj) (a G.obj) (ha G.obj)
      F.property G.property q.hom j

/-- Its whole component is the actual original connecting map on the
caller's unchanged cone and same original degree. -/
theorem connectingNatTrans_app (j : ℤ) (F : KArrows.FullSubcategory) :
    (connectingNatTrans a ha j).app F =
      IntegerFiberSequence.connectingMap F.obj.hom (a F.obj) (ha F.obj) F.property j := rfl

variable (b : ∀ F : Arrow C.{u, v}, PullbackCone F.hom (Diagrams.zeroTo F.right))
  (hb : ∀ F, IsLimit (b F))

/-- Every pair of original caller cone families has its actual whole
native change-of-choice isomorphism, with all original Arrow actions. -/
def choiceNatIso : chosenFiberFunctor a ha ≅ chosenFiberFunctor b hb :=
  chosenFiberNatIso a ha ≪≫ (chosenFiberNatIso b hb).symm

omit B in
/-- The family comparison retains the exact caller component and both
native chosen-fiber comparison maps. -/
theorem choiceNatIso_app (F : Arrow C.{u, v}) :
    (choiceNatIso a ha b hb).app F = choiceIso F.hom (a F) (ha F) (b F) (hb F) := rfl

/-- Both whole native choice families commute with the full connecting
natural transformation in every original integer degree. -/
theorem connectingNatTrans_choice (j : ℤ) :
    connectingNatTrans a ha j ≫
        (Functor.isoWhiskerLeft KArrows.ι
          (Functor.isoWhiskerRight (choiceNatIso a ha b hb) (integerPiFunctor j))).hom =
      connectingNatTrans b hb j := by
  apply NatTrans.ext
  funext F
  exact integerConnecting_choice_hom F.obj.hom (a F.obj) (ha F.obj) (b F.obj) (hb F.obj)
    F.property j

end Families

end PointedCGWH.Spectra.Orthogonal.ChosenFiberNaturality
