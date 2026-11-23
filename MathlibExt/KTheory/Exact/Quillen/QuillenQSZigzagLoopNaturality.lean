/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridZeroComparisonCoherence
public import MathlibExt.Topology.Homotopy.WeaklyPointedHomotopyRel

/-!
# Pointwise loop naturality for the Quillen Q/S zigzag

The canonical Stage-grid zero-comparison coherence turns each strict
underlying-map square into a homotopy relative to the source basepoint.  Its
two root-path compatibility fields then give pointwise path homotopies for
the induced Q- and Stage-side loop maps.

These results are pointwise.  They assert neither strict equality nor a
bundled homotopy of loop maps, and construct no weak equivalence, pointed
equivalence, group isomorphism, or spectrum map.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

local instance quillenQSZigzagLoopNaturalityWaldhausenC :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

local instance quillenQSZigzagLoopNaturalityWaldhausenD :
    WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The strict grid-to-Q square, viewed as a homotopy relative to the source
grid basepoint in map-first to Q-first order. -/
noncomputable def quillenStageGridToNQ_weak_square_homotopyRel :
    ContinuousMap.HomotopyRel
      (((quillenStageGridDiagonalRealMapWeaklyPointed F
          (quillenStageGridZeroComparisonCoherence F).rootPath).comp
        (quillenStageGridToNQWeaklyPointed (C := D))).hom)
      (((quillenStageGridToNQWeaklyPointed (C := C)).comp
        (NQRealMapWeaklyPointed F)).hom)
      {quillenStageGridDiagonalReal.basepoint C} :=
  (ContinuousMap.HomotopyRel.refl
    (((quillenStageGridDiagonalRealMapWeaklyPointed F
        (quillenStageGridZeroComparisonCoherence F).rootPath).comp
      (quillenStageGridToNQWeaklyPointed (C := D))).hom)
    {quillenStageGridDiagonalReal.basepoint C}).cast rfl
      (quillenStageGridToNQ_weak_square_hom F
        (quillenStageGridZeroComparisonCoherence F).rootPath)

/-- The strict grid-to-Stage square, viewed as a homotopy relative to the
source grid basepoint in map-first to Stage-first order. -/
noncomputable def quillenStageGridToStage_weak_square_homotopyRel :
    ContinuousMap.HomotopyRel
      (((quillenStageGridDiagonalRealMapWeaklyPointed F
          (quillenStageGridZeroComparisonCoherence F).rootPath).comp
        (quillenStageGridToStageWeaklyPointed (C := D))).hom)
      (((quillenStageGridToStageWeaklyPointed (C := C)).comp
        (stageWeakDiagonalRealMapWeaklyPointed C D F)).hom)
      {quillenStageGridDiagonalReal.basepoint C} :=
  (ContinuousMap.HomotopyRel.refl
    (((quillenStageGridDiagonalRealMapWeaklyPointed F
        (quillenStageGridZeroComparisonCoherence F).rootPath).comp
      (quillenStageGridToStageWeaklyPointed (C := D))).hom)
    {quillenStageGridDiagonalReal.basepoint C}).cast rfl
      (quillenStageGridToStage_weak_square_hom F
        (quillenStageGridZeroComparisonCoherence F).rootPath)

/-- Pointwise loop naturality for the Q-side leg, with the map-first route
on the left and the Q-first route on the right. -/
theorem quillenStageGridToNQLoopMap_naturality
    (gamma : quillenStageGridDiagonalKSpace C) :
    ((((quillenStageGridDiagonalRealMapWeaklyPointed F
        (quillenStageGridZeroComparisonCoherence F).rootPath).comp
      (quillenStageGridToNQWeaklyPointed (C := D))).loopMap gamma).Homotopic
      (((quillenStageGridToNQWeaklyPointed (C := C)).comp
        (NQRealMapWeaklyPointed F)).loopMap gamma)) := by
  exact ContinuousMap.WeaklyPointed.loopMap_homotopic_of_homotopyRel _ _
    (quillenStageGridToNQ_weak_square_homotopyRel F)
    (quillenStageGridZeroComparisonCoherence F).toNQ gamma

/-- Pointwise loop naturality for the Stage-side leg, with the map-first
route on the left and the Stage-first route on the right. -/
theorem quillenStageGridToStageLoopMap_naturality
    (gamma : quillenStageGridDiagonalKSpace C) :
    ((((quillenStageGridDiagonalRealMapWeaklyPointed F
        (quillenStageGridZeroComparisonCoherence F).rootPath).comp
      (quillenStageGridToStageWeaklyPointed (C := D))).loopMap gamma).Homotopic
      (((quillenStageGridToStageWeaklyPointed (C := C)).comp
        (stageWeakDiagonalRealMapWeaklyPointed C D F)).loopMap gamma)) := by
  exact ContinuousMap.WeaklyPointed.loopMap_homotopic_of_homotopyRel _ _
    (quillenStageGridToStage_weak_square_homotopyRel F)
    (quillenStageGridZeroComparisonCoherence F).toStage gamma

end AlgebraicKTheory
