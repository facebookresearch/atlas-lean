/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpace
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap
public import MathlibExt.KTheory.Exact.Quillen.KSpace
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzag
public import MathlibExt.KTheory.Exact.Quillen.ZeroCoherence
public import MathlibExt.Topology.Homotopy.WeaklyPointedMap

/-!
# Weakly pointed Quillen Q/S zigzag and loop maps

The common zero vertex of the unpointed Quillen Q/S zigzag selects basepoints
on the realized Stage-grid and outer-edgewise Stage carriers.  Each elementary
realized leg preserves its selected basepoint by an exact equality, so a cast
of the reflexive path equips it with a `ContinuousMap.WeaklyPointed` structure.
The factored right leg uses the generic weakly-pointed composition operation.

Applying `ContinuousMap.WeaklyPointed.loopMap` gives the continuous zigzag
between the corresponding one-fold loop-space carriers.  The factored right
loop map agrees with the composite only up to the generic pointwise path
homotopy: path concatenation is not strictly associative or unital.

This file does not claim that any loop map is a weak homotopy equivalence.  It
also constructs no endpoint map or inverse, homotopy equivalence, localization,
spectrum map, or exact-functor naturality.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The Waldhausen structure derived from the given exact structure, used by
the original Quillen/Stage comparison and its chosen zero point paths. -/
local instance quillenQSZigzagWeaklyPointedWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- Realization of the diagonal nerve of Quillen Stage-grid lifts. -/
noncomputable abbrev quillenStageGridDiagonalReal :=
  SSet.toTop.obj (quillenStageGridDiagonal C)

/-- Basepoint of the realized Stage-grid diagonal, selected by its canonical
zero vertex. -/
noncomputable def quillenStageGridDiagonalReal.basepoint :
    quillenStageGridDiagonalReal C :=
  SSet.realizedVertex (quillenStageGridDiagonalZeroVertex (C := C))

/-- Realization of the outer-edgewise weak-Stage diagonal. -/
noncomputable abbrev edgewiseStageWeakDiagonalReal :=
  SSet.toTop.obj (edgewiseStageWeakDiagonal C)

/-- Basepoint of the realized outer-edgewise weak-Stage diagonal, selected by
the pointwise-zero degree-one Stage. -/
noncomputable def edgewiseStageWeakDiagonalReal.basepoint :
    edgewiseStageWeakDiagonalReal C :=
  SSet.realizedVertex (edgewiseStageWeakDiagonalZeroVertex (C := C))

/-- The realized Q-side leg sends the selected Stage-grid basepoint exactly to
the selected Quillen basepoint. -/
@[simp]
theorem quillenStageGridToNQ_map_basepoint :
    SSet.toTop.map (quillenStageGridToNQ (C := C))
        (quillenStageGridDiagonalReal.basepoint C) =
      NQReal.basepoint C := by
  rw [quillenStageGridDiagonalReal.basepoint,
    quillenStageGridToNQ_realizedZeroVertex,
    ← NQReal.basepoint_eq_realizedVertex]

/-- The realized Stage projection sends the selected Stage-grid basepoint
exactly to the selected outer-edgewise Stage basepoint. -/
@[simp]
theorem quillenStageGridStageProjection_map_basepoint :
    SSet.toTop.map
        (quillenStageGridStageProjectionDiagonal (C := C))
        (quillenStageGridDiagonalReal.basepoint C) =
      edgewiseStageWeakDiagonalReal.basepoint C := by
  simpa only [quillenStageGridDiagonalReal.basepoint,
    edgewiseStageWeakDiagonalReal.basepoint] using
      quillenStageGridStageProjectionDiagonal_realizedZeroVertex (C := C)

/-- The realized outer-edgewise comparison sends its selected basepoint
exactly to the selected ordinary Stage basepoint. -/
@[simp]
theorem outerEdgewiseStageDiagonalComparison_map_basepoint :
    SSet.toTop.map (outerEdgewiseStageDiagonalComparison (C := C))
        (edgewiseStageWeakDiagonalReal.basepoint C) =
      stageWeakDiagonalReal.basepoint C := by
  rw [edgewiseStageWeakDiagonalReal.basepoint,
    outerEdgewiseStageDiagonalComparison_realizedZeroVertex,
    ← stageWeakDiagonalReal.basepoint_eq_realizedVertex]

/-- Weakly-pointed realized Q-side leg, with the endpoint-cast reflexive root
path supplied by exact preservation of the selected basepoint. -/
noncomputable def quillenStageGridToNQWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (quillenStageGridDiagonalReal.basepoint C)
      (NQReal.basepoint C) where
  hom := (SSet.toTop.map (quillenStageGridToNQ (C := C))).hom
  rootPath :=
    (Path.refl (NQReal.basepoint C)).cast
      (quillenStageGridToNQ_map_basepoint (C := C)) rfl

/-- Weakly-pointed realized Stage-projection leg, with the endpoint-cast
reflexive root path supplied by exact preservation of the selected basepoint. -/
noncomputable def quillenStageGridStageProjectionWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (quillenStageGridDiagonalReal.basepoint C)
      (edgewiseStageWeakDiagonalReal.basepoint C) where
  hom :=
    (SSet.toTop.map
      (quillenStageGridStageProjectionDiagonal (C := C))).hom
  rootPath :=
    (Path.refl (edgewiseStageWeakDiagonalReal.basepoint C)).cast
      (quillenStageGridStageProjection_map_basepoint (C := C)) rfl

/-- Weakly-pointed realized outer-edgewise Stage comparison, with the
endpoint-cast reflexive root path supplied by exact preservation of the
selected basepoint. -/
noncomputable def outerEdgewiseStageDiagonalComparisonWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (edgewiseStageWeakDiagonalReal.basepoint C)
      (stageWeakDiagonalReal.basepoint C) where
  hom :=
    (SSet.toTop.map
      (outerEdgewiseStageDiagonalComparison (C := C))).hom
  rootPath :=
    (Path.refl (stageWeakDiagonalReal.basepoint C)).cast
      (outerEdgewiseStageDiagonalComparison_map_basepoint (C := C)) rfl

/-- The weakly-pointed factored right leg, formed by generic composition of
the Stage projection and the outer-edgewise Stage comparison. -/
noncomputable def quillenStageGridToStageWeaklyPointed :
    ContinuousMap.WeaklyPointed
      (quillenStageGridDiagonalReal.basepoint C)
      (stageWeakDiagonalReal.basepoint C) :=
  (quillenStageGridStageProjectionWeaklyPointed (C := C)).comp
    (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C))

/-- The underlying continuous map of the weakly-pointed right leg is exactly
the realization of the named factored simplicial right leg. -/
@[simp]
theorem quillenStageGridToStageWeaklyPointed_hom :
    (quillenStageGridToStageWeaklyPointed (C := C)).hom =
      (SSet.toTop.map
        (quillenStageGridToStageWeakDiagonal (C := C))).hom := by
  change
    ((SSet.toTop.map
        (quillenStageGridStageProjectionDiagonal (C := C)) ≫
      SSet.toTop.map
        (outerEdgewiseStageDiagonalComparison (C := C))).hom) = _
  rw [← SSet.toTop.map_comp]
  rfl

/-- One-fold loop-space carrier of the realized Stage-grid diagonal. -/
noncomputable abbrev quillenStageGridDiagonalKSpace :=
  LoopSpace (quillenStageGridDiagonalReal C)
    (quillenStageGridDiagonalReal.basepoint C)

/-- One-fold loop-space carrier of the realized outer-edgewise weak-Stage
diagonal. -/
noncomputable abbrev edgewiseStageWeakDiagonalKSpace :=
  LoopSpace (edgewiseStageWeakDiagonalReal C)
    (edgewiseStageWeakDiagonalReal.basepoint C)

/-- Continuous loop map induced by the weakly-pointed Q-side leg. -/
noncomputable def quillenStageGridToNQLoopMap :
    C(quillenStageGridDiagonalKSpace C, NQKSpace C) :=
  (quillenStageGridToNQWeaklyPointed (C := C)).loopMap

/-- Continuous loop map induced by the weakly-pointed Stage projection. -/
noncomputable def quillenStageGridStageProjectionLoopMap :
    C(quillenStageGridDiagonalKSpace C,
      edgewiseStageWeakDiagonalKSpace C) :=
  (quillenStageGridStageProjectionWeaklyPointed (C := C)).loopMap

/-- Continuous loop map induced by the weakly-pointed outer-edgewise Stage
comparison. -/
noncomputable def outerEdgewiseStageDiagonalComparisonLoopMap :
    C(edgewiseStageWeakDiagonalKSpace C,
      stageWeakDiagonalKSpace C) :=
  (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)).loopMap

/-- Continuous loop map induced by the composed weakly-pointed right leg. -/
noncomputable def quillenStageGridToStageLoopMap :
    C(quillenStageGridDiagonalKSpace C,
      stageWeakDiagonalKSpace C) :=
  (quillenStageGridToStageWeaklyPointed (C := C)).loopMap

/-- The factored right loop map is pointwise homotopic to the composite of its
two elementary loop maps. -/
theorem quillenStageGridToStageLoopMap_comp_homotopic
    (gamma : quillenStageGridDiagonalKSpace C) :
    (quillenStageGridToStageLoopMap (C := C) gamma).Homotopic
      (outerEdgewiseStageDiagonalComparisonLoopMap (C := C)
        (quillenStageGridStageProjectionLoopMap (C := C) gamma)) := by
  exact ContinuousMap.WeaklyPointed.loopMap_comp_homotopic
    (quillenStageGridStageProjectionWeaklyPointed (C := C))
    (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)) gamma

end AlgebraicKTheory

end


public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe uK vK

namespace AlgebraicKTheory

variable (C : Type uK) [Category.{vK} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The Q leg retains the realization of the original simplicial map. -/
theorem quillenStageGridToNQWeaklyPointed_hom :
    (quillenStageGridToNQWeaklyPointed (C := C)).hom =
      (SSet.toTop.map (quillenStageGridToNQ (C := C))).hom := rfl

/-- The Q leg retains its original equality-cast reflexive root. -/
theorem quillenStageGridToNQWeaklyPointed_rootPath :
    (quillenStageGridToNQWeaklyPointed (C := C)).rootPath =
      (Path.refl (NQReal.basepoint C)).cast
        (quillenStageGridToNQ_map_basepoint (C := C)) rfl := rfl

/-- Both original factors of the factored Stage root have constant values. -/
theorem quillenStageGridToStageWeaklyPointed_rootPath_apply (t : unitInterval) :
    letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
    (quillenStageGridToStageWeaklyPointed (C := C)).rootPath t =
      stageWeakDiagonalReal.basepoint C := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  change (((quillenStageGridStageProjectionWeaklyPointed (C := C)).rootPath.map
      (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)).hom.continuous).trans
      (outerEdgewiseStageDiagonalComparisonWeaklyPointed (C := C)).rootPath) t = _
  rw [Path.trans_apply]
  split
  · exact outerEdgewiseStageDiagonalComparison_map_basepoint C
  · rfl

end AlgebraicKTheory

end
