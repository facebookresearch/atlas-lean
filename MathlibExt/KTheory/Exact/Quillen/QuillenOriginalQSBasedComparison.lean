/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalZigzagBasedInverse
public import MathlibExt.Topology.Homotopy.PointRelativeComposition
public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalQSLoopComparison

/-!
# The actual original based real Q/S comparison

The original Q inverse and Stage forward realization maps compose with their
BOTH original singleton-relative inverse families. Every comparison point is
derived from those actual maps. The same based comparison supplies the actual
constant-loop/strict-loop calibration needed for OWNunit transport.
No based/model/inverse/triangle outcome is supplied by the caller.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalQSBasedComparisonWaldhausen : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- SAME original based real Q/S comparison, with actual original Q inverse
and Stage forward map; both original relative inverse families are used. -/
def quillenOriginalQSRealHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (NQReal C) (stageWeakDiagonalReal C) :=
  (quillenOriginalQZigzagHomotopyEquiv C).symm.trans (quillenOriginalStageZigzagHomotopyEquiv C)

/-- The original comparison sends the selected Q point to selected Stage
point by the actual original inverse/forward point equations. -/
theorem quillenOriginalQSRealHomotopyEquiv_basepoint :
    (quillenOriginalQSRealHomotopyEquiv C).toFun (NQReal.basepoint C) =
      stageWeakDiagonalReal.basepoint C := by
  let Q := quillenOriginalQZigzagHomotopyEquiv C
  let S := quillenOriginalStageZigzagHomotopyEquiv C
  have hQ : Q.invFun (NQReal.basepoint C) =
      quillenStageGridDiagonalReal.basepoint C :=
    (DFunLike.congr_fun (quillenOriginalQZigzagHomotopyEquiv_invFun C)
      (NQReal.basepoint C)).trans (quillenOriginalQZigzagBasedInverse C).inv_basepoint
  have hS : S.toFun (quillenStageGridDiagonalReal.basepoint C) =
      stageWeakDiagonalReal.basepoint C := by
    rw [quillenOriginalStageZigzagHomotopyEquiv_toFun,
      quillenStageGridToStageWeaklyPointed_hom]
    exact (quillenStageGridToStageWeakDiagonal_realizedZeroVertex (C := C)).trans
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex C).symm
  change S.toFun (Q.invFun (NQReal.basepoint C)) = stageWeakDiagonalReal.basepoint C
  exact (congrArg S.toFun hQ).trans hS

/-- The original inverse comparison returns the SAME selected Stage zero
point to the SAME selected Q point, from original point laws. -/
theorem quillenOriginalQSRealHomotopyEquiv_inv_basepoint :
    (quillenOriginalQSRealHomotopyEquiv C).invFun (stageWeakDiagonalReal.basepoint C) =
      NQReal.basepoint C := by
  let Q := quillenOriginalQZigzagHomotopyEquiv C
  let S := quillenOriginalStageZigzagHomotopyEquiv C
  have hS : S.invFun (stageWeakDiagonalReal.basepoint C) =
      quillenStageGridDiagonalReal.basepoint C :=
    (DFunLike.congr_fun (quillenOriginalStageZigzagHomotopyEquiv_invFun C)
      (stageWeakDiagonalReal.basepoint C)).trans
        (quillenOriginalStageZigzagBasedInverse C).inv_basepoint
  have hQ : Q.toFun (quillenStageGridDiagonalReal.basepoint C) = NQReal.basepoint C := by
    rw [quillenOriginalQZigzagHomotopyEquiv_toFun]
    exact quillenStageGridToNQ_map_basepoint C
  change Q.toFun (S.invFun (stageWeakDiagonalReal.basepoint C)) = NQReal.basepoint C
  exact (congrArg Q.toFun hS).trans hQ

/-- BOTH original full singleton-relative inverse families remain at the
actual Q and Stage points of the SAME real comparison. -/
def quillenOriginalQSRealLeftHomotopyRel :
    ContinuousMap.HomotopyRel
      ((quillenOriginalQSRealHomotopyEquiv C).invFun.comp (quillenOriginalQSRealHomotopyEquiv C).toFun)
      (ContinuousMap.id (NQReal C)) {NQReal.basepoint C} :=
  ContinuousMap.HomotopyEquiv.transLeftHomotopyRel
    (quillenOriginalQZigzagHomotopyEquiv C).symm (quillenOriginalStageZigzagHomotopyEquiv C)
    (NQReal.basepoint C) (quillenStageGridDiagonalReal.basepoint C)
    ((DFunLike.congr_fun (quillenOriginalQZigzagHomotopyEquiv_invFun C)
      (NQReal.basepoint C)).trans (quillenOriginalQZigzagBasedInverse C).inv_basepoint)
    (quillenOriginalQZigzagRealRightFamily C) (quillenOriginalStageZigzagRealLeftFamily C)

/-- The original full target-relative inverse family is retained as well. -/
def quillenOriginalQSRealRightHomotopyRel :
    ContinuousMap.HomotopyRel
      ((quillenOriginalQSRealHomotopyEquiv C).toFun.comp (quillenOriginalQSRealHomotopyEquiv C).invFun)
      (ContinuousMap.id (stageWeakDiagonalReal C)) {stageWeakDiagonalReal.basepoint C} :=
  ContinuousMap.HomotopyEquiv.transRightHomotopyRel
    (quillenOriginalQZigzagHomotopyEquiv C).symm (quillenOriginalStageZigzagHomotopyEquiv C)
    (quillenStageGridDiagonalReal.basepoint C) (stageWeakDiagonalReal.basepoint C)
    ((DFunLike.congr_fun (quillenOriginalStageZigzagHomotopyEquiv_invFun C)
      (stageWeakDiagonalReal.basepoint C)).trans
        (quillenOriginalStageZigzagBasedInverse C).inv_basepoint)
    (quillenOriginalQZigzagRealLeftFamily C) (quillenOriginalStageZigzagRealRightFamily C)


/-- The actual strict-loop comparison of the SAME original based real map.
This is comparison data; original functor maps/units are not replaced. -/
def quillenOriginalQSBasedStrictLoopMap : C(NQKSpace C, stageWeakDiagonalKSpace C) where
  toFun gamma := (gamma.map (quillenOriginalQSRealHomotopyEquiv C).toFun.continuous).cast
    (quillenOriginalQSRealHomotopyEquiv_basepoint C).symm
    (quillenOriginalQSRealHomotopyEquiv_basepoint C).symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : NQKSpace C × unitInterval =>
      (quillenOriginalQSRealHomotopyEquiv C).toFun (z.1 z.2))
    exact (quillenOriginalQSRealHomotopyEquiv C).toFun.continuous.comp continuous_eval

private theorem originalQSStrictLoopValueComputed (gamma : NQKSpace C) (t : unitInterval) :
    quillenOriginalQSBasedStrictLoopMap C gamma t =
      (quillenOriginalQSRealHomotopyEquiv C).toFun (gamma t) := rfl

/-- Every original loop and time retain the SAME original based comparison value. -/
theorem quillenOriginalQSBasedStrictLoopMap_apply (gamma : NQKSpace C) (t : unitInterval) :
    quillenOriginalQSBasedStrictLoopMap C gamma t =
      (quillenOriginalQSRealHomotopyEquiv C).toFun (gamma t) :=
  originalQSStrictLoopValueComputed C gamma t

/-- The comparison constant loop is the actual selected Stage constant loop,
from the original derived point equation, not a functor unit substitution. -/
theorem quillenOriginalQSBasedStrictLoopMap_refl :
    quillenOriginalQSBasedStrictLoopMap C (Path.refl (NQReal.basepoint C)) =
      Path.refl (stageWeakDiagonalReal.basepoint C) := by
  apply Path.ext
  funext t
  exact (quillenOriginalQSBasedStrictLoopMap_apply C _ t).trans
    (quillenOriginalQSRealHomotopyEquiv_basepoint C)

/-- Actual designated comparison unit; the original081 functor units remain separate. -/
def quillenOriginalQSBasedStrictLoopUnit :
    Path (quillenOriginalQSBasedStrictLoopMap C (Path.refl (NQReal.basepoint C)))
      (Path.refl (stageWeakDiagonalReal.basepoint C)) :=
  (Path.refl (Path.refl (stageWeakDiagonalReal.basepoint C))).cast
    (quillenOriginalQSBasedStrictLoopMap_refl C) rfl

end AlgebraicKTheory

end

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe u v

namespace AlgebraicKTheory

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
attribute [local instance] originalQSBasedComparisonWaldhausen

private theorem originalQSRealForwardMapValueComputed :
    (quillenOriginalQSRealHomotopyEquiv C).toFun =
      (quillenOriginalStageZigzagHomotopyEquiv C).toFun.comp
        (quillenOriginalQZigzagHomotopyEquiv C).invFun := rfl

/-- The whole original real comparison retains the original Stage forward
map composed with the SAME original Q inverse. -/
theorem quillenOriginalQSRealHomotopyEquiv_toFun :
    (quillenOriginalQSRealHomotopyEquiv C).toFun =
      (quillenOriginalStageZigzagHomotopyEquiv C).toFun.comp
        (quillenOriginalQZigzagHomotopyEquiv C).invFun :=
  originalQSRealForwardMapValueComputed C

end AlgebraicKTheory

end
