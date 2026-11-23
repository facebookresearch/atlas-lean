/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Extension.BasedSplitExactQLoopComparison

/-! Direct full original-map, point and relative-family scope clients. -/

universe u v

noncomputable section

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial Topology
open AlgebraicKTheory AlgebraicKTheory.BasedSplitExactQLoop

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

#check @AlgebraicKTheory.BasedSplitExactQLoop.comparison
#print axioms AlgebraicKTheory.BasedSplitExactQLoop.comparison
#check @AlgebraicKTheory.BasedSplitExactQLoop.ComparisonData
#print axioms AlgebraicKTheory.BasedSplitExactQLoop.ComparisonData
#check @AlgebraicKTheory.BasedSplitExactQLoop.comparisonMap_point
#print axioms AlgebraicKTheory.BasedSplitExactQLoop.comparisonMap_point
#check @AlgebraicKTheory.BasedSplitExactQLoop.homotopyEquiv_toFun
#print axioms AlgebraicKTheory.BasedSplitExactQLoop.homotopyEquiv_toFun

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

-- Only the original category/exact structure and actual row splitness are inputs.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ComparisonData (C := C) := comparison hSplit

-- The weak comparison's original Core-to-fiber map has a genuine point-relative inverse.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ContinuousMap.HomotopyRel
      ((comparison hSplit).fiberInverse.comp
        (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)).hom)
      (ContinuousMap.id (completedCoreSpace (C := C))) {completedCorePoint (C := C)} :=
  (comparison hSplit).fiberSourceHomotopy

example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ContinuousMap.HomotopyRel
      ((OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)).hom.comp
        (comparison hSplit).fiberInverse)
      (ContinuousMap.id (originalZeroFiber (C := C))) {selectedZeroFiberPoint (C := C)} :=
  (comparison hSplit).fiberTargetHomotopy

-- Both relative inverse families concern the original full raw Q-loop composite.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ContinuousMap.HomotopyRel
      ((comparison hSplit).loopInverse.comp (comparisonMap (C := C)).hom)
      (ContinuousMap.id (completedCoreSpace (C := C))) {completedCorePoint (C := C)} :=
  (comparison hSplit).loopSourceHomotopy

example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ContinuousMap.HomotopyRel
      ((comparisonMap (C := C)).hom.comp (comparison hSplit).loopInverse)
      (ContinuousMap.id (originalQLoops (C := C))) {constantQLoop (C := C)} :=
  (comparison hSplit).loopTargetHomotopy

-- The actual returned inverse preserves the literal completed unit/constant loop.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    (comparison hSplit).loopInverse (constantQLoop (C := C)) = completedCorePoint (C := C) :=
  (comparison hSplit).loopInverse_point

-- The same returned loop inverse is j0 followed by the returned original fiber inverse.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    (comparison hSplit).loopInverse = (comparison hSplit).fiberInverse.comp
      (OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber (C := C)).hom :=
  (comparison hSplit).loopInverse_eq

-- Full-map equality preserves every original row/denominator and every loop component.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    (homotopyEquiv hSplit).toFun =
      (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C) ≫
        OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)).hom := by
  exact homotopyEquiv_toFun hSplit

-- Actual time-family stationarity, rather than only point equations at the endpoints.
example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (t : unitInterval) :
    (comparison hSplit).loopSourceHomotopy (t, completedCorePoint (C := C)) =
      completedCorePoint (C := C) := by
  have h := (comparison hSplit).loopSourceHomotopy.eq_fst t (Set.mem_singleton _)
  change (comparison hSplit).loopSourceHomotopy (t, completedCorePoint (C := C)) =
    (comparison hSplit).loopInverse (comparisonMap (C := C) (completedCorePoint (C := C))) at h
  exact h.trans ((congrArg (comparison hSplit).loopInverse comparisonMap_point).trans
    (comparison hSplit).loopInverse_point)

example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (t : unitInterval) :
    (comparison hSplit).loopTargetHomotopy (t, constantQLoop (C := C)) =
      constantQLoop (C := C) := by
  have h := (comparison hSplit).loopTargetHomotopy.eq_fst t (Set.mem_singleton _)
  change (comparison hSplit).loopTargetHomotopy (t, constantQLoop (C := C)) =
    comparisonMap (C := C) ((comparison hSplit).loopInverse (constantQLoop (C := C))) at h
  exact h.trans ((congrArg (comparisonMap (C := C)) (comparison hSplit).loopInverse_point).trans
    comparisonMap_point)

end
