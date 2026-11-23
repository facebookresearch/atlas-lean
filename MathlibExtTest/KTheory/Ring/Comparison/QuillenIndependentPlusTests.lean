/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.Comparison.QuillenIndependentPlus

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u v w

namespace AlgebraicKTheory.QuillenPlus

private local instance fixedRingK0Topology (R : Type u) [Ring R] :
    TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str

example (R : Type u) [Ring R] :
    let Q := BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)
    let q := BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max u v} R)
    let T := independentPlusProduct R
    let t : T := (0, StableGL.independentBGLCellPoint R)
    ∃ e : Q ≃ₕ T, e.toFun q = t ∧ e.invFun t = q ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Q) {q}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id T) {t}) := by
  obtain ⟨_d, _, _, _, _, _, _a, _, _, _, _, e, _, _, he, hei, L, S, _⟩ :=
    quillenIndependentPlusEquivalence_exists.{u, v, w} R
  exact ⟨e, he, hei, L, S⟩

example (R : Type u) [Ring R] :
    let Q := BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)
    let T := independentPlusProduct R
    ∃ e : Q ≃ₕ T, ∀ x : Q, (e.toFun x).1 =
      (RingK0.projectiveProductForward.{u, v, w} R
        (projectiveQLoopToNativePair.{u, v, w} R x)).1 := by
  obtain ⟨_d, _, _, _, _, _, _a, _, _, _, _, e, _, _, _, _, _, _, hClass⟩ :=
    quillenIndependentPlusEquivalence_exists.{u, v, w} R
  exact ⟨e, hClass⟩

example (R : Type u) [Ring R] :
    let Q := BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)
    let T := independentPlusProduct R
    let b := StableGL.independentBGLCellPoint R
    ∃ e : Q ≃ₕ T,
      ∃ H : ContinuousMap.Homotopy (e.toFun.comp e.invFun) (ContinuousMap.id T),
        ∀ k : RingK0 R,
          H (0, (k, b)) = e.toFun (e.invFun (k, b)) ∧ H (1, (k, b)) = (k, b) := by
  obtain ⟨_d, _, _, _, _, _, _a, _, _, _, _, e, _, _, _, _, _, ⟨S⟩, _⟩ :=
    quillenIndependentPlusEquivalence_exists.{u, v, w} R
  refine ⟨e, S.toHomotopy, ?_⟩
  intro k
  exact ⟨S.toHomotopy.map_zero_left _, S.toHomotopy.map_one_left _⟩

end AlgebraicKTheory.QuillenPlus

end


noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u v w

namespace AlgebraicKTheory.QuillenPlus

private local instance canonicalClientK0Topology (R : Type u) [Ring R] :
    TopologicalSpace (RingK0 R) := (RingK0.discreteSpace R).str

/-- The direct original-map calibration works in all original profiles. -/
example (R : Type u) [Ring R]
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{max u v} R)) :
    (RingK0.projectiveProductForward.{u, v, w} R
      (projectiveQLoopToNativePair.{u, v, w} R x)).1 =
      RingK0.projectiveUniverseEquiv.{u, v} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R) (ZerothHomotopy.mk x)) :=
  projectiveQLoopToNativePair_first_eq_canonicalK0.{u, v, w} R x

/-- The Ring, projective carrier and native probe are independently sized. -/
example (R : Type) [Ring R]
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{2} R)) :
    (RingK0.projectiveProductForward.{0, 2, 3} R
      (projectiveQLoopToNativePair.{0, 2, 3} R x)).1 =
      RingK0.projectiveUniverseEquiv.{0, 2} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{2} R) (ZerothHomotopy.mk x)) :=
  projectiveQLoopToNativePair_first_eq_canonicalK0.{0, 2, 3} R x

example (R : Type 2) [Ring R]
    (x : BasedSplitExactQLoop.originalQLoops (C := FGProjectiveCat.{2} R)) :
    (RingK0.projectiveProductForward.{2, 0, 1} R
      (projectiveQLoopToNativePair.{2, 0, 1} R x)).1 =
      RingK0.projectiveUniverseEquiv.{2, 0} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{2} R) (ZerothHomotopy.mk x)) :=
  projectiveQLoopToNativePair_first_eq_canonicalK0.{2, 0, 1} R x

/-- ONE global inverse and BOTH original point-relative families accompany
its independent canonical K0 formula on EVERY source point. -/
example (R : Type u) [Ring R] :
    let C := FGProjectiveCat.{max u v} R
    let Q := BasedSplitExactQLoop.originalQLoops (C := C)
    let q := BasedSplitExactQLoop.constantQLoop (C := C)
    let T := independentPlusProduct R
    let t : T := (0, StableGL.independentBGLCellPoint R)
    ∃ e : Q ≃ₕ T, e.toFun q = t ∧ e.invFun t = q ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id Q) {q}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id T) {t}) ∧
      ∀ x : Q, (e.toFun x).1 = RingK0.projectiveUniverseEquiv.{u, v} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max u v} R) (ZerothHomotopy.mk x)) := by
  obtain ⟨_d, _, _, _, _, _, _a, _, _, _, _, e, _, _, he, hei, L, S, hClass⟩ :=
    quillenIndependentPlusEquivalence_canonicalK0_exists.{u, v, w} R
  exact ⟨e, he, hei, L, S, hClass⟩

#check projectiveQLoopToNativePair_apply
#print axioms projectiveQLoopToNativePair_apply
#check projectiveQLoopToNativePair_first_eq_canonicalK0
#print axioms projectiveQLoopToNativePair_first_eq_canonicalK0
#check quillenIndependentPlusEquivalence_canonicalK0_exists
#print axioms quillenIndependentPlusEquivalence_canonicalK0_exists

end AlgebraicKTheory.QuillenPlus

end
