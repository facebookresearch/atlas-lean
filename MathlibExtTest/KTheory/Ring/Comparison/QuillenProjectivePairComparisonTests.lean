/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.Comparison.QuillenProjectivePairComparison

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u v w

namespace AlgebraicKTheory.QuillenPlus

example (R : Type u) [Ring R] :
    let C := FGProjectiveCat.{max u v} R
    let Q := BasedSplitExactQLoop.originalQLoops (C := C)
    let q := BasedSplitExactQLoop.constantQLoop (C := C)
    let N := RingK0.projectiveOriginalSpace.{u, v, w} R
    let n := RingK0.projectiveOriginalPoint.{u, v, w} R
    ∃ g : C(N, Q), g n = q ∧
      Nonempty (ContinuousMap.HomotopyRel
        (g.comp (projectiveQLoopToNativePair.{u, v, w} R)) (ContinuousMap.id Q) {q}) ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((projectiveQLoopToNativePair.{u, v, w} R).comp g) (ContinuousMap.id N) {n}) := by
  obtain ⟨e, hForward, _, hInversePoint, ⟨L⟩, ⟨S⟩⟩ :=
    projectiveQLoopNativePairEquivalence_exists.{u, v, w} R
  exact ⟨e.invFun, hInversePoint,
    ⟨L.cast (congrArg (fun f => e.invFun.comp f) hForward) rfl⟩,
    ⟨S.cast (congrArg (fun f => f.comp e.invFun) hForward) rfl⟩⟩

example (R : Type u) [Ring R] :
    projectiveQLoopToNativePair.{u, v, w} R
        (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max u v} R)) =
      RingK0.projectiveOriginalPoint.{u, v, w} R := by
  obtain ⟨e, hForward, hPoint, _, _, _⟩ :=
    projectiveQLoopNativePairEquivalence_exists.{u, v, w} R
  exact (congrArg (fun f => f
    (BasedSplitExactQLoop.constantQLoop (C := FGProjectiveCat.{max u v} R))) hForward).symm.trans
      hPoint

end AlgebraicKTheory.QuillenPlus

end
