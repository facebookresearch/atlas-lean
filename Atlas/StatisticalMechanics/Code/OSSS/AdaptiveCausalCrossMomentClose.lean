/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.OSSS.AdaptiveCausalWeightedMoments
import Code.OSSS.AdaptiveCausalCrossBridge

open scoped BigOperators

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]




theorem cross_flip_moment_extendDecisionTreeTriple_eq
    (mu : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < mu ω)
    (hmu : ∑ ω, mu ω = 1) (T : DecisionTree E)
    (seed : ConfigSpace E) (t : ℕ) (e : E) :
    let S := extendDecisionTreeTriple (some t) T seed
      (Finset.univ : Finset E)
    (∑ base,
      (if tripleModeAt S base e = .flip then 1 else 0) *
        (∑ left, ∑ right,
          (T.evalR left * Lindeberg.coord e right +
            T.evalR right * Lindeberg.coord e left) *
            crossTripleJointProb mu ∅ base left right S)) =
      2 * (Lindeberg.mean mu T.evalR *
        Lindeberg.mean mu (Lindeberg.coord e)) *
          flipBaseProb mu ∅ seed e S := by
  dsimp only
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)
  rw [cross_flip_atom_sum_eq_flipCrossTripleProb_sum
    mu seed e S
      (fun left right => T.evalR left * Lindeberg.coord e right +
        T.evalR right * Lindeberg.coord e left)]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have h := flipCrossTripleProb_structured_orientations
    mu hpos hmu T seed t e
  dsimp only at h
  rw [h.1, h.2]
  ring

end AdaptiveCausalKernel
end OSSS
end StatMech
