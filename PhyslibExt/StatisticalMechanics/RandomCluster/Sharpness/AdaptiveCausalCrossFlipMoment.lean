/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalWeightedMoments
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalCrossBridge

/-!
# Cross-flip moment for extended decision-tree triples

The cross-flip moment of the extended decision-tree triple coupling equals the corresponding
weighted moment.

## i. Overview

Combines the weighted-moment identities with the cross bridge to evaluate the cross-flip moment of
`extendDecisionTreeTriple`. Unconditional for a positive probability weight `mu`.

## ii. Key results

- `cross_flip_moment_extendDecisionTreeTriple_eq`: the cross-flip moment identity.

## iii. Table of contents

- A. Cross-flip moment

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech
namespace OSSS
namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Cross-flip moment -/

lemma cross_flip_moment_extendDecisionTreeTriple_eq
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
