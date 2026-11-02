/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianCompactCylinderIntersection
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianCompactCylinderIntersection`

* `nonempty_iInter_cylinder_of_compact` for the constant sequence of cylinders over the compact
  base `{fun _ => 0}` at index set `{0}`.
* `cylinderPrefixSupport` of a constant sequence of index sets.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianCompactCylinderIntersection

example : (⋂ _n : ℕ, (cylinder ({0} : Finset ℝ) {fun _ => (0 : ℝ)} : Set (ℝ → ℝ))).Nonempty :=
  nonempty_iInter_cylinder_of_compact (fun _ => {0}) (fun _ => {fun _ => 0})
    (fun _ => isCompact_singleton) (fun _ => Set.singleton_nonempty _) antitone_const

example (n : ℕ) : cylinderPrefixSupport (fun _ => ({0} : Finset ℝ)) n = {0} := by
  ext t; simp only [cylinderPrefixSupport, Finset.mem_biUnion, Finset.mem_range]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, by omega, h⟩⟩

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianCompactCylinderIntersection
