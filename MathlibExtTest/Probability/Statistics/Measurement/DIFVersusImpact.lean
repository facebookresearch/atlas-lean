/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.DIFVersusImpact

open scoped unitInterval
open MathlibExt.Probability.Statistics.Measurement

namespace MathlibExtTest.Probability.Statistics.Measurement.DIFVersusImpact

-- On the same scale, matching curves and latent laws force a zero gap at any universe.
example {Z : Type*} [Fintype Z] (π : PMF Z) (qA qB : Z → I) (hq : ∀ z, qA z = qB z) :
    itemSuccessMarginal π qA = itemSuccessMarginal π qB := by
  have h := dif_and_group_impact_independent.1 π π qA qB hq
  simpa only [sub_self, zero_mul, Finset.sum_const_zero, sub_eq_zero] using h

-- No implication from equal curves to equal observed marginals.
example : ∃ (πA πB : PMF (Fin 2)) (q : Fin 2 → I),
    itemSuccessMarginal πA q - itemSuccessMarginal πB q = -(1 / 4 : ℝ) := by
  obtain ⟨πA, πB, q, hA, hB⟩ := dif_and_group_impact_independent.{0}.2.1
  exact ⟨πA, πB, q, by rw [hA, hB]; norm_num⟩

-- No implication in the other direction, even with the same latent law.
example : ∃ (π : PMF (Fin 2)) (qA qB : Fin 2 → I),
    qA ≠ qB ∧ itemSuccessMarginal π qA = itemSuccessMarginal π qB := by
  obtain ⟨π, qA, qB, ⟨z, hz⟩, hA, hB⟩ := dif_and_group_impact_independent.{0}.2.2
  exact ⟨π, qA, qB, fun h => hz (congrFun h z), hA.trans hB.symm⟩

end MathlibExtTest.Probability.Statistics.Measurement.DIFVersusImpact
