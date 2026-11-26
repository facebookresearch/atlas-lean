/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69

/-!
# A counterexample corollary for Scottish Book Problem 69

The refutation theorem gives a nonempty complete space with both metric center properties
that is not isometric to any real Banach space.

Source: S. Mazur and S. Ulam, Problem 69 of the Scottish Book; typescript Ad 69 records the
negative answer (S. Mazur, December 21, 1936).
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook69

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook69Wanted

example : ∃ (E : Type) (_ : PseudoMetricSpace E) (_ : CompleteSpace E) (_ : Nonempty E),
    (∀ p q : E, ∃! c, IsMetricCenter E p q c) ∧
    (∀ p q : E, ∃! x, IsMetricCenter E p x q) ∧
    ¬ ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (_ : CompleteSpace F), Nonempty (E ≃ᵢ F) := by
  classical
  by_contra h
  apply mazurUlam69_refuted
  intro E _ _ _ hc hx
  by_contra hn
  exact h ⟨E, inferInstance, inferInstance, inferInstance, hc, hx, hn⟩

end MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook69
