/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55

open scoped BigOperators
open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook55Wanted

namespace MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook55

/-- Unpack the refutation into Banach-space data with no factorisation. -/
example : ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E)
    (_ : CompleteSpace E) (R : Set E) (n : ℕ)
    (P : (j : Fin (n + 1)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => E) ℝ),
    (∀ M : ℝ, ∃ r ∈ R, M < ‖r‖) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ x : E, (∃ r ∈ R, dist x r < ε) → |∑ j, P j (fun _ => x)| ≤ C) ∧
    ¬ ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : NormedSpace ℝ F)
      (L : E →L[ℝ] F) (a : F) (d : ℕ)
      (A : (j : Fin (d + 1)) →
        ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => F) ℝ),
      (∀ x : E, (∑ j, P j (fun _ => x)) = ∑ j, A j (fun _ => L x + a)) ∧
      ∃ M : ℝ, ∀ r ∈ R, ‖L r + a‖ ≤ M := by
  by_contra h
  push Not at h
  exact mazur55_refuted h

end MathlibExtTest.Analysis.FunctionalAnalysis.ScottishBook55
