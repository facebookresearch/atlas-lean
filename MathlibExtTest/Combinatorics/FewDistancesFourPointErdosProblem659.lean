/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FewDistancesFourPointErdosProblem659

namespace FewDistancesFourPointErdosProblem659Test

open MathlibExt.Combinatorics.FewDistancesFourPointErdosProblem659Wanted

-- The eventual statement supplies a set for each size beyond a threshold of at least four.
example : ∃ C : ℝ, ∃ N : ℕ, 4 ≤ N ∧ ∀ n ≥ N, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ (∀ S ⊆ P, S.card = 4 → 3 ≤ distinctDistances S) ∧
      (distinctDistances P : ℝ) ≤ C * n / Real.sqrt (Real.log n) := by
  obtain ⟨C, hC⟩ := fewDistancesWithFourPointCondition_holds
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hC
  exact ⟨C, max 4 N, le_max_left .., fun n hn => hN n ((le_max_right 4 N).trans hn)⟩

end FewDistancesFourPointErdosProblem659Test
