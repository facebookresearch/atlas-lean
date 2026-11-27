/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GameTheory.SocialChoice.HamiltonApportionment
import Mathlib.Data.Fintype.Powerset

/-! # Tests for Hamilton apportionment -/

open MathlibExt.GameTheory.SocialChoice.Hamilton

-- With common denominator 14, the lower quotas stay fixed while the remainder order reverses.
example : lowerQuota ![6, 6, 2] 10 = ![4, 4, 1] ∧ lowerQuota ![6, 6, 2] 11 = ![4, 4, 1] ∧
    remainderNumerator ![6, 6, 2] 10 = ![4, 4, 6] ∧
    remainderNumerator ![6, 6, 2] 11 = ![10, 10, 8] := by decide

-- Both vectors are attained. It is not just a restriction on hypothetical allocations.
example : IsHamilton ![6, 6, 2] 10 ![4, 4, 2] ∧ IsHamilton ![6, 6, 2] 11 ![5, 5, 1] :=
  ⟨(isHamilton_ten_iff _).2 rfl, (isHamilton_eleven_iff _).2 rfl⟩

-- The quotas (3½, 1½, 1) leave one seat for two tied states of *unequal* populations.
-- Giving it to the third state fills the house but violates the remainder ranking.
example : IsHamilton ![7, 3, 2] 6 ![4, 1, 1] ∧ IsHamilton ![7, 3, 2] 6 ![3, 2, 1] ∧
    ¬ IsHamilton ![7, 3, 2] 6 ![3, 1, 2] := by
  unfold IsHamilton IsAwardSet
  decide

-- No seats remain when every quota is integral; zero population in one state is harmless.
example : IsHamilton ![0, 3, 1] 4 ![0, 3, 1] ∧ ¬ IsHamilton ![0, 3, 1] 4 ![1, 2, 1] := by
  unfold IsHamilton IsAwardSet
  decide

-- A zero-size house is allowed for positive total population, not for zero total population.
example : IsHamilton ![0, 3, 1] 0 ![0, 0, 0] ∧ ¬ IsHamilton ![0, 0, 0] 0 ![0, 0, 0] := by
  unfold IsHamilton IsAwardSet
  decide
