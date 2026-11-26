/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RamificationConductorsExistsLowerGroupEqBot

@[expose] public section

/-!
# Tests for termination of the lower ramification filtration

The termination theorem gives a positive bound beyond which all lower groups are trivial.

Authors: Jean-Pierre Serre.
Source: Corps Locaux, Chapter IV, §1;
https://doi.org/10.1007/978-1-4757-5673-9.
-/

namespace MathlibExtTest.AlgebraicGeometry.RamificationConductorsExistsLowerGroupEqBot

open ValuativeRel MathlibExt.NumberTheory.FiniteRamificationConductors

example (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L] :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → lowerGroup K L n = ⊥ := by
  obtain ⟨N, hN⟩ :=
    WantedExt.AlgebraicGeometry.RamificationConductors.exists_lowerGroup_eq_bot K L
  refine ⟨N + 1, Nat.succ_pos N, fun n hn => ?_⟩
  exact lowerGroup_eq_bot_of_bound K L N hN n ((Nat.le_succ N).trans hn)

end MathlibExtTest.AlgebraicGeometry.RamificationConductorsExistsLowerGroupEqBot
