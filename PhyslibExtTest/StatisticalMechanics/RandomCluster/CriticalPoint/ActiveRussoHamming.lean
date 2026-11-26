/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveRussoHamming

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveRussoHamming`

On the complete graph on `Fin 2` (one edge) at `q = 2` with the increasing event "every edge is
open":
* `active_russoHamming` at `p = 1/2`;
* `active_russoHammingIntegrated` at `p₁ = 1/3`, `p₂ = 2/3`;
* both headlines are unconditional and are applied at explicit parameters.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveRussoHamming

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.FK

/-- The event "every edge is open". -/
def allOpen : Set (ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet) := {ω | ∀ e, ω e = true}

/-- "Every edge is open" is increasing. -/
theorem allOpen_isIncreasing : IsIncreasing allOpen := by
  intro x y hxy hx e
  have h := hxy e
  rw [hx e] at h
  exact top_le_iff.mp h

-- The Russo–Hamming derivative bound at `p = 1/2`, `q = 2`.
example := active_russoHamming (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num) allOpen allOpen_isIncreasing

-- The integrated comparison between `p₁ = 1/3` and `p₂ = 2/3`.
example := active_russoHammingIntegrated (⊤ : SimpleGraph (Fin 2)) (p₁ := 1 / 3) (p₂ := 2 / 3)
  (q := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) allOpen allOpen_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveRussoHamming
