/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluence

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluence`

On the complete graph on `Fin 2` (one edge) with the increasing event "every edge is open":
* `activeInfluence_nonneg` at `p = 1/2`, `q = 2`;
* `active_reducedDensity_le_openMarginal` at `p = 1/2`, `q = 2`;
* `active_deriv_ge_total_influence` at `ε = 1/4`, `p = 1/2`, `q = 2`;
* `activeCov_eq_marginal_mul_influence` at `p = 1/2`, `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluence

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.FK

/-- The event "every edge is open". -/
def allOpen : Set (ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet) := {ω | ∀ e, ω e = true}

/-- "Every edge is open" is increasing. -/
theorem allOpen_isIncreasing : IsIncreasing allOpen := by
  intro x y hxy hx e
  have h := hxy e
  rw [hx e] at h
  exact top_le_iff.mp h

-- Influences of an increasing event are nonnegative.
example (e : (⊤ : SimpleGraph (Fin 2)).edgeSet) : 0 ≤ activeInfluence ⊤ (1 / 2) 2 allOpen e :=
  activeInfluence_nonneg _ (by norm_num) (by norm_num) (by norm_num) allOpen allOpen_isIncreasing e

-- The open marginal is at least the reduced density.
example (e : (⊤ : SimpleGraph (Fin 2)).edgeSet) := active_reducedDensity_le_openMarginal
  (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) e

-- The Russo-type derivative bound.
example := active_deriv_ge_total_influence (⊤ : SimpleGraph (Fin 2)) (ε := 1 / 4) (p := 1 / 2)
  (q := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) allOpen allOpen_isIncreasing

-- Covariance with an edge coordinate is marginal variance times influence.
example (e : (⊤ : SimpleGraph (Fin 2)).edgeSet) := activeCov_eq_marginal_mul_influence
  (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
  allOpen e

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluence
