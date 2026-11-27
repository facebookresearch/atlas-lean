/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluenceQOne

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluenceQOne`

On the complete graph on `Fin 2` (one edge) at `q = 1`:
* `activeZ_one_eq_one` and `active_openMarginal_one_eq` at `p = 1/2`;
* `activeInfluence_one_eq_influence` for the increasing event "the edge is open";
* `maxActiveInfluence_half` and `maxActiveInfluence_qOne_corrected` for that event.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluenceQOne

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.FK

instance : Nonempty (⊤ : SimpleGraph (Fin 2)).edgeSet := ⟨⟨s(0, 1), by simp⟩⟩

/-- The event "every edge is open". -/
def allOpen : Set (ConfigSpace (⊤ : SimpleGraph (Fin 2)).edgeSet) := {ω | ∀ e, ω e = true}

/-- "Every edge is open" is increasing. -/
theorem allOpen_isIncreasing : IsIncreasing allOpen := by
  intro x y hxy hx e
  have h := hxy e
  rw [hx e] at h
  exact top_le_iff.mp h

-- At `q = 1` the active partition function is `1`.
example : activeZ (⊤ : SimpleGraph (Fin 2)) (fun _ => (1 / 2 : ℝ)) 1 = 1 :=
  activeZ_one_eq_one _ (by norm_num) (by norm_num)

-- At `q = 1` every edge is open with probability `p`.
example (e : (⊤ : SimpleGraph (Fin 2)).edgeSet) :
    openMarginal (activeProb (⊤ : SimpleGraph (Fin 2)) (fun _ => (1 / 2 : ℝ)) 1) e = 1 / 2 :=
  active_openMarginal_one_eq _ (by norm_num) (by norm_num) e

-- Active influence is Bernoulli influence at `q = 1`.
example (e : (⊤ : SimpleGraph (Fin 2)).edgeSet) :
    activeInfluence ⊤ (1 / 3) 1 allOpen e = influence (1 / 3) allOpen e :=
  activeInfluence_one_eq_influence _ (by norm_num) (by norm_num) allOpen allOpen_isIncreasing e

-- KKL at `p = 1/2` for the active measure.
example := maxActiveInfluence_half (⊤ : SimpleGraph (Fin 2)) allOpen allOpen_isIncreasing

-- The corrected `p`-biased bound at `p = 1/3`.
example := maxActiveInfluence_qOne_corrected (⊤ : SimpleGraph (Fin 2)) (p := 1 / 3)
  (by norm_num) (by norm_num) allOpen allOpen_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.ActiveInfluenceQOne
