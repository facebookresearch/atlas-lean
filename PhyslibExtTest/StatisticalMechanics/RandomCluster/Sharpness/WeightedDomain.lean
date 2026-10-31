/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomain

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomain`

On the complete graph on `Fin 2` with edge parameters `1/2` and `q = 2`:
* `bcProbW_nonneg` and `bcProbW_sum_eq_one`: the weighted measure with free boundary is a
  probability mass function;
* `bcProbW_mono_bc`: the event "edge `s(0, 1)` is open" is more likely under the wired boundary
  graph `⊤` than the free one `⊥`;
* `weighted_transShellEvent_domain_dominated`: the lattice domination statement, as stated.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomain

open _root_.StatMech _root_.StatMech.FK

/-- The event "edge `s(0, 1)` is open". -/
def open01 : Set (ConfigSpace (Sym2 (Fin 2))) := {ω | ω s(0, 1) = true}

/-- "Edge `s(0, 1)` is open" is increasing. -/
theorem open01_isIncreasing : IsIncreasing open01 := by
  intro x y hxy hx
  have h := hxy s(0, 1)
  simp only [open01, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- The free weighted measure is nonnegative.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    0 ≤ bcProbW (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2 ω :=
  bcProbW_nonneg _ _ (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num) ω

-- The free weighted measure has total mass one.
example : ∑ ω, bcProbW (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2 ω = 1 :=
  bcProbW_sum_eq_one _ _ (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num)

-- Wiring the boundary makes the increasing event "`s(0, 1)` open" more likely.
example :
    (∑ ω, open01.indicator (fun _ => (1 : ℝ)) ω *
        bcProbW (⊤ : SimpleGraph (Fin 2)) ⊥ (fun _ => 1 / 2) 2 ω) ≤
      ∑ ω, open01.indicator (fun _ => (1 : ℝ)) ω *
        bcProbW (⊤ : SimpleGraph (Fin 2)) ⊤ (fun _ => 1 / 2) 2 ω :=
  bcProbW_mono_bc _ _ ⊤ bot_le (fun _ => by norm_num) (fun _ => by norm_num) (by norm_num)
    open01_isIncreasing

-- The translated-shell domination is available as stated.
example := @OSSS.FKSharpnessWeightedDomain.weighted_transShellEvent_domain_dominated

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedDomain
