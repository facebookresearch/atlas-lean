/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.InclusionExclusion

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.InclusionExclusion`

On configurations of `Fin 2`:
* `openEvent_increasing` and `openIndicator_mem` for the coordinate `0`;
* `cyl_indicator_signedIncreasingCombo` for the cylinder of the all-closed configuration on
  `univ`;
* `indicator_signedIncreasingCombo_of_dependsOn` for the decreasing event "coordinate `0` is
  closed", which depends only on `{0}`; `signedIncreasingCombo_iff` then unpacks it.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.InclusionExclusion

open _root_.StatMech _root_.StatMech.FK

-- "Coordinate `0` is open" is increasing and its indicator is a generator.
example : IsIncreasing {ω : ConfigSpace (Fin 2) | ω 0 = true} ∧
    ({ω : ConfigSpace (Fin 2) | ω 0 = true}).indicator 1 ∈ incrIndicators (Fin 2) :=
  ⟨openEvent_increasing 0, openIndicator_mem 0⟩

-- A cylinder indicator is a signed combination of increasing indicators.
example : SignedIncreasingCombo ((cyl Finset.univ (fun _ : Fin 2 => false)).indicator 1) :=
  cyl_indicator_signedIncreasingCombo _ _

/-- The indicator of "coordinate `0` is closed" depends only on `{0}`. -/
theorem closed0_dependsOn :
    DependsOn ({ω : ConfigSpace (Fin 2) | ω 0 = false}.indicator (1 : ConfigSpace (Fin 2) → ℝ))
      ((({0} : Finset (Fin 2))) : Set (Fin 2)) := by
  intro x y h
  have h0 : x 0 = y 0 := h 0 (by simp)
  simp only [Set.indicator, Set.mem_ofPred_eq, h0, Pi.one_apply]

/-- A decreasing local event is a signed combination of increasing indicators. -/
theorem closed0_combo :
    SignedIncreasingCombo ({ω : ConfigSpace (Fin 2) | ω 0 = false}.indicator 1) :=
  indicator_signedIncreasingCombo_of_dependsOn _ {0} closed0_dependsOn

-- The combination unpacks to an explicit finite signed sum.
example : ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (A : ι → Set (ConfigSpace (Fin 2))),
    (∀ i ∈ s, IsIncreasing (A i)) ∧
      {ω : ConfigSpace (Fin 2) | ω 0 = false}.indicator 1 =
        ∑ i ∈ s, c i • (A i).indicator (1 : ConfigSpace (Fin 2) → ℝ) :=
  (signedIncreasingCombo_iff _).mp closed0_combo

end PhyslibExtTest.StatisticalMechanics.RandomCluster.InclusionExclusion
