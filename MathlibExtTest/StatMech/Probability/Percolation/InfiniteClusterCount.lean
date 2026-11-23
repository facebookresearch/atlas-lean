/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# Tests for `MathlibExt.Probability.Percolation.BurtonKeane`

Tests `StatMech.Percolation.numInfiniteClusters_ae_const` (the number of infinite clusters is a.s.
constant for a translation-ergodic probability measure; the Newman–Schulman step of Burton–Keane).
Its hypothesis `IsErgodic` is proved for the Dirac mass at the all-open configuration of `ℤ^d`, and
the theorem is applied at `d = 2`. The library does not prove ergodicity of the Bernoulli product
measure, so the theorem cannot yet be applied to Bernoulli percolation. Also checks
`numInfiniteClusters_shift` and `measurable_numInfiniteClusters`.
-/

@[expose] public section

open MeasureTheory StatMech StatMech.Percolation StatMech.Lattice StatMech.ConfigSpace

namespace MathlibExtTest.StatMech.Probability.Percolation.BurtonKeane

/-- The configuration of `ℤ^d` with every edge open. -/
def allOpen (d : ℕ) : ConfigSpace (Sym2 (Site d)) := fun _ => true

-- `allOpen` is fixed by every lattice translation.
theorem shift_allOpen (d : ℕ) (g : Multiplicative (Site d)) : shift g (allOpen d) = allOpen d :=
  rfl

-- The Dirac mass at `allOpen d` is translation-ergodic.
theorem isErgodic_dirac_allOpen (d : ℕ) :
    IsErgodic (G := Multiplicative (Site d)) (Measure.dirac (allOpen d)) := by
  refine ⟨fun g => ⟨measurable_shift g, ?_⟩, fun s hs _ => ?_⟩
  · rw [Measure.map_dirac' (measurable_shift g), shift_allOpen]
  · by_cases h : allOpen d ∈ s
    · right; rw [Measure.dirac_apply_of_mem h, measure_univ]
    · left; rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h]

-- The headline at `d = 2`, with the Dirac witness.
example : ∃ k : ℕ∞, (Measure.dirac (allOpen 2)) {ω | numInfiniteClusters 2 ω = k} = 1 :=
  numInfiniteClusters_ae_const _ (isErgodic_dirac_allOpen 2)

-- Translation invariance and measurability of `N`.
example (g : Multiplicative (Site 2)) (ω : ConfigSpace (Sym2 (Site 2))) :
    numInfiniteClusters 2 (shift g ω) = numInfiniteClusters 2 ω :=
  numInfiniteClusters_shift g ω

example : Measurable (numInfiniteClusters 1) := measurable_numInfiniteClusters

end MathlibExtTest.StatMech.Probability.Percolation.BurtonKeane
