/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.Defs

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.Defs`

Tests the definitions of `StatMech.Universality`: `criticalProbability_eq_pc` at `d = 2`, the
increasing percolation event, `translateConfig` at `0` and the translated crossing events at `0`,
and the named predicate `PositivelyAssociated`, proved for the Dirac mass at the all-open
configuration (every nonempty increasing event contains it). `BoxCrossingProperty` is only
restated via `boxCrossingProperty_iff`: a witness needs crossings of all large rectangles.
-/

@[expose] public section

open MeasureTheory StatMech StatMech.Universality StatMech.Lattice StatMech.TwoDim
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.Defs

-- The real critical probability is `p_c`.
example : criticalProbability 2 = (Percolation.pc 2 : ℝ) := criticalProbability_eq_pc

example : IsIncreasing (percolationEvent 2) := percolationEvent_increasing

-- Translation by `0` is the identity.
example (ω : ConfigSpace (Sym2 (Site 2))) : translateConfig 0 ω = ω := translateConfig_zero ω

example : translatedHorizontalCrossingEvent 0 3 2 = horizontalCrossingEvent 3 2 := by simp

/-- The all-open configuration. -/
def allOpen : ConfigSpace (Sym2 (Site 2)) := fun _ => true

theorem allOpen_mem {A : Set (ConfigSpace (Sym2 (Site 2)))} (hA : IsIncreasing A)
    (hne : A.Nonempty) : allOpen ∈ A := by
  obtain ⟨a, ha⟩ := hne
  exact hA (fun _ => Bool.le_true _) ha

theorem dirac_real_of_increasing {A : Set (ConfigSpace (Sym2 (Site 2)))} (hA : IsIncreasing A)
    (hne : A.Nonempty) : (Measure.dirac allOpen).real A = 1 := by
  simp [Measure.real, Measure.dirac_apply_of_mem (allOpen_mem hA hne)]

-- `PositivelyAssociated` holds for the Dirac mass at the all-open configuration.
example : PositivelyAssociated (Measure.dirac allOpen) := by
  intro A B hA hB
  rcases A.eq_empty_or_nonempty with hAe | hAn
  · simp [hAe]
  rcases B.eq_empty_or_nonempty with hBe | hBn
  · simp [hBe]
  have hAB : (A ∩ B).Nonempty := ⟨allOpen, allOpen_mem hA hAn, allOpen_mem hB hBn⟩
  rw [dirac_real_of_increasing hA hAn, dirac_real_of_increasing hB hBn,
    dirac_real_of_increasing (IsUpperSet.inter hA hB) hAB]
  norm_num

-- `BoxCrossingProperty` unfolds to a positive infimum of crossing probabilities.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) :
    BoxCrossingProperty μ 2 ↔ 1 < (2 : ℝ) ∧ ∃ n0 : ℕ, 0 < sInf (boxCrossingProbabilities μ 2 n0) :=
  boxCrossingProperty_iff μ 2

end MathlibExtTest.StatMech.Probability.Percolation.Universality.Defs
