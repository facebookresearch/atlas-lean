/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.BoxCrossing
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.BoxCrossing`

* `sqrt_trick_real` at `m = 1/2`, `s = 3/4`.
* `sqrt_trick` and `complFKG_union_bound` for a Dirac measure (complement FKG holds there).
* `square_crossing_ge_half` and `box_crossing_lower_bound` at `n = 0`, where every crossing of the
  one-site box is trivial; all hypotheses are discharged, including positive association of a
  Dirac measure. (For `n ≥ 2` the hypothesis `hdualExists` of `square_crossing_ge_half` is false,
  see its docstring, so `n = 0` is the meaningful witness.)
-/

@[expose] public section

open MeasureTheory StatMech StatMech.Lattice StatMech.RSW.Box StatMech.RSW.BoxCrossing
open StatMech.Universality

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.BoxCrossing

/-- A Dirac measure on bond configurations is positively associated. -/
theorem dirac_positivelyAssociated (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    PositivelyAssociated (Measure.dirac ω₀) := by
  intro A B _ _
  simp only [Measure.real, Measure.dirac_apply, Set.indicator]
  by_cases ha : ω₀ ∈ A <;> by_cases hb : ω₀ ∈ B <;> simp [ha, hb]

example : 1 - Real.sqrt (1 - 3 / 4) ≤ (1 / 2 : ℝ) :=
  sqrt_trick_real (by norm_num) (by norm_num)

/-- Complement FKG for a Dirac measure and two copies of the same event. -/
theorem dirac_complFKG (ω₀ : ConfigSpace (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2)))) :
    (Measure.dirac ω₀).real Aᶜ * (Measure.dirac ω₀).real Aᶜ
      ≤ (Measure.dirac ω₀).real (Aᶜ ∩ Aᶜ) := by
  simp only [Set.inter_self, Measure.real, Measure.dirac_apply, Set.indicator]
  by_cases h : ω₀ ∈ Aᶜ <;> simp [h]

example (ω₀ : ConfigSpace (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2))))
    (hA : MeasurableSet A) :
    1 - Real.sqrt (1 - (Measure.dirac ω₀).real (A ∪ A)) ≤ (Measure.dirac ω₀).real A :=
  sqrt_trick _ hA hA rfl (dirac_complFKG ω₀ A)

example (ω₀ : ConfigSpace (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2))))
    (hA : MeasurableSet A) :
    (Measure.dirac ω₀).real Aᶜ * (Measure.dirac ω₀).real Aᶜ ≤ 1 - (Measure.dirac ω₀).real (A ∪ A) :=
  complFKG_union_bound _ hA hA (dirac_complFKG ω₀ A)

/-- The origin of `ℤ²`. -/
def z0 : Site 2 := fun _ => 0

/-- Every configuration crosses the one-site box `[0, 0]²` horizontally. -/
theorem horizontalCrossing_zero (ω : ConfigSpace (Sym2 (Site 2))) :
    ω ∈ squareCrossingEvent 0 :=
  ⟨⟨z0, by simp [z0, mem_rect]⟩, ⟨z0, by simp [z0, mem_rect]⟩, connectedWithin_refl _ _ _⟩

/-- Every configuration has a dual vertical crossing of the one-site box `[0, 0]²`. -/
theorem dualCrossing_zero (ω : ConfigSpace (Sym2 (Site 2))) :
    ω ∈ squareDualCrossingEvent 0 :=
  ⟨⟨z0, by simp [z0, mem_rect]⟩, ⟨z0, by simp [z0, mem_rect]⟩, connectedWithin_refl _ _ _⟩

theorem squareCrossingEvent_zero : squareCrossingEvent 0 = Set.univ :=
  Set.eq_univ_of_forall horizontalCrossing_zero

theorem squareDualCrossingEvent_zero : squareDualCrossingEvent 0 = Set.univ :=
  Set.eq_univ_of_forall dualCrossing_zero

example (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    (1 : ℝ) / 2 ≤ (Measure.dirac ω₀).real (squareCrossingEvent 0) :=
  square_crossing_ge_half _ 0 (by simp [squareCrossingEvent_zero])
    (by rw [squareCrossingEvent_zero, squareDualCrossingEvent_zero])
    (by rw [squareCrossingEvent_zero]; exact MeasurableSet.univ)

theorem hz0 : z0 0 = (0 : ℤ) := rfl
theorem hzc : (0 : ℤ) ≤ z0 1 := le_rfl
theorem hzd : z0 1 ≤ (0 : ℤ) := le_rfl

theorem rectLeftHalfEvent_zero :
    rectLeftHalfEvent 0 le_rfl hz0 hzc hzd = Set.univ :=
  Set.eq_univ_of_forall fun _ =>
    ⟨⟨z0, by simp [z0, mem_rect]⟩, connectedWithin_refl _ _ _⟩

theorem rectRightHalfEvent_zero :
    rectRightHalfEvent 0 le_rfl hz0 hzc hzd = Set.univ :=
  Set.eq_univ_of_forall fun _ =>
    ⟨⟨z0, by simp [z0, mem_rect]⟩, connectedWithin_refl _ _ _⟩

example (ω₀ : ConfigSpace (Sym2 (Site 2))) :
    (1 : ℝ) / 4 ≤ (Measure.dirac ω₀).real (rectangleCrossingEvent 0) :=
  box_crossing_lower_bound _ (dirac_positivelyAssociated ω₀) 0 le_rfl hz0 hzc hzd
    (by rw [rectLeftHalfEvent_zero]; norm_num) (by rw [rectRightHalfEvent_zero]; norm_num)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.BoxCrossing
