/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Independence.Blocks
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests for events determined by blocks of independent events

Four independent events split into the blocks `{0, 1}` and `{2, 3}`: an intersection of the first
two and a union of the last two are independent. With singleton blocks the original family is
recovered.
-/

@[expose] public section

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace MathlibExtTest.Probability.Independence.Blocks

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The block map `{0, 1} ↦ 0`, `{2, 3} ↦ 1`. -/
def halves (x : Fin 4) : Fin 2 := if (x : ℕ) < 2 then 0 else 1

/-- An intersection of the first two of four independent events is independent of a union of the
last two. -/
example {E : Fin 4 → Set Ω} (hE : ∀ x, MeasurableSet (E x)) (h : iIndepSet E μ) :
    μ ((E 0 ∩ E 1) ∩ (E 2 ∪ E 3)) = μ (E 0 ∩ E 1) * μ (E 2 ∪ E 3) := by
  have hmem (x : Fin 4) (i : Fin 2) (hx : halves x = i) :
      MeasurableSet[generateFrom (E '' (halves ⁻¹' {i}))] (E x) :=
    measurableSet_generateFrom ⟨x, hx, rfl⟩
  have hD : iIndepSet ![E 0 ∩ E 1, E 2 ∪ E 3] μ := by
    refine h.iIndepSet_of_measurableSet_generateFrom hE halves fun i => ?_
    fin_cases i
    · exact (hmem 0 0 rfl).inter (hmem 1 0 rfl)
    · exact (hmem 2 1 rfl).union (hmem 3 1 rfl)
  have := hD.meas_biInter Finset.univ
  rw [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero] at this
  convert this using 2
  ext ω
  simp [Fin.forall_fin_two]

/-- With singleton blocks, the events are the original independent events. -/
example {E : Fin 4 → Set Ω} (hE : ∀ x, MeasurableSet (E x)) (h : iIndepSet E μ) :
    iIndepSet E μ :=
  h.iIndepSet_of_measurableSet_generateFrom hE id fun i =>
    measurableSet_generateFrom ⟨i, rfl, rfl⟩

end MathlibExtTest.Probability.Independence.Blocks
