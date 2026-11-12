/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.InfiniteVolume

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.InfiniteVolume`

* `boxFinset d 0` is the single site `0`, and `boxFinset 1 1` has three sites.
* `glue` keeps the boundary condition outside the box.
* The plus-boundary box measure `plusMeasure` gives probability `0` to a minus spin outside the
  box, and the minus-boundary measure gives probability `0` to a plus spin there: the boundary
  conditions are really imposed.
* `InfiniteVolumeState` holds for a constant sequence and its value (so the predicate is
  satisfiable), and `plusState`, `minusState`, `freeState` are infinite-volume states of their box
  sequences.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.InfiniteVolume

open MeasureTheory
open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

-- The box of radius `0` is the single site `0`.
example (d : ℕ) (x : Site d) : x ∈ boxFinset d 0 ↔ x = 0 := by
  simp only [mem_boxFinset, mem_box, Nat.le_zero, Int.natAbs_eq_zero]
  exact ⟨fun h => funext h, fun h i => by simp [h]⟩

-- Outside the box, `glue` is the boundary condition.
example (d n : ℕ) (τ : {x // x ∈ box d n} → Bool) (x : Site d) (hx : x ∉ box d n) :
    glue (plusField d) τ x = true := by
  simp [glue, hx, plusField]

/-- A finite-volume measure puts no mass on configurations that disagree with the boundary
condition `η` at a site `x` outside the box. -/
lemma fvMeasure_disagree_outside (d n : ℕ) (η : ConfigSpace (Site d))
    (B : Finset (Sym2 (Site d))) (β h : ℝ) (x : Site d) (hx : x ∉ box d n) :
    fvMeasure η n B β h {ω | ω x ≠ η x} = 0 := by
  have hmeas : MeasurableSet {ω : ConfigSpace (Site d) | ω x ≠ η x} :=
    (measurableSet_singleton (η x)).compl.preimage (measurable_pi_apply x)
  unfold fvMeasure
  rw [Measure.finsetSum_apply _ _ _]
  refine Finset.sum_eq_zero fun τ _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem, smul_zero]
  simp [glue, hx]

-- The plus-boundary measure has no minus spin outside the box.
example (d n : ℕ) (β h : ℝ) (x : Site d) (hx : x ∉ box d n) :
    (plusMeasure d n β h : Measure (ConfigSpace (Site d))) {ω | ω x = false} = 0 := by
  have := fvMeasure_disagree_outside d n (plusField d) (bondFinsetTouch d n) β h x hx
  simp only [plusField, ne_eq, Bool.not_eq_true] at this
  exact this

-- The minus-boundary measure has no plus spin outside the box.
example (d n : ℕ) (β h : ℝ) (x : Site d) (hx : x ∉ box d n) :
    (minusMeasure d n β h : Measure (ConfigSpace (Site d))) {ω | ω x = true} = 0 := by
  have := fvMeasure_disagree_outside d n (minusField d) (bondFinsetTouch d n) β h x hx
  simp only [minusField, ne_eq, Bool.not_eq_false] at this
  exact this

-- `InfiniteVolumeState` is satisfiable: a constant sequence has its value as a state.
example (d : ℕ) (μ : ProbabilityMeasure (ConfigSpace (Site d))) :
    InfiniteVolumeState (fun _ => μ) μ :=
  ⟨id, strictMono_id, tendsto_const_nhds⟩

-- The plus, minus and free states are infinite-volume states of their box sequences.
example (β h : ℝ) :
    InfiniteVolumeState (fun n => plusMeasure 2 n β h) (plusState 2 β h) ∧
      InfiniteVolumeState (fun n => minusMeasure 2 n β h) (minusState 2 β h) ∧
      InfiniteVolumeState (fun n => freeMeasure 2 n β h) (freeState 2 β h) :=
  ⟨plusState_isInfiniteVolumeState 2 β h, minusState_isInfiniteVolumeState 2 β h,
    freeState_isInfiniteVolumeState 2 β h⟩

end PhyslibExtTest.CondensedMatter.IsingModel.InfiniteVolume
