/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.ZhangRotSymmetry
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.ZhangRotSymmetry`

* `zrs_rotConfig_apply`, `zrs_rotConfig_monotone`, `zrs_rotPreimage_measureReal`.
* `zrs_sideFamily` on the increasing event "the pair `e` is open": its four members are increasing,
  measurable and of equal `halfMeasure`-probability (`zrs_side_symmetry`).
* `zrs_geometricData_of_remaining` for `base = univ`, `Err = ∅`, `A = B = univ`.
  `zrs_zhangUnion_of_remaining` is not instantiated: it needs `PositivelyAssociated halfMeasure`,
  which the library does not prove.
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
open StatMech StatMech.Lattice StatMech.Universality StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.ZhangRotSymmetry

/-- The increasing event that a given pair is open. -/
def openAt (e : Sym2 (Site 2)) : Set (ConfigSpace (Sym2 (Site 2))) := {ω | ω e = true}

theorem openAt_inc (e : Sym2 (Site 2)) : IsIncreasing (openAt e) := by
  intro ω ω' h hω
  have := h e
  simp only [openAt, Set.mem_ofPred_eq] at hω ⊢
  rw [hω] at this
  exact le_antisymm le_top this

theorem openAt_meas (e : Sym2 (Site 2)) : MeasurableSet (openAt e) :=
  measurableSet_eq_fun (measurable_pi_apply e) measurable_const

example (e : Sym2 (Site 2)) : kdi_rotConfig (fun _ => true) e = true := by
  rw [zrs_rotConfig_apply]

example : Monotone kdi_rotConfig := zrs_rotConfig_monotone

example (e : Sym2 (Site 2)) (i : Fin 4) : IsIncreasing (zrs_sideFamily (openAt e) i) :=
  zrs_sideFamily_isIncreasing (openAt_inc e) i

example (e : Sym2 (Site 2)) (i : Fin 4) :
    halfMeasure.real (zrs_sideFamily (openAt e) i) = halfMeasure.real (openAt e) :=
  zrs_side_symmetry (openAt_meas e) i

example (e : Sym2 (Site 2)) :
    halfMeasure.real (kdi_rotConfig ⁻¹' openAt e) = halfMeasure.real (openAt e) :=
  zrs_rotPreimage_measureReal (openAt_meas e)

theorem sideFamily_univ (i : Fin 4) :
    zrs_sideFamily (Set.univ : Set (ConfigSpace (Sym2 (Site 2)))) i = Set.univ := by
  fin_cases i <;> rfl

example : ZhangGeometricData halfMeasure (fun _ => Set.univ) (fun _ => Set.univ) :=
  zrs_geometricData_of_remaining (fun _ => Set.univ) (fun _ => ∅) (fun _ => isUpperSet_univ)
    (fun _ => MeasurableSet.univ) (by simp)
    (by simp only [sideFamily_univ, Set.union_self, probReal_univ]; exact tendsto_const_nhds)
    (fun _ => by simp)

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.ZhangRotSymmetry
