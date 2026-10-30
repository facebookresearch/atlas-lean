/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.SelfDualDichotomy
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.SelfDualDichotomy`

* `kdi_rotConfig_measurePreserving`.
* `kdi_crossing_balance_family` with `R = id` and `kdi_crossing_balance_family_rot` (with the
  quarter-turn rotation) for the event "the diagonal pair `s(0, 0)` is open", which both maps
  exchange with its complement; its `halfMeasure`-probability is `1/2`. (For events that depend
  only on nearest-neighbour edges the `_rot` hypothesis fails, see the source docstring; the
  diagonal pair is fixed by the rotation, which is why this event works.)
-/

@[expose] public section

open Filter MeasureTheory
open scoped NNReal Topology
open StatMech StatMech.Lattice StatMech.Percolation StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.SelfDualDichotomy

/-- The diagonal pair at the origin. -/
def e0 : Sym2 (Site 2) := s(fun _ => 0, fun _ => 0)

/-- The event that `e0` is open. -/
def H : Set (ConfigSpace (Sym2 (Site 2))) := {ω | ω e0 = true}

theorem measurableSet_H : MeasurableSet H :=
  measurableSet_eq_fun (measurable_pi_apply e0) measurable_const

theorem crossEdge_symm_e0 : crossEdge.symm e0 = e0 := by
  apply crossEdge.injective
  rw [Equiv.apply_symm_apply]
  simp [e0, crossEdge, sym2Congr, rot90Equiv, rot90Fun]
  funext i; fin_cases i <;> rfl

theorem H_compl_id : Hᶜ = (id ∘ dualConfig) ⁻¹' H := by
  ext ω
  simp only [H, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, id,
    dual_isOpen_iff_isClosed, crossEdge_symm_e0, Bool.not_eq_true]

theorem H_compl_rot : Hᶜ = (kdi_rotConfig ∘ dualConfig) ⁻¹' H := by
  ext ω
  have h1 : kdi_rotConfig (dualConfig ω) e0 = dualConfig ω e0 := by
    simp only [kdi_rotConfig, Equiv.piCongrLeft_apply, eq_rec_constant, crossEdge_symm_e0]
  simp only [H, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, h1,
    dual_isOpen_iff_isClosed, crossEdge_symm_e0, Bool.not_eq_true]

example : MeasurePreserving kdi_rotConfig Universality.halfMeasure Universality.halfMeasure :=
  kdi_rotConfig_measurePreserving

example : Universality.halfMeasure.real H = 1 / 2 :=
  kdi_crossing_balance_family (boxFam := fun _ => H) (R := id) (fun _ => measurableSet_H)
    measurable_id Measure.map_id (fun _ => H_compl_id) 0

example : Universality.halfMeasure.real H = 1 / 2 :=
  kdi_crossing_balance_family_rot (boxFam := fun _ => H) (fun _ => measurableSet_H)
    (fun _ => H_compl_rot) 0

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.SelfDualDichotomy
