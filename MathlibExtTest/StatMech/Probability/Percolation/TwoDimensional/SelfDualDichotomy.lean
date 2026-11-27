/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.SelfDualDichotomy
public import Mathlib.Tactic

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.SelfDualDichotomy`

* `kdi_rotConfig_measurePreserving`.
* `kdi_crossing_balance_family` with `R = id` and `R = kdi_rotConfig` for the event "the loop
  `s(0, 0)` is open". Both maps exchange this event with its complement, so its
  `halfMeasure`-probability is `1/2`. The loop is not a nearest-neighbour bond.
* The closed-east/open-west configuration refutes the rotation/complement dichotomy for the
  east-bond event. This is a single-bond counterexample, not a proof about every crossing event.
* Inverse coordinate rotation cancels the coordinate permutation in `dualConfig`. This gives a
  genuine nearest-neighbour bond witness for the general-`R` balance theorem.
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
  kdi_crossing_balance_family (boxFam := fun _ => H) (R := kdi_rotConfig)
    (fun _ => measurableSet_H) kdi_measurable_rotConfig kdi_map_rotConfig
    (fun _ => H_compl_rot) 0

/-- The east-pointing nearest-neighbour bond at the origin. -/
private def eastEdge : Sym2 (Site 2) := s(![0, 0], ![1, 0])

/-- The west-pointing nearest-neighbour bond at the origin. -/
private def westEdge : Sym2 (Site 2) := s(![0, 0], ![-1, 0])

example : NearestNeighbour 2 ![0, 0] ![1, 0] := by
  unfold NearestNeighbour
  decide

example : NearestNeighbour 2 ![0, 0] ![-1, 0] := by
  unfold NearestNeighbour
  decide

private lemma east_west_ne : eastEdge ≠ westEdge := by decide

private lemma half_turn_east : crossEdge.symm (crossEdge.symm eastEdge) = westEdge := by
  decide

/-- The event that the east bond is open. -/
private def bondEvent : Set (ConfigSpace (Sym2 (Site 2))) := {ω | ω eastEdge = true}

/-- Only the west bond is open, so the east bond is closed. -/
private def oppositeConfig : ConfigSpace (Sym2 (Site 2)) := fun e => decide (e = westEdge)

private lemma not_bond_rot_dichotomy :
    bondEventᶜ ≠ (kdi_rotConfig ∘ dualConfig) ⁻¹' bondEvent := by
  intro h
  have hm : oppositeConfig ∈ bondEventᶜ := by
    simp [bondEvent, oppositeConfig, east_west_ne]
  rw [h] at hm
  change kdi_rotConfig (dualConfig oppositeConfig) eastEdge = true at hm
  have ht : kdi_rotConfig (dualConfig oppositeConfig) eastEdge = false := by
    simp [kdi_rotConfig, Equiv.piCongrLeft_apply, dualConfig, half_turn_east, oppositeConfig]
  rw [ht] at hm
  cases hm

/-- Inverse quarter-turn coordinate permutation, used only for this bond-event witness. -/
private noncomputable def invRotConfig :
    ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2)) :=
  Equiv.piCongrLeft (fun _ => Bool) crossEdge.symm

private lemma invRot_dual_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    invRotConfig (dualConfig ω) e = !(ω e) := by
  simp [invRotConfig, Equiv.piCongrLeft_apply, dualConfig]

private lemma invRot_measurePreserving :
    MeasurePreserving invRotConfig Universality.halfMeasure Universality.halfMeasure := by
  refine ⟨(MeasurableEquiv.piCongrLeft (fun _ => Bool) crossEdge.symm).measurable, ?_⟩
  rw [invRotConfig, Universality.halfMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : ℝ≥0) (by norm_num)) crossEdge.symm

private lemma bond_compl_invRot : bondEventᶜ = (invRotConfig ∘ dualConfig) ⁻¹' bondEvent := by
  ext ω
  simp [bondEvent, invRot_dual_apply]

example : Universality.halfMeasure.real bondEvent = 1 / 2 :=
  kdi_crossing_balance_family (boxFam := fun _ => bondEvent) (R := invRotConfig)
    (fun _ => measurableSet_eq_fun (measurable_pi_apply eastEdge) measurable_const)
    invRot_measurePreserving.measurable invRot_measurePreserving.map_eq
    (fun _ => bond_compl_invRot) 0

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.SelfDualDichotomy

assert_not_exists StatMech.TwoDim.kdi_selfDual_crossing_half_rot
assert_not_exists StatMech.TwoDim.kdi_crossing_balance_family_rot
