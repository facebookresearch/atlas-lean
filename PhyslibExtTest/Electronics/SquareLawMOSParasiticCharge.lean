/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.SquareLawMOSParasiticCharge
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

open PhyslibExt.Electronics.DynamicTerminalKCL
open PhyslibExt.Electronics.SquareLawMOSParasiticCharge

namespace PhyslibExtTest.Electronics.SquareLawMOSParasiticCharge

/-! ### Saturation, triode and cutoff -/

/-- Each forward regime contains a concrete bias point, so the path premise is satisfiable. -/
example : (![0, 1, 0] : Fin 3 → ℝ) ∈ forwardRegion 1 .cutoff ∧
    (![5, 1, 0] : Fin 3 → ℝ) ∈ forwardRegion 1 .triode ∧
    (![2, 5, 0] : Fin 3 → ℝ) ∈ forwardRegion 1 .saturation := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [forwardRegion] <;> norm_num

/-- Saturation drain current at `(2, 5, 0)` with `beta = 2`, `Vth = 1`: `beta * u^2 / 2 = 1`. -/
example : conductionCurrent 2 1 ![2, 5, 0] 1 = 1 := by
  rw [conductionCurrent_drain_of_saturation 2 1 _ (by simp [forwardRegion]; norm_num)]
  simp [PhyslibExt.Electronics.IdealSquareLawMOS.saturationCurrent]
  norm_num

/-- Triode drain current at `(5, 1, 0)` with `beta = 2`, `Vth = 1`: `2 * (4 * 1 - 1 / 2) = 7`. -/
example : conductionCurrent 2 1 ![5, 1, 0] 1 = 7 := by
  rw [conductionCurrent_drain_of_triode 2 1 _ (by simp [forwardRegion]; norm_num)]
  simp [PhyslibExt.Electronics.IdealSquareLawMOS.triodeCurrent]
  norm_num

/-- The source current is the negated drain current in saturation: `-1`. -/
example : conductionCurrent 2 1 ![2, 5, 0] 2 = -1 := by
  rw [(conductionCurrent_apply 2 1 _).2.2,
    conductionCurrent_drain_of_saturation 2 1 _ (by simp [forwardRegion]; norm_num)]
  simp [PhyslibExt.Electronics.IdealSquareLawMOS.saturationCurrent]
  norm_num

/-- Cutoff carries no drain current. -/
example : conductionCurrent 2 1 ![0, 1, 0] 1 = 0 :=
  conductionCurrent_drain_of_cutoff 2 1 _ (by simp [forwardRegion])

/-- The saturation bias path has gate displacement current `1` at time `0`, a nonzero
individual current, while the dynamic currents still sum to zero. -/
example : displacementCurrent 3 (parasiticCharge 1 1 1)
      (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 0 0 = 1 ∧
    ∑ i, dynamicTerminalCurrent 3 (parasiticCharge 1 1 1) (conductionCurrent 2 1)
      (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 0 i = 0 :=
  saturation_path_example.2

/-- The bundled statement applied to the saturation bias path, at time `3`. -/
example : ∑ i, dynamicTerminalCurrent 3 (parasiticCharge 1 1 1) (conductionCurrent 2 1)
    (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 3 i = 0 := by
  have hv : Differentiable ℝ (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> simp
  exact (squareLawMOSParasiticCharge_dynamicKCL 1 1 1 2 1 zero_le_one zero_le_one zero_le_one
    two_pos .saturation _ hv saturation_path_example.1).2.2.2.1 3

/-- The bundled statement's sign conclusions on the saturation bias path, at time `3`:
nonnegative stored energy and nonnegative drain current. -/
example : 0 ≤ parasiticEnergy 1 1 1 ((fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 3) ∧
    0 ≤ conductionCurrent 2 1 ((fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 3) 1 := by
  have hv : Differentiable ℝ (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> simp
  obtain ⟨-, -, -, -, hE, hI⟩ := squareLawMOSParasiticCharge_dynamicKCL 1 1 1 2 1 zero_le_one
    zero_le_one zero_le_one two_pos .saturation _ hv saturation_path_example.1
  exact ⟨hE 3, hI 3⟩

/-- A ramp on the gate with the drain held: the gate displacement current is `Cgs + Cgd`. -/
example : displacementCurrent 3 (parasiticCharge 2 3 5) (fun s : ℝ => ![s, 0, 0]) 1 0 = 5 := by
  have hv : Differentiable ℝ (fun s : ℝ => ![s, (0 : ℝ), 0]) := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> simp
  rw [(displacementCurrent_parasiticCharge 2 3 5 _ hv 1).1]
  simp
  norm_num

/-- The charge Jacobian sum rules hold at a bias point with no open-set premise: the drain
column sums to zero at `(2, 5, 0)`. -/
example : ∑ i, MetaMathlibExt.jacobianMatrix (parasiticCharge 2 3 5) ![2, 5, 0] i 1 = 0 :=
  (parasiticCharge_jacobian_sums_eq_zero 2 3 5 _).1 1

/-- The sum rules on any voltage set follow from the pointwise statement. -/
example (Cgs Cgd Cds : ℝ) (U : Set (Fin 3 → ℝ)) :
    ∀ w ∈ U,
      (∀ j, ∑ i, MetaMathlibExt.jacobianMatrix (parasiticCharge Cgs Cgd Cds) w i j = 0) ∧
        (∀ i, ∑ j, MetaMathlibExt.jacobianMatrix (parasiticCharge Cgs Cgd Cds) w i j = 0) :=
  fun w _ => parasiticCharge_jacobian_sums_eq_zero Cgs Cgd Cds w

/-! ### Flipped charge sign -/

/-- Flipping the gate charge sign gives total charge `-2` at `(1, 0, 0)` for
`Cgs = 1`, `Cgd = 0`, `Cds = 1`. -/
example : ∑ i, flippedGateCharge 1 0 1 ![1, 0, 0] i = -2 := by
  simp [flippedGateCharge, Fin.sum_univ_three]
  norm_num

/-- The static conservation failure, for concrete capacitances. -/
example : ∃ w : Fin 3 → ℝ, ∑ i, flippedGateCharge 1 0 1 w i ≠ 0 :=
  exists_sum_flippedGateCharge_ne_zero 1 0 1 one_pos le_rfl

/-- The dynamic law fails under the flipped sign, with the saturation device's currents. -/
example : ∑ i, dynamicTerminalCurrent 3 (flippedGateCharge 1 1 1) (conductionCurrent 2 1)
    (fun s : ℝ => ![s, 0, 0]) 0 i ≠ 0 :=
  flippedGateCharge_dynamic_sum_ne_zero 1 1 1 2 1 one_pos zero_le_one

/-- The unflipped charge map conserves charge at the same voltage. -/
example : ∑ i, parasiticCharge 1 0 1 ![1, 0, 0] i = 0 :=
  parasiticCharge_sum_eq_zero 1 0 1 _

/-! ### Negative capacitance -/

/-- The negative-capacitance device stores energy `-1/2` at `(1, 0, 0)`. -/
example : parasiticEnergy (-1) 0 1 ![1, 0, 0] = -1 / 2 := by
  norm_num [parasiticEnergy]

/-- Its dynamic currents still sum to zero, here along the saturation-shaped path. -/
example : ∑ i, dynamicTerminalCurrent 3 (parasiticCharge (-1) 0 1) (conductionCurrent 1 0)
    (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 1 i = 0 := by
  have hv : Differentiable ℝ (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) := by
    rw [differentiable_pi]
    intro i
    fin_cases i <;> simp
  exact negativeCapacitance_negative_energy_and_kcl.1 _ hv 1

/-- Nonnegative capacitances give nonnegative energy at the same voltage. -/
example : 0 ≤ parasiticEnergy 1 0 1 ![1, 0, 0] :=
  parasiticEnergy_nonneg 1 0 1 zero_le_one le_rfl zero_le_one _

/-- One negative capacitance does not by itself make the device active: `Cgs = -1/10`,
`Cgd = Cds = 1` stores nonnegative energy at every voltage. -/
example (w : Fin 3 → ℝ) : 0 ≤ parasiticEnergy (-1 / 10) 1 1 w := by
  unfold parasiticEnergy
  have h : w 1 - w 2 = (w 0 - w 2) - (w 0 - w 1) := by ring
  rw [h]
  nlinarith [sq_nonneg (9 * (w 0 - w 2) - 10 * (w 0 - w 1)), sq_nonneg (w 0 - w 1)]

/-- The charge-energy identity at `(1, 0, 0)` for the negative-capacitance device. -/
example : ∑ i, (![1, 0, 0] : Fin 3 → ℝ) i * parasiticCharge (-1) 0 1 ![1, 0, 0] i = -1 := by
  rw [sum_mul_parasiticCharge_eq_two_mul_energy]
  norm_num [parasiticEnergy]

end PhyslibExtTest.Electronics.SquareLawMOSParasiticCharge
