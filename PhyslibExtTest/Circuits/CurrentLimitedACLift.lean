/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.CurrentLimitedACLift
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open ComplexConjugate Matrix
open PhyslibExt.Circuits.ACInjectionLossBalance
open PhyslibExt.Circuits.CurrentLimitedACLift

namespace PhyslibExtTest.Circuits.CurrentLimitedACLift

/-! ### Concrete matrices of the two-bus fixture -/

/-- The two-bus bus admittance matrix is the unit Laplacian. -/
lemma admittance_eq : twoBusExample.admittance = !![1, -1; -1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [CurrentLimitedOPF.admittance, twoBusExample, busAdmittance, Matrix.diagonal]

/-- The lift of the witness `V = (1, 1/2)`. -/
lemma lift_eq : voltageLift 2 ![1, 1 / 2] = !![1, 1 / 2; 1 / 2, 1 / 4] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [voltageLift, Matrix.vecMulVec] <;>
    norm_num [Complex.ext_iff]

/-- Active coefficient matrix at bus `0`. -/
lemma active0 : activeCoeff 2 !![1, -1; -1, 1] 0 = !![1, -1 / 2; -1 / 2, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [activeCoeff, rowSelect, Matrix.conjTranspose_apply] <;> norm_num

/-- Active coefficient matrix at bus `1`. -/
lemma active1 : activeCoeff 2 !![1, -1; -1, 1] 1 = !![0, -1 / 2; -1 / 2, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [activeCoeff, rowSelect, Matrix.conjTranspose_apply] <;> norm_num

/-- Reactive coefficient matrix at bus `0`. -/
lemma reactive0 : reactiveCoeff 2 !![1, -1; -1, 1] 0 =
    !![0, 1 / (2 * Complex.I); -(1 / (2 * Complex.I)), 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [reactiveCoeff, rowSelect, Matrix.conjTranspose_apply]

/-- Voltage coefficient matrix at bus `0`. -/
lemma voltage0 : voltageCoeff 2 0 = !![1, 0; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [voltageCoeff]

/-- Branch-current coefficient matrix of the single branch. -/
lemma current0 : branchCurrentCoeff 2 1 twoBusExample.incidence
    twoBusExample.branchAdmittance 0 = !![1, -1; -1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [branchCurrentCoeff, twoBusExample]

/-- The pairing of two explicit `2 × 2` matrices. -/
lemma pairing_two (a b c d p q r s : ℂ) :
    pairing 2 !![a, b; c, d] !![p, q; r, s] = (a * p + b * r + (c * q + d * s)).re := by
  simp [pairing, Matrix.trace_fin_two_of]

/-! ### AC quantities at the witness, computed directly -/

/-- Absorbed complex power at bus `0`. -/
lemma power0 : nodeComplexPower 2 1 twoBusExample.incidence ![1, 1 / 2]
    twoBusExample.branchAdmittance twoBusExample.shuntAdmittance 0 = 1 / 2 := by
  simp [twoBusExample, nodeComplexPower,
    PhyslibExt.Circuits.BalancedThreePhase.complexPower, nodeInjection, branchDrop,
    Fin.sum_univ_two]
  norm_num [Complex.ext_iff]

/-- Absorbed complex power at bus `1`. -/
lemma power1 : nodeComplexPower 2 1 twoBusExample.incidence ![1, 1 / 2]
    twoBusExample.branchAdmittance twoBusExample.shuntAdmittance 1 = -1 / 4 := by
  simp [twoBusExample, nodeComplexPower,
    PhyslibExt.Circuits.BalancedThreePhase.complexPower, nodeInjection, branchDrop,
    Fin.sum_univ_two]
  norm_num [Complex.ext_iff]

/-- Branch drop on the single branch. -/
lemma drop0 : branchDrop 2 1 twoBusExample.incidence ![1, 1 / 2] 0 = 1 / 2 := by
  simp [twoBusExample, branchDrop, Fin.sum_univ_two]
  norm_num

/-! ### Coefficient pairings agree with the AC quantities -/

/-- Active pairing at bus `0` equals the directly computed active power `1/2`. -/
example : pairing 2 (activeCoeff 2 twoBusExample.admittance 0)
    (voltageLift 2 ![1, 1 / 2]) = 1 / 2 := by
  rw [admittance_eq, active0, lift_eq, pairing_two]
  norm_num

/-- Active pairing at bus `1` equals the directly computed active power `-1/4`. -/
example : pairing 2 (activeCoeff 2 twoBusExample.admittance 1)
    (voltageLift 2 ![1, 1 / 2]) = -1 / 4 := by
  rw [admittance_eq, active1, lift_eq, pairing_two]
  norm_num

/-- Reactive pairing at bus `0` vanishes, as does the reactive power. -/
example : pairing 2 (reactiveCoeff 2 twoBusExample.admittance 0)
    (voltageLift 2 ![1, 1 / 2]) = 0 := by
  rw [admittance_eq, reactive0, lift_eq, pairing_two]
  simp

/-- Voltage pairing at bus `0` is the squared magnitude `1`. -/
example : pairing 2 (voltageCoeff 2 0) (voltageLift 2 ![1, 1 / 2]) = 1 := by
  rw [voltage0, lift_eq, pairing_two]
  norm_num

/-- Branch-current pairing equals the squared branch current `1/4`. -/
example : pairing 2 (branchCurrentCoeff 2 1 twoBusExample.incidence
    twoBusExample.branchAdmittance 0) (voltageLift 2 ![1, 1 / 2]) = 1 / 4 := by
  rw [current0, lift_eq, pairing_two]
  norm_num

/-- The general exactness lemma gives the same branch current from the drop. -/
example : pairing 2 (branchCurrentCoeff 2 1 twoBusExample.incidence
    twoBusExample.branchAdmittance 0) (voltageLift 2 ![1, 1 / 2]) = 1 / 4 := by
  rw [pairing_branchCurrentCoeff_voltageLift, drop0]
  norm_num [twoBusExample, Complex.normSq_apply]

/-- Lifted-injection formula at bus `0`: `∑ j, conj (Y 0 j) * W 0 j = 1/2`. -/
example : liftedInjection 2 twoBusExample.admittance (voltageLift 2 ![1, 1 / 2]) 0 =
    1 / 2 := by
  rw [admittance_eq, lift_eq]
  simp [liftedInjection, Fin.sum_univ_two]
  norm_num

/-- The general lifted-injection theorem agrees with the direct power at bus `1`. -/
example : liftedInjection 2 twoBusExample.admittance (voltageLift 2 ![1, 1 / 2]) 1 =
    -1 / 4 := by
  rw [CurrentLimitedOPF.admittance, ← nodeComplexPower_eq_liftedInjection]
  exact power1

/-! ### Rank-one witness, rank-two point, rank bound, soundness and phase -/

/-- The rank-one witness is AC feasible, with relaxation-feasible lift and cost `1/4`. -/
example : acFeasible 2 1 twoBusExample ![1, 1 / 2] ∧
    sdpCost 2 1 twoBusExample (voltageLift 2 ![1, 1 / 2]) = 1 / 4 :=
  ⟨twoBus_rankOne_witness.1, twoBus_rankOne_witness.2.2.2⟩

/-- The identity is relaxation feasible and not a lift. -/
example : sdpFeasible 2 1 twoBusExample 1 ∧ voltageLift 2 ![1, 1 / 2] ≠ 1 :=
  ⟨twoBus_rankTwo_relaxed_not_lift.1, twoBus_rankTwo_relaxed_not_lift.2 _⟩

/-- The rank-two point has relaxation cost `2`, strictly above the witness cost. -/
example : sdpCost 2 1 twoBusExample (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  have hI : (1 : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; 0, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  rw [sdpCost, admittance_eq, hI]
  simp only [Fin.sum_univ_two, Fin.isValue]
  rw [active0, active1, pairing_two, pairing_two]
  simp [twoBusExample]
  norm_num

/-- Soundness: every lower bound on the relaxation cost bounds the witness cost `1/4`. -/
example (L : ℝ)
    (hL : ∀ W : Matrix (Fin 2) (Fin 2) ℂ, sdpFeasible 2 1 twoBusExample W →
      L ≤ sdpCost 2 1 twoBusExample W) : L ≤ 1 / 4 := by
  rw [← twoBus_rankOne_witness.2.2.1]
  exact (currentLimitedACLift_sound 2 1 twoBusExample).2 L hL _ twoBus_rankOne_witness.1

/-- Rank at most one: the witness lift is nonzero with rank at most one, while the zero
vector lifts to the zero matrix. -/
example : (voltageLift 2 ![1, 1 / 2]).rank ≤ 1 ∧ voltageLift 2 ![1, 1 / 2] ≠ 0 ∧
    voltageLift 2 0 = 0 := by
  refine ⟨voltageLift_rank_le_one 2 _, fun h => ?_, voltageLift_zero 2⟩
  have h00 := congrFun (congrFun h 0) 0
  rw [lift_eq] at h00
  simp at h00

/-- Global phase: multiplying the witness by `i` leaves its lift unchanged. -/
example : voltageLift 2 (fun k => Complex.I * (![1, 1 / 2] : Fin 2 → ℂ) k) =
    voltageLift 2 ![1, 1 / 2] :=
  voltageLift_unit_mul 2 _ Complex.I (by simp)

end PhyslibExtTest.Circuits.CurrentLimitedACLift
