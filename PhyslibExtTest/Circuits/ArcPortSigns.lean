/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import PhyslibExt.Circuits.ArcPortSigns
import Mathlib.Tactic.NormNum

@[expose] public section

open Matrix
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.TellegenPowerBalance

namespace PhyslibExtTest.Circuits.ArcPortSigns

/-- Electrical incidence entries on the two-node branch: tail node `0`
contributes `+1`, head node `1` contributes `-1`. -/
example : electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1] 0 0 = 1 := by
  rw [electricalIncidence_apply]
  norm_num

example : electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1] 1 0 = -1 := by
  rw [electricalIncidence_apply]
  norm_num

/-- Branch voltage from potentials on the two-node branch: potentials
`3` and `1` give branch voltage `2`, through the public voltage lemma. -/
example : (![2] : Fin 1 → ℝ) 0 = 3 - 1 := by
  have h := branchVoltage_eq_tail_sub_head (V := Fin 2) (E := Fin 1) ![0] ![1]
    ![3, 1] ![2] (by
      ext e
      fin_cases e
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
        Fin.sum_univ_two]
      norm_num) 0
  simpa using h

/-- Two-node power balance through the shared Tellegen theorem applied to
the electrical incidence: one branch from node `0` to node `1`, potentials
`3` and `1`, branch current `5`. Branch power and node power are both
`10`, in sum form and in dot-product form. -/
example :
    (∑ e : Fin 1, (![2] : Fin 1 → ℝ) e * (![5] : Fin 1 → ℝ) e) =
      ∑ n : Fin 2, (![3, 1] : Fin 2 → ℝ) n * (![5, -5] : Fin 2 → ℝ) n :=
  branchPower_eq_nodePower (electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1])
    ![3, 1] ![5, -5] ![2] ![5]
    (by
      ext e
      fin_cases e
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
        Fin.sum_univ_two]
      norm_num)
    (by
      ext n
      fin_cases n <;>
        simp [Matrix.mulVec, dotProduct, electricalIncidence_apply])

example : (![2] : Fin 1 → ℝ) ⬝ᵥ (![5] : Fin 1 → ℝ) =
    (![3, 1] : Fin 2 → ℝ) ⬝ᵥ (![5, -5] : Fin 2 → ℝ) :=
  branchPower_eq_nodePower (electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1])
    ![3, 1] ![5, -5] ![2] ![5]
    (by
      ext e
      fin_cases e
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
        Fin.sum_univ_two]
      norm_num)
    (by
      ext n
      fin_cases n <;>
        simp [Matrix.mulVec, dotProduct, electricalIncidence_apply])

/-- Three-node cycle through the shared Tellegen theorem: three branches
forming a directed cycle, unit current on each, potentials `3`, `1`, `0`.
The nodal injection is zero and total branch power is zero. -/
example :
    (∑ e : Fin 3, (![2, 1, -3] : Fin 3 → ℝ) e * (![1, 1, 1] : Fin 3 → ℝ) e) =
      ∑ n : Fin 3, (![3, 1, 0] : Fin 3 → ℝ) n * (![0, 0, 0] : Fin 3 → ℝ) n :=
  branchPower_eq_nodePower
    (electricalIncidence (V := Fin 3) (E := Fin 3) ![0, 1, 2] ![1, 2, 0])
    ![3, 1, 0] ![0, 0, 0] ![2, 1, -3] ![1, 1, 1]
    (by
      ext e
      fin_cases e <;>
        norm_num [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
          electricalIncidence_apply, Fin.sum_univ_three])
    (by
      ext n
      fin_cases n <;>
        simp [Matrix.mulVec, dotProduct, electricalIncidence_apply, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

/-- Flipped current: reversing both voltage and current preserves branch
power, while flipping the current alone breaks the two-node balance. -/
example : Function.update (![2] : Fin 1 → ℝ) 0 (-(![2] : Fin 1 → ℝ) 0) ⬝ᵥ
    Function.update (![5] : Fin 1 → ℝ) 0 (-(![5] : Fin 1 → ℝ) 0) =
    (![2] : Fin 1 → ℝ) ⬝ᵥ (![5] : Fin 1 → ℝ) :=
  branchPower_reversedBranch_eq ![2] ![5] 0

/-- With the incidence, the potentials and the injection held fixed, the
flipped current violates current balance at both nodes, and the power
identity fails. -/
example :
    electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1] *ᵥ (![-5] : Fin 1 → ℝ) ≠
        ![5, -5] ∧
      (![2] : Fin 1 → ℝ) ⬝ᵥ (![-5] : Fin 1 → ℝ) ≠
        (![3, 1] : Fin 2 → ℝ) ⬝ᵥ (![5, -5] : Fin 2 → ℝ) := by
  refine ⟨fun h => ?_, ?_⟩
  · have h0 := congrFun h 0
    simp [Matrix.mulVec, dotProduct, electricalIncidence_apply] at h0
    norm_num at h0
  · simp only [dotProduct, Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num

/-- Simultaneous reversal on the two-node branch preserves the nodal
injection, through the public reversal lemma. -/
example :
    electricalIncidence (V := Fin 2) (E := Fin 1)
        (Function.update (![0] : Fin 1 → Fin 2) 0 1)
        (Function.update (![1] : Fin 1 → Fin 2) 0 0) *ᵥ
      Function.update (![5] : Fin 1 → ℝ) 0 (-5) =
    electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![1] *ᵥ ![5] :=
  mulVec_reversedBranch_eq (V := Fin 2) (E := Fin 1) ![0] ![1] ![5] 0

/-- Two-branch path `0 → 1 → 2` with current `5` on each branch: the
nodal injection is `5`, `0`, `-5`. -/
lemma path_kcl :
    electricalIncidence (V := Fin 3) (E := Fin 2) ![0, 1] ![1, 2] *ᵥ (![5, 5] : Fin 2 → ℝ) =
      ![5, 0, -5] := by
  ext n
  fin_cases n <;>
    norm_num [Matrix.mulVec, dotProduct, electricalIncidence_apply, Fin.sum_univ_two]

/-- The same path with potentials `3`, `1`, `0`: branch voltages are `2`
and `1`. -/
lemma path_kvl :
    (![2, 1] : Fin 2 → ℝ) =
      (electricalIncidence (V := Fin 3) (E := Fin 2) ![0, 1] ![1, 2]).transpose *ᵥ
        ![3, 1, 0] := by
  ext e
  fin_cases e <;>
    norm_num [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
      Fin.sum_univ_three]

/-- The path current after flipping branch `0`. -/
lemma path_reversed_current :
    Function.update (![5, 5] : Fin 2 → ℝ) 0 (-(![5, 5] : Fin 2 → ℝ) 0) = ![-5, 5] := by
  ext e
  fin_cases e <;> simp [Function.update_apply]

/-- The path voltage after flipping branch `0`. -/
lemma path_reversed_voltage :
    Function.update (![2, 1] : Fin 2 → ℝ) 0 (-(![2, 1] : Fin 2 → ℝ) 0) = ![-2, 1] := by
  ext e
  fin_cases e <;> simp [Function.update_apply]

/-- Reversing branch `0` of the path together with its current keeps the
injection `5`, `0`, `-5`, while branch `1` keeps current `5`. -/
example :
    electricalIncidence (V := Fin 3) (E := Fin 2)
        (Function.update ![0, 1] 0 1) (Function.update ![1, 2] 0 0) *ᵥ
      (![-5, 5] : Fin 2 → ℝ) = ![5, 0, -5] := by
  have h := mulVec_reversedBranch_eq (V := Fin 3) (E := Fin 2) ![0, 1] ![1, 2] ![5, 5] 0
  rw [path_kcl, path_reversed_current] at h
  exact h

/-- Reversing branch `0` of the path negates its potential-defined voltage
from `2` to `-2` and leaves branch `1` at `1`. -/
example :
    (electricalIncidence (V := Fin 3) (E := Fin 2)
        (Function.update ![0, 1] 0 1) (Function.update ![1, 2] 0 0)).transpose *ᵥ
      (![3, 1, 0] : Fin 3 → ℝ) = ![-2, 1] := by
  have h := transpose_mulVec_reversedBranch_eq (V := Fin 3) (E := Fin 2) ![0, 1] ![1, 2]
    ![3, 1, 0] 0
  rw [← path_kvl, path_reversed_voltage] at h
  exact h

/-- The combined statement on the path: branch power `15` equals node
power `15`, and reversing branch `0` keeps the injection and negates only
that branch's voltage. -/
example :
    ((∑ e : Fin 2, (![2, 1] : Fin 2 → ℝ) e * (![5, 5] : Fin 2 → ℝ) e) =
        ∑ n : Fin 3, (![3, 1, 0] : Fin 3 → ℝ) n * (![5, 0, -5] : Fin 3 → ℝ) n) ∧
      electricalIncidence (V := Fin 3) (E := Fin 2)
          (Function.update ![0, 1] 0 1) (Function.update ![1, 2] 0 0) *ᵥ
        (![-5, 5] : Fin 2 → ℝ) = ![5, 0, -5] ∧
      (electricalIncidence (V := Fin 3) (E := Fin 2)
          (Function.update ![0, 1] 0 1) (Function.update ![1, 2] 0 0)).transpose *ᵥ
        (![3, 1, 0] : Fin 3 → ℝ) = ![-2, 1] := by
  obtain ⟨hp, hj, hv⟩ := orientedBranchPorts_powerBalance_andReversal (V := Fin 3)
    (E := Fin 2) ![0, 1] ![1, 2] ![3, 1, 0] ![5, 0, -5] ![2, 1] ![5, 5] path_kcl path_kvl 0
  rw [path_reversed_current] at hj
  rw [path_reversed_voltage] at hv
  exact ⟨hp, hj, hv⟩

/-- A loop branch has a zero electrical incidence column. -/
example : electricalIncidence (V := Fin 2) (E := Fin 1) ![0] ![0] 1 0 = 0 :=
  electricalIncidence_loop_eq_zero (V := Fin 2) (E := Fin 1) ![0] ![0] 0 rfl 1

/-- Parallel branches with the same endpoints share a column while
keeping distinct branch identifiers. -/
example : electricalIncidence (V := Fin 2) (E := Fin 2) ![0, 0] ![1, 1] 0 0 =
    electricalIncidence (V := Fin 2) (E := Fin 2) ![0, 0] ![1, 1] 0 1 :=
  electricalIncidence_eq_of_same_endpoints (V := Fin 2) (E := Fin 2) ![0, 0] ![1, 1]
    0 1 rfl rfl 0

end PhyslibExtTest.Circuits.ArcPortSigns
