/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.NetworkPlantPassivity
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.NetworkPlantPassivity
open PhyslibExt.Circuits.NetworkStorageBalance

namespace PhyslibExtTest.Circuits.NetworkPlantPassivity

/-- One-node, one-branch capacitor plant at constant values: the
branch is a capacitor with `C = 2`, constant branch voltage `4`
and zero branch current, the node potential is `4` and the
independent injection is `0`. Stored energy is `2 * 4^2 / 2 = 16`,
the supply rate and the loss rate are both `0`. -/
private def capPlant : NetworkPlant 1 1 where
  incidence := !![1]
  resistorSet := ∅
  inductorSet := ∅
  capacitorSet := {0}
  sourceSet := ∅
  resistance := ![0]
  inductance := ![0]
  capacitance := ![2]
  potential := fun _ => ![4]
  injection := fun _ => ![0]
  branchVoltage := fun _ => ![4]
  branchCurrent := fun _ => ![0]

private lemma capPlant_partition :
    IsBranchPartition 1 (∅ : Finset (Fin 1)) ∅ {0} ∅ := by
  unfold IsBranchPartition
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

private lemma capPlant_trajectory : IsNetworkTrajectory capPlant := by
  refine ⟨capPlant_partition, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    ext i
    fin_cases i
    norm_num [capPlant, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Matrix.transpose]
  · intro t
    ext i
    fin_cases i
    norm_num [capPlant, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  · intro t e he
    simp [capPlant] at he
  · intro t e he
    have he0 : e = 0 := by
      have he' : e ∈ ({0} : Finset (Fin 1)) := he
      simpa using he'
    subst he0
    simp [capPlant]
  · intro t e he
    simp [capPlant] at he
  · intro t e he
    have hconst : (fun s => capPlant.branchVoltage s e)
        = fun _ => (4 : ℝ) := by
      funext s
      fin_cases e
      rfl
    rw [hconst]
    exact differentiableAt_const _
  · intro t e he
    simp [capPlant] at he

/-- Concrete stored energy: `2 * 4^2 / 2 = 16` at time `0`, through
the public storage read-off, and its nonnegativity through the
public lemma. -/
example : plantStorage capPlant 0 = 16 := by
  norm_num [capPlant, plantStorage, storedEnergy, Finset.sum_singleton]

example : 0 ≤ plantStorage capPlant 0 :=
  plantStorage_nonneg capPlant
    (by intro e he; fin_cases e; norm_num [capPlant])
    (by intro e he; simp [capPlant] at he) 0

/-- Supply and loss rates of the concrete plant both vanish. -/
example : plantSupplyRate capPlant 0 = 0 := by
  norm_num [capPlant, plantSupplyRate, sourceAbsorbedPower,
    dotProduct, Fin.sum_univ_one, Finset.sum_empty]

example : plantLossRate capPlant 0 = 0 := by
  norm_num [capPlant, plantLossRate, resistiveLoss, Finset.sum_empty]

/-- Finite-horizon passivity on the concrete interval `[0, 1]`:
the storage increase is at most the integral of the supply rate,
through the public finite-horizon lemma. -/
example : FiniteHorizonPassiveOn capPlant 0 1 := by
  have hsupply : (fun s => plantSupplyRate capPlant s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, plantSupplyRate, sourceAbsorbedPower,
      dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  have hbalance : (fun s => plantSupplyRate capPlant s - plantLossRate capPlant s)
      = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, plantSupplyRate, plantLossRate, sourceAbsorbedPower,
      resistiveLoss, dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  apply plant_finiteHorizonPassive capPlant capPlant_trajectory
    (by intro e he; simp [capPlant] at he)
    (by intro e he; simp [capPlant] at he)
    (by intro e he; fin_cases e; norm_num [capPlant]) 0 1 (by norm_num)
  · rw [hsupply]
    exact continuousOn_const
  · rw [hbalance]
    exact intervalIntegrable_const

/-- A capacitor plant that obeys the network laws only up to time `2`:
after that its node potential jumps to `5` while the branch voltage stays
`4`, so the potential-voltage law fails. -/
private noncomputable def capPlantUntilTwo : NetworkPlant 1 1 where
  incidence := !![1]
  resistorSet := ∅
  inductorSet := ∅
  capacitorSet := {0}
  sourceSet := ∅
  resistance := ![0]
  inductance := ![0]
  capacitance := ![2]
  potential := fun t => if t ≤ 2 then ![4] else ![5]
  injection := fun _ => ![0]
  branchVoltage := fun _ => ![4]
  branchCurrent := fun _ => ![0]

/-- The plant is not a network trajectory at every time. -/
example : ¬ IsNetworkTrajectory capPlantUntilTwo := by
  intro h
  have h3 := congrFun (h.2.1 3) 0
  norm_num [capPlantUntilTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    Matrix.transpose] at h3

/-- On `[0, 1]` it obeys the network laws. -/
private lemma capPlantUntilTwo_trajectoryOn :
    IsNetworkTrajectoryOn capPlantUntilTwo (Set.Icc 0 1) := by
  refine ⟨capPlant_partition, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht2 : t ≤ 2 := ht.2.trans (by norm_num)
    ext i
    fin_cases i
    norm_num [capPlantUntilTwo, ht2, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Matrix.transpose]
  · intro t _
    ext i
    fin_cases i
    norm_num [capPlantUntilTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  · intro t _ e he
    simp [capPlantUntilTwo] at he
  · intro t _ e he
    have he0 : e = 0 := by
      have he' : e ∈ ({0} : Finset (Fin 1)) := he
      simpa using he'
    subst he0
    simp [capPlantUntilTwo]
  · intro t _ e he
    simp [capPlantUntilTwo] at he
  · intro t _ e he
    have hconst : (fun s => capPlantUntilTwo.branchVoltage s e)
        = fun _ => (4 : ℝ) := by
      funext s
      fin_cases e
      rfl
    rw [hconst]
    exact differentiableAt_const _
  · intro t _ e he
    simp [capPlantUntilTwo] at he

/-- Finite-horizon passivity on `[0, 1]` for a plant with no global
trajectory, through the interval-scoped public lemma. -/
example : FiniteHorizonPassiveOn capPlantUntilTwo 0 1 := by
  have hsupply : (fun s => plantSupplyRate capPlantUntilTwo s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlantUntilTwo, plantSupplyRate, sourceAbsorbedPower,
      dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  have hbalance : (fun s => plantSupplyRate capPlantUntilTwo s -
      plantLossRate capPlantUntilTwo s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlantUntilTwo, plantSupplyRate, plantLossRate, sourceAbsorbedPower,
      resistiveLoss, dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  apply plant_finiteHorizonPassive_of_trajectoryOn capPlantUntilTwo
    (by intro e he; simp [capPlantUntilTwo] at he)
    (by intro e he; simp [capPlantUntilTwo] at he)
    (by intro e he; fin_cases e; norm_num [capPlantUntilTwo]) 0 1 (by norm_num)
    capPlantUntilTwo_trajectoryOn
  · rw [hsupply]
    exact continuousOn_const
  · rw [hbalance]
    exact intervalIntegrable_const

/-- Zero-length interval at time `2`: zero storage increase is at
most zero supplied energy, through the public zero-length lemma. -/
example : plantStorage capPlant 2 - plantStorage capPlant 2
    ≤ ∫ s in (2 : ℝ)..2, plantSupplyRate capPlant s :=
  finiteHorizonPassive_zeroLength capPlant 2

end PhyslibExtTest.Circuits.NetworkPlantPassivity
