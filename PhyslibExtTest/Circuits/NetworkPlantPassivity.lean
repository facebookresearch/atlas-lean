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

private lemma capPlant_partition :
    IsBranchPartition 1 (∅ : Finset (Fin 1)) ∅ {0} ∅ := by
  unfold IsBranchPartition
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

/-- One-node, one-branch capacitor plant: the branch is a capacitor with
`C = 2`, and there are no resistor, inductor or source branches. -/
private def capPlant : NetworkPlant 1 1 where
  incidence := !![1]
  resistorSet := ∅
  inductorSet := ∅
  capacitorSet := {0}
  sourceSet := ∅
  resistance := ![0]
  inductance := ![0]
  capacitance := ![2]
  isBranchPartition := capPlant_partition

private lemma capPlant_R : ∀ e ∈ capPlant.resistorSet, 0 ≤ capPlant.resistance e := by
  intro e he; simp [capPlant] at he

private lemma capPlant_L : ∀ e ∈ capPlant.inductorSet, 0 < capPlant.inductance e := by
  intro e he; simp [capPlant] at he

private lemma capPlant_C : ∀ e ∈ capPlant.capacitorSet, 0 < capPlant.capacitance e := by
  intro e he; fin_cases e; norm_num [capPlant]

/-- The fixed capacitor plant is finite-horizon passive along all of its
admissible trajectories. -/
private lemma capPlant_passive : IsFiniteHorizonPassive capPlant :=
  networkPlant_isFiniteHorizonPassive capPlant capPlant_R capPlant_L capPlant_C

/-- Constant trajectory of the capacitor plant: branch voltage `4`, zero
branch current, node potential `4` and zero injection. Stored energy is
`2 * 4^2 / 2 = 16`, the supply rate and the loss rate are both `0`. -/
private def capTraj : NetworkTrajectory 1 1 where
  potential := fun _ => ![4]
  injection := fun _ => ![0]
  branchVoltage := fun _ => ![4]
  branchCurrent := fun _ => ![0]

private lemma capTraj_trajectory : IsNetworkTrajectory capPlant capTraj := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    ext i
    fin_cases i
    norm_num [capPlant, capTraj, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
      Matrix.transpose]
  · intro t
    ext i
    fin_cases i
    norm_num [capPlant, capTraj, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  · intro t e he
    simp [capPlant] at he
  · intro t e he
    have he0 : e = 0 := by
      have he' : e ∈ ({0} : Finset (Fin 1)) := he
      simpa using he'
    subst he0
    simp [capPlant, capTraj]
  · intro t e he
    simp [capPlant] at he
  · intro t e he
    have hconst : (fun s => capTraj.branchVoltage s e)
        = fun _ => (4 : ℝ) := by
      funext s
      fin_cases e
      rfl
    rw [hconst]
    exact differentiableAt_const _
  · intro t e he
    simp [capPlant] at he

/-- The constant trajectory obeys the network laws on `[0, 1]`. -/
private lemma capTraj_trajectoryOn : IsNetworkTrajectoryOn capPlant capTraj (Set.Icc 0 1) :=
  capTraj_trajectory.isNetworkTrajectoryOn (uniqueDiffOn_Icc zero_lt_one)

/-- Concrete stored energy: `2 * 4^2 / 2 = 16` at time `0`, through
the public storage read-off, and its nonnegativity through the
public lemma. -/
example : plantStorage capPlant capTraj 0 = 16 := by
  norm_num [capPlant, capTraj, plantStorage, storedEnergy, Finset.sum_singleton]

example : 0 ≤ plantStorage capPlant capTraj 0 :=
  plantStorage_nonneg capPlant
    (by intro e he; fin_cases e; norm_num [capPlant])
    (by intro e he; simp [capPlant] at he) capTraj 0

/-- Supply and loss rates of the concrete trajectory both vanish. -/
example : plantSupplyRate capPlant capTraj 0 = 0 := by
  norm_num [capPlant, capTraj, plantSupplyRate, sourceAbsorbedPower,
    dotProduct, Fin.sum_univ_one, Finset.sum_empty]

example : plantLossRate capPlant capTraj 0 = 0 := by
  norm_num [capPlant, capTraj, plantLossRate, resistiveLoss, Finset.sum_empty]

/-- Finite-horizon passivity on the concrete interval `[0, 1]`:
the storage increase is at most the integral of the supply rate,
through the public finite-horizon lemma. -/
example : FiniteHorizonPassiveOn capPlant capTraj 0 1 := by
  have hsupply : (fun s => plantSupplyRate capPlant capTraj s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, capTraj, plantSupplyRate, sourceAbsorbedPower,
      dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  have hbalance : (fun s => plantSupplyRate capPlant capTraj s -
      plantLossRate capPlant capTraj s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, capTraj, plantSupplyRate, plantLossRate, sourceAbsorbedPower,
      resistiveLoss, dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  apply plant_finiteHorizonPassive capPlant capTraj capTraj_trajectory
    capPlant_R capPlant_L capPlant_C 0 1 (by norm_num)
  · rw [hsupply]
    exact continuousOn_const
  · rw [hbalance]
    exact intervalIntegrable_const

/-- A trajectory of the same plant that obeys the network laws only up to
time `2`: after that its node potential jumps to `5` while the branch
voltage stays `4`, so the potential-voltage law fails. -/
private noncomputable def capTrajUntilTwo : NetworkTrajectory 1 1 where
  potential := fun t => if t ≤ 2 then ![4] else ![5]
  injection := fun _ => ![0]
  branchVoltage := fun _ => ![4]
  branchCurrent := fun _ => ![0]

/-- The trajectory is not a network trajectory at every time. -/
example : ¬ IsNetworkTrajectory capPlant capTrajUntilTwo := by
  intro h
  have h3 := congrFun (h.1 3) 0
  norm_num [capPlant, capTrajUntilTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    Matrix.transpose] at h3

/-- On `[0, 1]` it obeys the network laws, since it agrees there with the
constant trajectory. -/
private lemma capTrajUntilTwo_trajectoryOn :
    IsNetworkTrajectoryOn capPlant capTrajUntilTwo (Set.Icc 0 1) :=
  capTraj_trajectoryOn.congr
    (fun t ht => by
      have ht2 : t ≤ 2 := ht.2.trans (by norm_num)
      simp [capTrajUntilTwo, capTraj, ht2])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Finite-horizon passivity on `[0, 1]` for a trajectory with no global
extension, through the interval-scoped public lemma. -/
example : FiniteHorizonPassiveOn capPlant capTrajUntilTwo 0 1 := by
  have hsupply : (fun s => plantSupplyRate capPlant capTrajUntilTwo s) =
      fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, capTrajUntilTwo, plantSupplyRate, sourceAbsorbedPower,
      dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  have hbalance : (fun s => plantSupplyRate capPlant capTrajUntilTwo s -
      plantLossRate capPlant capTrajUntilTwo s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, capTrajUntilTwo, plantSupplyRate, plantLossRate,
      sourceAbsorbedPower, resistiveLoss, dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  apply plant_finiteHorizonPassive_of_trajectoryOn capPlant capPlant_R capPlant_L
    capPlant_C capTrajUntilTwo 0 1 (by norm_num) capTrajUntilTwo_trajectoryOn
  · rw [hsupply]
    exact continuousOn_const
  · rw [hbalance]
    exact intervalIntegrable_const

/-- Undamped constancy reaches intermediate times: storage at `1/2` equals
storage at `0` for the trajectory that obeys the network laws only on
`[0, 1]`, through the interval-scoped public lemma. -/
example : plantStorage capPlant capTrajUntilTwo (1 / 2) =
    plantStorage capPlant capTrajUntilTwo 0 := by
  have hsupply : ∀ s ∈ Set.Icc (0 : ℝ) 1, plantSupplyRate capPlant capTrajUntilTwo s = 0 := by
    intro s _
    norm_num [capPlant, capTrajUntilTwo, plantSupplyRate, sourceAbsorbedPower,
      dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  have hloss : ∀ s ∈ Set.Icc (0 : ℝ) 1, plantLossRate capPlant capTrajUntilTwo s = 0 := by
    intro s _
    norm_num [capPlant, capTrajUntilTwo, plantLossRate, resistiveLoss, Finset.sum_empty]
  have hbalance : (fun s => plantSupplyRate capPlant capTrajUntilTwo s -
      plantLossRate capPlant capTrajUntilTwo s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, capTrajUntilTwo, plantSupplyRate, plantLossRate,
      sourceAbsorbedPower, resistiveLoss, dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  refine plantStorage_constant_of_zero_supply_loss_of_trajectoryOn capPlant capPlant_R
    capPlant_L capPlant_C capTrajUntilTwo 0 1 (by norm_num) capTrajUntilTwo_trajectoryOn
    hsupply hloss ?_ (1 / 2) (by norm_num)
  rw [hbalance]
  exact intervalIntegrable_const

/-- The global-trajectory form gives the same intermediate-time constancy
for the constant trajectory on `[0, 1]`. -/
example : plantStorage capPlant capTraj (1 / 2) = plantStorage capPlant capTraj 0 := by
  have hbalance : (fun s => plantSupplyRate capPlant capTraj s -
      plantLossRate capPlant capTraj s) = fun _ => (0 : ℝ) := by
    funext s
    norm_num [capPlant, capTraj, plantSupplyRate, plantLossRate, sourceAbsorbedPower,
      resistiveLoss, dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  refine plantStorage_constant_of_zero_supply_loss capPlant capTraj capTraj_trajectory
    capPlant_R capPlant_L capPlant_C 0 1 (by norm_num) ?_ ?_ ?_ (1 / 2) (by norm_num)
  · intro s _
    norm_num [capPlant, capTraj, plantSupplyRate, sourceAbsorbedPower,
      dotProduct, Fin.sum_univ_one, Finset.sum_empty]
  · intro s _
    norm_num [capPlant, capTraj, plantLossRate, resistiveLoss, Finset.sum_empty]
  · rw [hbalance]
    exact intervalIntegrable_const

/-- A trajectory of the same plant whose branch voltage and node potential
are `4` on `[0, ∞)` and `4 - t` before time `0`. It agrees with the constant
trajectory on `[0, 1]` but has a kink at the left endpoint `0`. -/
private noncomputable def kinkTraj : NetworkTrajectory 1 1 where
  potential := fun t => ![if 0 ≤ t then 4 else 4 - t]
  injection := fun _ => ![0]
  branchVoltage := fun t => ![if 0 ≤ t then 4 else 4 - t]
  branchCurrent := fun _ => ![0]

/-- The kinked capacitor voltage has no two-sided derivative at the left
endpoint `0`: its right derivative is `0` and its left derivative is `-1`. -/
private lemma kinkTraj_not_differentiableAt :
    ¬ DifferentiableAt ℝ (fun s => kinkTraj.branchVoltage s 0) 0 := by
  have hfun : (fun s => kinkTraj.branchVoltage s 0) =
      fun s : ℝ => if 0 ≤ s then (4 : ℝ) else 4 - s := by
    funext s
    rfl
  rw [hfun]
  intro h
  have hd := h.hasDerivAt
  have hright : HasDerivWithinAt (fun s : ℝ => if 0 ≤ s then (4 : ℝ) else 4 - s) 0
      (Set.Ici 0) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Set.Ici 0) (4 : ℝ)).congr
      (fun s hs => by simp [Set.mem_Ici.mp hs]) (by simp)
  have hleft : HasDerivWithinAt (fun s : ℝ => if 0 ≤ s then (4 : ℝ) else 4 - s) (-1)
      (Set.Iic 0) 0 := by
    have hsub : HasDerivWithinAt (fun s : ℝ => 4 - s) (-1) (Set.Iic 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_sub (4 : ℝ)).hasDerivWithinAt
    refine hsub.congr (fun s hs => ?_) (by norm_num)
    have hs0 : s ≤ 0 := Set.mem_Iic.mp hs
    split_ifs with h0
    · have : s = 0 := le_antisymm hs0 h0
      subst this
      norm_num
    · rfl
  have e1 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd.hasDerivWithinAt hright
  have e2 := (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _ hd.hasDerivWithinAt hleft
  linarith

/-- Because of the kink the trajectory is not a network trajectory at every
time, and an ambient-derivative condition at the endpoint `0 ∈ [0, 1]` would
reject it. -/
example : ¬ IsNetworkTrajectory capPlant kinkTraj := by
  intro h
  exact kinkTraj_not_differentiableAt (h.2.2.2.2.2.1 0 0 (by simp [capPlant]))

/-- The interval relation only reads `[0, 1]`, where the kinked trajectory
agrees with the constant one, so it obeys the network laws there. -/
private lemma kinkTraj_trajectoryOn :
    IsNetworkTrajectoryOn capPlant kinkTraj (Set.Icc 0 1) :=
  capTraj_trajectoryOn.congr
    (fun t ht => by simp [kinkTraj, capTraj, ht.1])
    (fun _ _ => rfl)
    (fun t ht => by simp [kinkTraj, capTraj, ht.1])
    (fun _ _ => rfl)

/-- Plant-level passivity holds the plant fixed and applies to each of its
trajectories: the constant and the kinked trajectory are both passive on
`[0, 1]`. -/
example : FiniteHorizonPassiveOn capPlant capTraj 0 1 ∧
    FiniteHorizonPassiveOn capPlant kinkTraj 0 1 := by
  have hzero : ∀ x : NetworkTrajectory 1 1, x.injection = (fun _ => ![0]) →
      (fun s => plantSupplyRate capPlant x s) = (fun _ => (0 : ℝ)) ∧
      (fun s => plantSupplyRate capPlant x s - plantLossRate capPlant x s) =
        (fun _ => (0 : ℝ)) := by
    intro x hx
    constructor
    · funext s
      simp [plantSupplyRate, sourceAbsorbedPower, capPlant, hx, dotProduct]
    · funext s
      simp [plantSupplyRate, plantLossRate, sourceAbsorbedPower, resistiveLoss, capPlant,
        hx, dotProduct]
  have hpass : ∀ x : NetworkTrajectory 1 1, x.injection = (fun _ => ![0]) →
      IsNetworkTrajectoryOn capPlant x (Set.Icc 0 1) →
      FiniteHorizonPassiveOn capPlant x 0 1 := by
    intro x hx hP
    obtain ⟨hs, hb⟩ := hzero x hx
    refine capPlant_passive x 0 1 (by norm_num) hP ?_ ?_
    · rw [hs]
      exact continuousOn_const
    · rw [hb]
      exact intervalIntegrable_const
  exact ⟨hpass capTraj rfl capTraj_trajectoryOn, hpass kinkTraj rfl kinkTraj_trajectoryOn⟩

/-- Malformed branch data is not a plant: one branch in no class misses the
covering half of the partition, so no plant with these classes exists and
none can be certified passive. -/
example : ¬ ∃ P : NetworkPlant 0 1, P.resistorSet = ∅ ∧ P.inductorSet = ∅ ∧
    P.capacitorSet = ∅ ∧ P.sourceSet = ∅ := by
  rintro ⟨P, hR, hL, hC, hS⟩
  have hu := P.isBranchPartition.2.2.2.2.2.2
  rw [hR, hL, hC, hS] at hu
  exact absurd hu (by decide)

/-- Malformed branch data is not a plant: one branch in two classes misses
the disjointness half of the partition. -/
example : ¬ ∃ P : NetworkPlant 0 1, 0 ∈ P.resistorSet ∧ 0 ∈ P.capacitorSet := by
  rintro ⟨P, hR, hC⟩
  exact Finset.disjoint_left.mp P.isBranchPartition.2.1 hR hC

/-- Zero-length interval at time `2`: zero storage increase is at
most zero supplied energy, through the public zero-length lemma. -/
example : plantStorage capPlant capTraj 2 - plantStorage capPlant capTraj 2
    ≤ ∫ s in (2 : ℝ)..2, plantSupplyRate capPlant capTraj s :=
  finiteHorizonPassive_zeroLength capPlant capTraj 2

end PhyslibExtTest.Circuits.NetworkPlantPassivity
