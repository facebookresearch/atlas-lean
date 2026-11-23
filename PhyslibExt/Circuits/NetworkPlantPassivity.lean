/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.NetworkStorageBalance
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Network plant passivity

## i. Overview

A finite lumped network has its branches partitioned exactly once
into resistor, inductor, capacitor and source classes, as carried
by `PhyslibExt.Circuits.NetworkStorageBalance`. This module reads
that network off as a plant. A `NetworkPlant` holds only the static
data: the incidence matrix, the branch partition and the element
values, together with the proof that the four branch classes are an
exact partition of the branches, so malformed branch data is not a
plant and cannot be certified passive. A `NetworkTrajectory` is a separate signal tuple of node
potentials, independent node injections, branch voltages and branch
currents, and `IsNetworkTrajectoryOn P x S` is the relation saying
that the trajectory `x` obeys the network laws of the plant `P` at
every time of `S`. Storage, supply rate and loss rate of a trajectory
are read directly from the canonical network storage, source absorbed
power and resistive loss, so no second storage or power definition is
introduced here.

The `NetworkPlant` read-off interface is owned by this leaf: no
canonical plant interface exists in the library at the time of
writing, so `NetworkPlant`, `NetworkTrajectory`, `plantStorage`,
`plantSupplyRate`, `plantLossRate`, `FiniteHorizonPassiveOn` and
`IsFiniteHorizonPassive` are defined here and read the merged network
carrier directly. On a trajectory obeying the network laws, the
storage derivative is supply minus resistive loss, and over a finite
interval the increase of storage is at most the integral of the
supply rate. `IsFiniteHorizonPassive P` holds a plant fixed and
quantifies over all of its admissible trajectories and intervals;
`networkPlant_isFiniteHorizonPassive` proves it for nonnegative
resistances and positive reactive values.

The interval relation is local to the interval: the capacitor and
inductor laws use derivatives within `S` and differentiability within
`S`, so it depends only on the signal values at times of `S`
(`IsNetworkTrajectoryOn.congr`). At an endpoint of `[a, b]` these are
one-sided derivatives. The global `IsNetworkTrajectory` uses ambient
derivatives at every time and implies the interval relation on every
set with unique derivatives, such as `[a, b]` with `a < b`. No
trajectory existence is asserted, no asymptotic stability is claimed,
and no wider control framework is introduced.

## ii. Key results

- `plantOfNetwork_storage_eq`, `plantOfNetwork_supplyAndLoss_eq`
  and `trajectoryOfSignals_eq`: the identity representation of raw
  network data and signals as a plant and a trajectory preserves
  storage, supply and loss rates, and the signals themselves.
- `IsNetworkTrajectoryOn.congr`: the interval relation depends only
  on the signals at times of the interval.
- `plantStorage_nonneg`: plant storage is nonnegative for
  nonnegative capacitance and inductance.
- `plantStorage_deriv_eq_supply_sub_loss`: on a network
  trajectory, the derivative of plant storage is the supply rate
  minus the resistive loss rate.
- `plant_finiteHorizonPassive_of_trajectoryOn`: the finite-horizon
  passivity bound when the network laws hold only on `[a, b]`;
  `plant_finiteHorizonPassive` is its global-trajectory corollary.
- `networkPlant_isFiniteHorizonPassive` and `networkPlant_passivity`:
  every admissible trajectory of a fixed plant is finite-horizon
  passive, the latter packaged with storage nonnegativity and the
  storage balance for every trajectory.
- `plantStorage_constant_of_zero_supply_loss` (with its
  interval-scoped form
  `plantStorage_constant_of_zero_supply_loss_of_trajectoryOn`),
  `finiteHorizonPassive_zeroLength` and
  `partition_no_branch_counted_twice`: validation cases covering
  constant undamped storage, a zero-length interval, and exact
  branch accounting with no source branch of a plant counted twice.

## iii. Table of contents

- A. The plant read-off interface
- B. Representation preservation
- C. Storage balance and finite-horizon passivity
- D. Validation cases

## iv. References

- J. C. Willems, *Dissipative dynamical systems part I: General
  theory*, Archive for Rational Mechanics and Analysis 45 (1972),
  321-351: dissipativity, storage functions and supply rates.
- A. van der Schaft, *L2-Gain and Passivity Techniques in
  Nonlinear Control*, third edition, Springer, 2017: passivity,
  storage functions and the finite-horizon supplied-energy bound.

## A. The plant read-off interface
## B. Representation preservation
## C. Storage balance and finite-horizon passivity
## D. Validation cases
-/

@[expose] public section

open Matrix

namespace PhyslibExt.Circuits.NetworkPlantPassivity

open PhyslibExt.Circuits.NetworkStorageBalance


/-! ### A. The plant read-off interface -/

/-- Static plant data for one lumped network: incidence, branch partition
and element values, with the invariant that the resistor, inductor,
capacitor and source classes partition the branches exactly. It carries no
signals; trajectories are separate. New definition owned by this leaf. -/
structure NetworkPlant (nN nB : ℕ) where
  incidence : Matrix (Fin nN) (Fin nB) ℝ
  resistorSet : Finset (Fin nB)
  inductorSet : Finset (Fin nB)
  capacitorSet : Finset (Fin nB)
  sourceSet : Finset (Fin nB)
  resistance : Fin nB → ℝ
  inductance : Fin nB → ℝ
  capacitance : Fin nB → ℝ
  isBranchPartition : IsBranchPartition nB resistorSet inductorSet capacitorSet sourceSet

/-- A candidate signal tuple for a network with `nN` nodes and `nB`
branches: node potentials, independent node injections, branch voltages
and branch currents as functions of time. New definition owned by this
leaf. -/
structure NetworkTrajectory (nN nB : ℕ) where
  potential : ℝ → Fin nN → ℝ
  injection : ℝ → Fin nN → ℝ
  branchVoltage : ℝ → Fin nB → ℝ
  branchCurrent : ℝ → Fin nB → ℝ

/-- Storage of a plant along a trajectory at a time, read directly from
the network storage. -/
noncomputable def plantStorage {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (t : ℝ) : ℝ :=
  storedEnergy nB P.capacitorSet P.inductorSet P.capacitance P.inductance
    (x.branchVoltage t) (x.branchCurrent t)

/-- Supply rate of a plant along a trajectory: node supplied power minus
source absorbed power. -/
def plantSupplyRate {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (t : ℝ) : ℝ :=
  (x.potential t) ⬝ᵥ (x.injection t) -
    sourceAbsorbedPower nB P.sourceSet (x.branchVoltage t) (x.branchCurrent t)

/-- Resistive loss rate of a plant along a trajectory. -/
def plantLossRate {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (t : ℝ) : ℝ :=
  resistiveLoss nB P.resistorSet P.resistance (x.branchCurrent t)

/-- The trajectory obeys the network laws of the plant at every time:
potential voltage, node current balance for the independent injection, and
the resistor, capacitor and inductor laws with differentiability of the
storage coordinates at every time. -/
def IsNetworkTrajectory {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) : Prop :=
  (∀ t : ℝ, x.branchVoltage t = P.incidence.transpose *ᵥ x.potential t) ∧
    (∀ t : ℝ, P.incidence *ᵥ x.branchCurrent t = x.injection t) ∧
    (∀ t : ℝ, ∀ e ∈ P.resistorSet, x.branchVoltage t e =
      P.resistance e * x.branchCurrent t e) ∧
    (∀ t : ℝ, ∀ e ∈ P.capacitorSet, x.branchCurrent t e =
      P.capacitance e * deriv (fun s => x.branchVoltage s e) t) ∧
    (∀ t : ℝ, ∀ e ∈ P.inductorSet, x.branchVoltage t e =
      P.inductance e * deriv (fun s => x.branchCurrent s e) t) ∧
    (∀ t : ℝ, ∀ e ∈ P.capacitorSet,
      DifferentiableAt ℝ (fun s => x.branchVoltage s e) t) ∧
    (∀ t : ℝ, ∀ e ∈ P.inductorSet,
      DifferentiableAt ℝ (fun s => x.branchCurrent s e) t)

/-- The trajectory obeys the network laws of the plant at every time in
`S`: potential voltage, node current balance for the independent
injection, and the resistor, capacitor and inductor laws.
The capacitor and inductor laws use derivatives within `S` and
differentiability within `S`, so the relation depends only on the signal
values at times of `S`; at an endpoint of an interval they are one-sided. -/
def IsNetworkTrajectoryOn {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (S : Set ℝ) : Prop :=
  (∀ t ∈ S, x.branchVoltage t = P.incidence.transpose *ᵥ x.potential t) ∧
    (∀ t ∈ S, P.incidence *ᵥ x.branchCurrent t = x.injection t) ∧
    (∀ t ∈ S, ∀ e ∈ P.resistorSet, x.branchVoltage t e =
      P.resistance e * x.branchCurrent t e) ∧
    (∀ t ∈ S, ∀ e ∈ P.capacitorSet, x.branchCurrent t e =
      P.capacitance e * derivWithin (fun s => x.branchVoltage s e) S t) ∧
    (∀ t ∈ S, ∀ e ∈ P.inductorSet, x.branchVoltage t e =
      P.inductance e * derivWithin (fun s => x.branchCurrent s e) S t) ∧
    (∀ t ∈ S, ∀ e ∈ P.capacitorSet,
      DifferentiableWithinAt ℝ (fun s => x.branchVoltage s e) S t) ∧
    (∀ t ∈ S, ∀ e ∈ P.inductorSet,
      DifferentiableWithinAt ℝ (fun s => x.branchCurrent s e) S t)

/-- A network trajectory obeys the network laws on every set of times on
which derivatives are unique, such as `[a, b]` with `a < b`. -/
lemma IsNetworkTrajectory.isNetworkTrajectoryOn {nN nB : ℕ} {P : NetworkPlant nN nB}
    {x : NetworkTrajectory nN nB} (hP : IsNetworkTrajectory P x) {S : Set ℝ}
    (hS : UniqueDiffOn ℝ S) : IsNetworkTrajectoryOn P x S := by
  obtain ⟨hV, hbal, hRlaw, hClaw, hLlaw, hCdiff, hLdiff⟩ := hP
  refine ⟨fun t _ => hV t, fun t _ => hbal t, fun t _ => hRlaw t, ?_, ?_,
    fun t _ e he => (hCdiff t e he).differentiableWithinAt,
    fun t _ e he => (hLdiff t e he).differentiableWithinAt⟩
  · intro t ht e he
    rw [(hCdiff t e he).derivWithin (hS t ht)]
    exact hClaw t e he
  · intro t ht e he
    rw [(hLdiff t e he).derivWithin (hS t ht)]
    exact hLlaw t e he

/-- Locality of the interval relation: a trajectory that agrees with a
network trajectory on `S` at every time of `S` obeys the network laws on
`S` as well. -/
lemma IsNetworkTrajectoryOn.congr {nN nB : ℕ} {P : NetworkPlant nN nB}
    {x y : NetworkTrajectory nN nB} {S : Set ℝ} (hP : IsNetworkTrajectoryOn P x S)
    (hphi : Set.EqOn y.potential x.potential S) (hj : Set.EqOn y.injection x.injection S)
    (hv : Set.EqOn y.branchVoltage x.branchVoltage S)
    (hi : Set.EqOn y.branchCurrent x.branchCurrent S) :
    IsNetworkTrajectoryOn P y S := by
  obtain ⟨hV, hbal, hRlaw, hClaw, hLlaw, hCdiff, hLdiff⟩ := hP
  have hve : ∀ e, Set.EqOn (fun s => y.branchVoltage s e) (fun s => x.branchVoltage s e) S :=
    fun e _ ht => congrFun (hv ht) e
  have hie : ∀ e, Set.EqOn (fun s => y.branchCurrent s e) (fun s => x.branchCurrent s e) S :=
    fun e _ ht => congrFun (hi ht) e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hv ht, hphi ht]
    exact hV t ht
  · intro t ht
    rw [hi ht, hj ht]
    exact hbal t ht
  · intro t ht e he
    rw [hv ht, hi ht]
    exact hRlaw t ht e he
  · intro t ht e he
    rw [hi ht, derivWithin_congr (hve e) (hve e ht)]
    exact hClaw t ht e he
  · intro t ht e he
    rw [hv ht, derivWithin_congr (hie e) (hie e ht)]
    exact hLlaw t ht e he
  · intro t ht e he
    exact (hCdiff t ht e he).congr (hve e) (hve e ht)
  · intro t ht e he
    exact (hLdiff t ht e he).congr (hie e) (hie e ht)

/-- Finite-horizon passivity of one trajectory of a plant on an interval:
the increase of storage is at most the integral of the supply rate. -/
def FiniteHorizonPassiveOn {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (a b : ℝ) : Prop :=
  plantStorage P x b - plantStorage P x a ≤ ∫ s in a..b, plantSupplyRate P x s

/-- Finite-horizon passivity of a fixed plant: every trajectory that obeys
the network laws of the plant on an interval `[a, b]`, with continuous
supply rate and integrable balance rate there, is finite-horizon passive
on that interval. -/
def IsFiniteHorizonPassive {nN nB : ℕ} (P : NetworkPlant nN nB) : Prop :=
  ∀ (x : NetworkTrajectory nN nB) (a b : ℝ), a ≤ b →
    IsNetworkTrajectoryOn P x (Set.Icc a b) →
    ContinuousOn (fun s => plantSupplyRate P x s) (Set.Icc a b) →
    IntervalIntegrable (fun s => plantSupplyRate P x s - plantLossRate P x s)
      MeasureTheory.volume a b →
    FiniteHorizonPassiveOn P x a b

/-- The identity representation of raw network data, with its branch
partition, as a plant. -/
def plantOfNetwork (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset) (Rval Lval Cval : Fin nB → ℝ) :
    NetworkPlant nN nB where
  incidence := B
  resistorSet := Rset
  inductorSet := Lset
  capacitorSet := Cset
  sourceSet := Sset
  resistance := Rval
  inductance := Lval
  capacitance := Cval
  isBranchPartition := hpart

/-- The identity representation of raw network signals as a trajectory. -/
def trajectoryOfSignals {nN nB : ℕ} (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) :
    NetworkTrajectory nN nB where
  potential := phi
  injection := j
  branchVoltage := v
  branchCurrent := iB

/-! ### B. Representation preservation -/

/-- Representation preserves storage: the plant built from network data,
along the trajectory built from network signals, has exactly the network
stored energy at every time. -/
lemma plantOfNetwork_storage_eq (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset) (Rval Lval Cval : Fin nB → ℝ)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) (t : ℝ) :
    plantStorage (plantOfNetwork nN nB B Rset Lset Cset Sset hpart Rval Lval Cval)
        (trajectoryOfSignals phi j v iB) t =
      storedEnergy nB Cset Lset Cval Lval (v t) (iB t) := by
  rfl

/-- Representation preserves supply and loss: the plant supply and loss
rates are exactly the network supplied-minus-source power and resistive
loss. -/
lemma plantOfNetwork_supplyAndLoss_eq (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset) (Rval Lval Cval : Fin nB → ℝ)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) (t : ℝ) :
    plantSupplyRate (plantOfNetwork nN nB B Rset Lset Cset Sset hpart Rval Lval Cval)
        (trajectoryOfSignals phi j v iB) t =
        (phi t) ⬝ᵥ (j t) - sourceAbsorbedPower nB Sset (v t) (iB t) ∧
      plantLossRate (plantOfNetwork nN nB B Rset Lset Cset Sset hpart Rval Lval Cval)
        (trajectoryOfSignals phi j v iB) t =
        resistiveLoss nB Rset Rval (iB t) := by
  exact ⟨rfl, rfl⟩

/-- Representation preserves signals: the trajectory built from network
signals has the same potentials, injections, branch voltages and branch
currents as the signals. -/
lemma trajectoryOfSignals_eq {nN nB : ℕ} (phi j : ℝ → Fin nN → ℝ)
    (v iB : ℝ → Fin nB → ℝ) :
    (trajectoryOfSignals phi j v iB).potential = phi ∧
      (trajectoryOfSignals phi j v iB).injection = j ∧
      (trajectoryOfSignals phi j v iB).branchVoltage = v ∧
      (trajectoryOfSignals phi j v iB).branchCurrent = iB := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### C. Storage balance and finite-horizon passivity -/

/-- Storage is nonnegative for nonnegative capacitance and inductance. -/
lemma plantStorage_nonneg {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hC : ∀ e ∈ P.capacitorSet, 0 ≤ P.capacitance e)
    (hL : ∀ e ∈ P.inductorSet, 0 ≤ P.inductance e)
    (x : NetworkTrajectory nN nB) (t : ℝ) :
    0 ≤ plantStorage P x t :=
  storedEnergy_nonneg nB P.capacitorSet P.inductorSet P.capacitance
    P.inductance (x.branchVoltage t) (x.branchCurrent t) hC hL

/-- The resistive loss rate is nonnegative for nonnegative resistances. -/
lemma plantLossRate_nonneg {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (x : NetworkTrajectory nN nB) (t : ℝ) :
    0 ≤ plantLossRate P x t :=
  Finset.sum_nonneg fun e he => mul_nonneg (hR e he) (sq_nonneg _)

/-- Storage balance: on a network trajectory with nonnegative resistances
and positive reactive values, the derivative of storage is the supply rate
minus the resistive loss rate. -/
lemma plantStorage_deriv_eq_supply_sub_loss {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (hP : IsNetworkTrajectory P x)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (t : ℝ) :
    deriv (fun s => plantStorage P x s) t =
      plantSupplyRate P x t - plantLossRate P x t := by
  obtain ⟨hV, hbal, hRlaw, hClaw, hLlaw, hCdiff, hLdiff⟩ := hP
  exact network_storage_deriv_eq_supplied_minus_losses nN nB P.incidence
    P.resistorSet P.inductorSet P.capacitorSet P.sourceSet P.isBranchPartition
    P.resistance P.inductance P.capacitance hR hL hC
    x.potential x.injection x.branchVoltage x.branchCurrent t
    (hV t) (hbal t) (hRlaw t) (hClaw t) (hLlaw t) (hCdiff t) (hLdiff t)

/-- On a set where the trajectory obeys the network laws, storage is
continuous within that set. -/
lemma IsNetworkTrajectoryOn.continuousOn_plantStorage {nN nB : ℕ}
    {P : NetworkPlant nN nB} {x : NetworkTrajectory nN nB} {S : Set ℝ}
    (hP : IsNetworkTrajectoryOn P x S) :
    ContinuousOn (fun s => plantStorage P x s) S := by
  obtain ⟨-, -, -, -, -, hCdiff, hLdiff⟩ := hP
  unfold plantStorage storedEnergy
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum _ fun e he => ?_
    have hv : ContinuousOn (fun s => x.branchVoltage s e) S :=
      fun t ht => (hCdiff t ht e he).continuousWithinAt
    exact (continuousOn_const.mul (hv.pow 2)).div_const 2
  · refine continuousOn_finsetSum _ fun e he => ?_
    have hi : ContinuousOn (fun s => x.branchCurrent s e) S :=
      fun t ht => (hLdiff t ht e he).continuousWithinAt
    exact (continuousOn_const.mul (hi.pow 2)).div_const 2

/-- Storage balance at interior times: if the network laws hold on
`[a, b]`, then at every time of `(a, b)` storage has derivative supply
minus resistive loss, read off the canonical storage balance. -/
lemma IsNetworkTrajectoryOn.hasDerivAt_plantStorage {nN nB : ℕ}
    {P : NetworkPlant nN nB} {x : NetworkTrajectory nN nB} {a b : ℝ}
    (hP : IsNetworkTrajectoryOn P x (Set.Icc a b))
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun s => plantStorage P x s)
      (plantSupplyRate P x t - plantLossRate P x t) t := by
  obtain ⟨hV, hbal, hRlaw, hClaw, hLlaw, hCdiff, hLdiff⟩ := hP
  have hnhds : Set.Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have htI : t ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht
  have hCdiff' : ∀ e ∈ P.capacitorSet,
      DifferentiableAt ℝ (fun s => x.branchVoltage s e) t :=
    fun e he => (hCdiff t htI e he).differentiableAt hnhds
  have hLdiff' : ∀ e ∈ P.inductorSet,
      DifferentiableAt ℝ (fun s => x.branchCurrent s e) t :=
    fun e he => (hLdiff t htI e he).differentiableAt hnhds
  have hClaw' : ∀ e ∈ P.capacitorSet, x.branchCurrent t e =
      P.capacitance e * deriv (fun s => x.branchVoltage s e) t := by
    intro e he
    rw [hClaw t htI e he, derivWithin_of_mem_nhds hnhds]
  have hLlaw' : ∀ e ∈ P.inductorSet, x.branchVoltage t e =
      P.inductance e * deriv (fun s => x.branchCurrent s e) t := by
    intro e he
    rw [hLlaw t htI e he, derivWithin_of_mem_nhds hnhds]
  have hE := hasDerivAt_storedEnergy nB P.capacitorSet P.inductorSet
    P.capacitance P.inductance x.branchVoltage x.branchCurrent t
    hClaw' hLlaw' hCdiff' hLdiff'
  have hbalance := network_storage_deriv_eq_supplied_minus_losses nN nB P.incidence
    P.resistorSet P.inductorSet P.capacitorSet P.sourceSet P.isBranchPartition
    P.resistance P.inductance P.capacitance hR hL hC
    x.potential x.injection x.branchVoltage x.branchCurrent t
    (hV t htI) (hbal t htI) (hRlaw t htI) hClaw' hLlaw' hCdiff' hLdiff'
  rw [hE.deriv] at hbalance
  exact hE.congr_deriv hbalance

/-- Finite-horizon passivity under interval-scoped trajectory hypotheses:
if the network laws hold on `[a, b]`, with continuous supply rate and
integrable balance rate there, the increase of storage is at most the
integral of the supply rate. -/
lemma plant_finiteHorizonPassive_of_trajectoryOn {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e)
    (x : NetworkTrajectory nN nB) (a b : ℝ) (hab : a ≤ b)
    (hP : IsNetworkTrajectoryOn P x (Set.Icc a b))
    (hsupply_cont : ContinuousOn (fun s => plantSupplyRate P x s) (Set.Icc a b))
    (hderiv_int : IntervalIntegrable (fun s => plantSupplyRate P x s - plantLossRate P x s)
      MeasureTheory.volume a b) :
    FiniteHorizonPassiveOn P x a b := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hP.continuousOn_plantStorage (fun t ht => hP.hasDerivAt_plantStorage hR hL hC ht)
    hderiv_int
  have hsupplied_int : IntervalIntegrable (fun s => plantSupplyRate P x s)
      MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hsupply_cont
  have hle : ∀ s ∈ Set.Icc a b,
      plantSupplyRate P x s - plantLossRate P x s ≤ plantSupplyRate P x s :=
    fun s _ => sub_le_self _ (plantLossRate_nonneg P hR x s)
  unfold FiniteHorizonPassiveOn
  rw [← hFTC]
  exact intervalIntegral.integral_mono_on hab hderiv_int hsupplied_int hle

/-- Plant passivity: a plant with nonnegative resistances and positive
reactive values is finite-horizon passive along every admissible
trajectory on every interval. -/
lemma networkPlant_isFiniteHorizonPassive {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) :
    IsFiniteHorizonPassive P :=
  fun x a b hab hP hcont hint =>
    plant_finiteHorizonPassive_of_trajectoryOn P hR hL hC x a b hab hP hcont hint

/-- Zero-length interval: passivity on a degenerate interval is the
statement that zero storage increase is at most zero supplied energy. -/
lemma finiteHorizonPassive_zeroLength {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (a : ℝ) :
    plantStorage P x a - plantStorage P x a ≤ ∫ s in a..a, plantSupplyRate P x s := by
  simp [intervalIntegral.integral_same]

/-- Finite-horizon passivity: on a network trajectory over an interval,
with continuous supply rate and integrable balance rate, the increase of
storage is at most the integral of the supply rate. -/
lemma plant_finiteHorizonPassive {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (hP : IsNetworkTrajectory P x)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (a b : ℝ) (hab : a ≤ b)
    (hsupply_cont : ContinuousOn (fun s => plantSupplyRate P x s) (Set.Icc a b))
    (hderiv_int : IntervalIntegrable (fun s => plantSupplyRate P x s - plantLossRate P x s)
      MeasureTheory.volume a b) :
    FiniteHorizonPassiveOn P x a b := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact plant_finiteHorizonPassive_of_trajectoryOn P hR hL hC x a b hab
      (hP.isNetworkTrajectoryOn (uniqueDiffOn_Icc hlt)) hsupply_cont hderiv_int
  · exact finiteHorizonPassive_zeroLength P x _

/-- Headline passivity correctness for a fixed plant: along every
trajectory storage is nonnegative, along every network trajectory the
storage derivative is supply minus loss, and every admissible trajectory
is finite-horizon passive on every interval satisfying the stated
regularity. -/
lemma networkPlant_passivity {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) :
    (∀ (x : NetworkTrajectory nN nB) (t : ℝ), 0 ≤ plantStorage P x t) ∧
      (∀ x : NetworkTrajectory nN nB, IsNetworkTrajectory P x → ∀ t : ℝ,
        deriv (fun s => plantStorage P x s) t =
          plantSupplyRate P x t - plantLossRate P x t) ∧
      IsFiniteHorizonPassive P := by
  refine ⟨?_, ?_, networkPlant_isFiniteHorizonPassive P hR hL hC⟩
  · intro x t
    exact plantStorage_nonneg P (fun e he => le_of_lt (hC e he))
      (fun e he => le_of_lt (hL e he)) x t
  · intro x hP t
    exact plantStorage_deriv_eq_supply_sub_loss P x hP hR hL hC t

/-! ### D. Validation cases -/

/-- Undamped case under interval-scoped trajectory hypotheses: if the
network laws hold on `[a, b]` and the supply and loss rates vanish there,
storage is constant on that interval, not decaying: at every time of
`[a, b]` it equals its value at `a`. -/
lemma plantStorage_constant_of_zero_supply_loss_of_trajectoryOn {nN nB : ℕ}
    (P : NetworkPlant nN nB)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e)
    (x : NetworkTrajectory nN nB) (a b : ℝ) (hab : a ≤ b)
    (hP : IsNetworkTrajectoryOn P x (Set.Icc a b))
    (hsupply : ∀ s ∈ Set.Icc a b, plantSupplyRate P x s = 0)
    (hloss : ∀ s ∈ Set.Icc a b, plantLossRate P x s = 0)
    (hderiv_int : IntervalIntegrable (fun s => plantSupplyRate P x s - plantLossRate P x s)
      MeasureTheory.volume a b) :
    ∀ t ∈ Set.Icc a b, plantStorage P x t = plantStorage P x a := by
  intro t ht
  have hsub : Set.Icc a t ⊆ Set.Icc a b := Set.Icc_subset_Icc_right ht.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hP.continuousOn_plantStorage.mono hsub)
    (fun s hs => hP.hasDerivAt_plantStorage hR hL hC ⟨hs.1, hs.2.trans_le ht.2⟩)
    (hderiv_int.mono_set (by rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]; exact hsub))
  have hEqOn : Set.EqOn (fun s => plantSupplyRate P x s - plantLossRate P x s)
      (fun _ => (0 : ℝ)) (Set.uIcc a t) := by
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    change plantSupplyRate P x s - plantLossRate P x s = 0
    rw [hsupply s (hsub hs), hloss s (hsub hs), sub_self]
  rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_zero] at hFTC
  exact (sub_eq_zero.mp hFTC.symm)

/-- Undamped case: if supply and loss rates vanish on an interval and the
trajectory hypotheses hold there, storage is constant on that interval, not
decaying: at every time of `[a, b]` it equals its value at `a`. -/
lemma plantStorage_constant_of_zero_supply_loss {nN nB : ℕ} (P : NetworkPlant nN nB)
    (x : NetworkTrajectory nN nB) (hP : IsNetworkTrajectory P x)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (a b : ℝ) (hab : a ≤ b)
    (hsupply : ∀ s ∈ Set.Icc a b, plantSupplyRate P x s = 0)
    (hloss : ∀ s ∈ Set.Icc a b, plantLossRate P x s = 0)
    (hderiv_int : IntervalIntegrable (fun s => plantSupplyRate P x s - plantLossRate P x s)
      MeasureTheory.volume a b) :
    ∀ t ∈ Set.Icc a b, plantStorage P x t = plantStorage P x a := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact plantStorage_constant_of_zero_supply_loss_of_trajectoryOn P hR hL hC x a b hab
      (hP.isNetworkTrajectoryOn (uniqueDiffOn_Icc hlt)) hsupply hloss hderiv_int
  · intro t ht
    rw [le_antisymm ht.2 ht.1]

/-- Exact accounting: the branch partition of a plant puts no branch in two
classes, so no source branch is also counted as a resistor, inductor or
capacitor branch. -/
lemma partition_no_branch_counted_twice {nN nB : ℕ} (P : NetworkPlant nN nB)
    (e : Fin nB) (he : e ∈ P.sourceSet) :
    e ∉ P.resistorSet ∧ e ∉ P.inductorSet ∧ e ∉ P.capacitorSet := by
  obtain ⟨-, -, hRS, -, hLS, hCS, -⟩ := P.isBranchPartition
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact absurd he (Finset.disjoint_left.mp hRS h)
  · intro h
    exact absurd he (Finset.disjoint_left.mp hLS h)
  · intro h
    exact absurd he (Finset.disjoint_left.mp hCS h)

end PhyslibExt.Circuits.NetworkPlantPassivity
