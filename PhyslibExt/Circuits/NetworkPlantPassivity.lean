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
that network off as a plant: `NetworkPlant` packages the incidence
matrix, the branch partition, the element values and one trajectory
of node potentials, independent node injections, branch voltages
and branch currents. Storage, supply rate and loss rate are read
directly from the canonical network storage, source absorbed power
and resistive loss, so no second storage or power definition is
introduced here.

The `NetworkPlant` read-off interface is owned by this leaf: no
canonical plant interface exists in the library at the time of
writing, so `NetworkPlant`, `plantStorage`, `plantSupplyRate`,
`plantLossRate` and `FiniteHorizonPassiveOn` are defined here and
read the merged network carrier directly. A network trajectory is
a plant trajectory with the same storage and the same supply rate,
its storage derivative is supply minus resistive loss, and over a
finite interval the increase of storage is at most the integral of
the supply rate. That finite-horizon inequality is the passivity
statement. No trajectory existence is asserted, no asymptotic
stability is claimed, and no wider control framework is introduced.

## ii. Key results

- `plantOfNetwork_storage_eq`, `plantOfNetwork_supplyAndLoss_eq`
  and `plantOfNetwork_trajectory_eq`: the identity representation
  of raw network data as a plant preserves storage, supply and
  loss rates, and the trajectory data itself.
- `plantStorage_nonneg`: plant storage is nonnegative for
  nonnegative capacitance and inductance.
- `plantStorage_deriv_eq_supply_sub_loss`: on a network
  trajectory, the derivative of plant storage is the supply rate
  minus the resistive loss rate.
- `plant_finiteHorizonPassive` and `networkPlant_passivity`: the
  finite-horizon passivity bound, packaged with storage
  nonnegativity and the storage balance.
- `plantStorage_constant_of_zero_supply_loss`,
  `finiteHorizonPassive_zeroLength` and
  `partition_no_branch_counted_twice`: validation cases covering
  constant undamped storage, a zero-length interval, and exact
  branch accounting with no source branch counted twice.

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

/-- Scoped plant data for one lumped network: incidence, branch partition,
element values and one trajectory of potentials, injections, branch
voltages and branch currents. New definition owned by this leaf. -/
structure NetworkPlant (nN nB : ℕ) where
  incidence : Matrix (Fin nN) (Fin nB) ℝ
  resistorSet : Finset (Fin nB)
  inductorSet : Finset (Fin nB)
  capacitorSet : Finset (Fin nB)
  sourceSet : Finset (Fin nB)
  resistance : Fin nB → ℝ
  inductance : Fin nB → ℝ
  capacitance : Fin nB → ℝ
  potential : ℝ → Fin nN → ℝ
  injection : ℝ → Fin nN → ℝ
  branchVoltage : ℝ → Fin nB → ℝ
  branchCurrent : ℝ → Fin nB → ℝ

/-- Storage of a plant at a time, read directly from the network storage. -/
noncomputable def plantStorage {nN nB : ℕ} (P : NetworkPlant nN nB) (t : ℝ) : ℝ :=
  storedEnergy nB P.capacitorSet P.inductorSet P.capacitance P.inductance
    (P.branchVoltage t) (P.branchCurrent t)

/-- Supply rate of a plant: node supplied power minus source absorbed
power. -/
def plantSupplyRate {nN nB : ℕ} (P : NetworkPlant nN nB) (t : ℝ) : ℝ :=
  (P.potential t) ⬝ᵥ (P.injection t) -
    sourceAbsorbedPower nB P.sourceSet (P.branchVoltage t) (P.branchCurrent t)

/-- Resistive loss rate of a plant. -/
def plantLossRate {nN nB : ℕ} (P : NetworkPlant nN nB) (t : ℝ) : ℝ :=
  resistiveLoss nB P.resistorSet P.resistance (P.branchCurrent t)

/-- The plant trajectory obeys the network laws: exact branch partition,
potential voltage, node current balance for the independent injection, and
the resistor, capacitor and inductor laws with differentiability of the
storage coordinates at every time. -/
def IsNetworkTrajectory {nN nB : ℕ} (P : NetworkPlant nN nB) : Prop :=
  IsBranchPartition nB P.resistorSet P.inductorSet P.capacitorSet P.sourceSet ∧
    (∀ t : ℝ, P.branchVoltage t = P.incidence.transpose *ᵥ P.potential t) ∧
    (∀ t : ℝ, P.incidence *ᵥ P.branchCurrent t = P.injection t) ∧
    (∀ t : ℝ, ∀ e ∈ P.resistorSet, P.branchVoltage t e =
      P.resistance e * P.branchCurrent t e) ∧
    (∀ t : ℝ, ∀ e ∈ P.capacitorSet, P.branchCurrent t e =
      P.capacitance e * deriv (fun s => P.branchVoltage s e) t) ∧
    (∀ t : ℝ, ∀ e ∈ P.inductorSet, P.branchVoltage t e =
      P.inductance e * deriv (fun s => P.branchCurrent s e) t) ∧
    (∀ t : ℝ, ∀ e ∈ P.capacitorSet,
      DifferentiableAt ℝ (fun s => P.branchVoltage s e) t) ∧
    (∀ t : ℝ, ∀ e ∈ P.inductorSet,
      DifferentiableAt ℝ (fun s => P.branchCurrent s e) t)

/-- Finite-horizon passivity of a plant on an interval: the increase of
storage is at most the integral of the supply rate. -/
def FiniteHorizonPassiveOn {nN nB : ℕ} (P : NetworkPlant nN nB) (a b : ℝ) : Prop :=
  plantStorage P b - plantStorage P a ≤ ∫ s in a..b, plantSupplyRate P s

/-- The identity representation of raw network data as a plant. -/
def plantOfNetwork (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval : Fin nB → ℝ)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) : NetworkPlant nN nB where
  incidence := B
  resistorSet := Rset
  inductorSet := Lset
  capacitorSet := Cset
  sourceSet := Sset
  resistance := Rval
  inductance := Lval
  capacitance := Cval
  potential := phi
  injection := j
  branchVoltage := v
  branchCurrent := iB

/-! ### B. Representation preservation -/

/-- Representation preserves storage: the plant built from network data has
exactly the network stored energy at every time. -/
lemma plantOfNetwork_storage_eq (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval : Fin nB → ℝ)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) (t : ℝ) :
    plantStorage (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB) t =
      storedEnergy nB Cset Lset Cval Lval (v t) (iB t) := by
  rfl

/-- Representation preserves supply and loss: the plant supply and loss
rates are exactly the network supplied-minus-source power and resistive
loss. -/
lemma plantOfNetwork_supplyAndLoss_eq (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval : Fin nB → ℝ)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) (t : ℝ) :
    plantSupplyRate (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB) t =
        (phi t) ⬝ᵥ (j t) - sourceAbsorbedPower nB Sset (v t) (iB t) ∧
      plantLossRate (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB) t =
        resistiveLoss nB Rset Rval (iB t) := by
  exact ⟨rfl, rfl⟩

/-- Representation preserves trajectories: the plant built from network
data has the same potentials, injections, branch voltages and branch
currents as the data. -/
lemma plantOfNetwork_trajectory_eq (nN nB : ℕ) (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB)) (Rval Lval Cval : Fin nB → ℝ)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) :
    (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB).potential = phi ∧
      (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB).injection = j ∧
      (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB).branchVoltage = v ∧
      (plantOfNetwork nN nB B Rset Lset Cset Sset Rval Lval Cval phi j v iB).branchCurrent =
        iB := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### C. Storage balance and finite-horizon passivity -/

/-- Resistive loss rate is nonnegative for nonnegative resistances. -/
private lemma plantLossRate_nonneg {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e) (t : ℝ) :
    0 ≤ plantLossRate P t := by
  unfold plantLossRate resistiveLoss
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg (hR e he) (sq_nonneg _)

/-- Storage balance at the `HasDerivAt` level: on a network trajectory the
storage has derivative supply minus loss. -/
private lemma hasDerivAt_plantStorage {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hP : IsNetworkTrajectory P)
    (_hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (_hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (_hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (t : ℝ) :
    HasDerivAt (fun s => plantStorage P s)
      (plantSupplyRate P t - plantLossRate P t) t := by
  unfold IsNetworkTrajectory at hP
  obtain ⟨hpart, hV, hbal, hRlaw, hClaw, hLlaw, hCdiff, hLdiff⟩ := hP
  unfold IsBranchPartition at hpart
  obtain ⟨hRL, hRC, hRS, hLC, hLS, hCS, hcover⟩ := hpart
  have hC : ∀ e ∈ P.capacitorSet,
      HasDerivAt (fun s => P.capacitance e * (P.branchVoltage s e) ^ 2 / 2)
        (P.branchVoltage t e * P.branchCurrent t e) t := by
    intro e he
    have hu : HasDerivAt (fun s => P.branchVoltage s e)
        (deriv (fun s => P.branchVoltage s e) t) t :=
      (hCdiff t e he).hasDerivAt
    have hpow : HasDerivAt (fun s => (P.branchVoltage s e) ^ 2)
        (2 * P.branchVoltage t e * deriv (fun s => P.branchVoltage s e) t) t := by
      have h := hu.pow 2
      norm_num at h
      exact h
    have h0 := HasDerivAt.div_const
      (HasDerivAt.const_mul (P.capacitance e) hpow) 2
    have hcap := hClaw t e he
    have hval : P.capacitance e * (2 * P.branchVoltage t e *
        deriv (fun s => P.branchVoltage s e) t) / 2 =
        P.branchVoltage t e * P.branchCurrent t e := by
      rw [hcap]
      ring
    rw [hval] at h0
    exact h0
  have hL : ∀ e ∈ P.inductorSet,
      HasDerivAt (fun s => P.inductance e * (P.branchCurrent s e) ^ 2 / 2)
        (P.branchVoltage t e * P.branchCurrent t e) t := by
    intro e he
    have hu : HasDerivAt (fun s => P.branchCurrent s e)
        (deriv (fun s => P.branchCurrent s e) t) t :=
      (hLdiff t e he).hasDerivAt
    have hpow : HasDerivAt (fun s => (P.branchCurrent s e) ^ 2)
        (2 * P.branchCurrent t e * deriv (fun s => P.branchCurrent s e) t) t := by
      have h := hu.pow 2
      norm_num at h
      exact h
    have h0 := HasDerivAt.div_const
      (HasDerivAt.const_mul (P.inductance e) hpow) 2
    have hLaw := hLlaw t e he
    have hval : P.inductance e * (2 * P.branchCurrent t e *
        deriv (fun s => P.branchCurrent s e) t) / 2 =
        P.branchVoltage t e * P.branchCurrent t e := by
      rw [hLaw]
      ring
    rw [hval] at h0
    exact h0
  have hsumC := HasDerivAt.sum hC
  have hsumL := HasDerivAt.sum hL
  have hadd := hsumC.add hsumL
  have hfun : ((∑ e ∈ P.capacitorSet,
      (fun s => P.capacitance e * (P.branchVoltage s e) ^ 2 / 2)) +
      (∑ e ∈ P.inductorSet,
        (fun s => P.inductance e * (P.branchCurrent s e) ^ 2 / 2))) =
      (fun s => plantStorage P s) := by
    funext s
    simp [plantStorage, storedEnergy, Pi.add_apply, Finset.sum_apply]
  have hRpow : plantLossRate P t =
      ∑ e ∈ P.resistorSet, P.branchVoltage t e * P.branchCurrent t e := by
    unfold plantLossRate resistiveLoss
    apply Finset.sum_congr rfl
    intro e he
    show P.resistance e * (P.branchCurrent t e) ^ 2 =
      P.branchVoltage t e * P.branchCurrent t e
    have hRv := hRlaw t e he
    rw [hRv]
    ring
  have htel : (P.potential t) ⬝ᵥ (P.injection t) =
      ∑ e, P.branchVoltage t e * P.branchCurrent t e := by
    have hVt := hV t
    have hjt := hbal t
    rw [← hjt, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hVt]
    rfl
  have hsplit : (∑ e, P.branchVoltage t e * P.branchCurrent t e) =
      (∑ e ∈ P.resistorSet, P.branchVoltage t e * P.branchCurrent t e) +
      (∑ e ∈ P.inductorSet, P.branchVoltage t e * P.branchCurrent t e) +
      (∑ e ∈ P.capacitorSet, P.branchVoltage t e * P.branchCurrent t e) +
      (∑ e ∈ P.sourceSet, P.branchVoltage t e * P.branchCurrent t e) := by
    have h1 : Disjoint (P.resistorSet ∪ P.inductorSet ∪ P.capacitorSet)
        P.sourceSet :=
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hRS, hLS⟩, hCS⟩
    have h2 : Disjoint (P.resistorSet ∪ P.inductorSet) P.capacitorSet :=
      Finset.disjoint_union_left.mpr ⟨hRC, hLC⟩
    conv_lhs => rw [← hcover, Finset.sum_union h1, Finset.sum_union h2,
      Finset.sum_union hRL]
  have hval : (∑ e ∈ P.capacitorSet, P.branchVoltage t e * P.branchCurrent t e) +
      (∑ e ∈ P.inductorSet, P.branchVoltage t e * P.branchCurrent t e) =
      plantSupplyRate P t - plantLossRate P t := by
    unfold plantSupplyRate sourceAbsorbedPower
    rw [htel, hsplit, hRpow]
    ring
  rw [← hfun, ← hval]
  exact hadd

/-- Storage is nonnegative for nonnegative capacitance and inductance. -/
lemma plantStorage_nonneg {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hC : ∀ e ∈ P.capacitorSet, 0 ≤ P.capacitance e)
    (hL : ∀ e ∈ P.inductorSet, 0 ≤ P.inductance e) (t : ℝ) :
    0 ≤ plantStorage P t := by
  unfold plantStorage storedEnergy
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro e he
    exact div_nonneg (mul_nonneg (hC e he) (sq_nonneg _)) (by norm_num)
  · apply Finset.sum_nonneg
    intro e he
    exact div_nonneg (mul_nonneg (hL e he) (sq_nonneg _)) (by norm_num)

/-- Storage balance: on a network trajectory with nonnegative resistances
and positive reactive values, the derivative of storage is the supply rate
minus the resistive loss rate. -/
lemma plantStorage_deriv_eq_supply_sub_loss {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hP : IsNetworkTrajectory P)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (t : ℝ) :
    deriv (fun s => plantStorage P s) t = plantSupplyRate P t - plantLossRate P t := by
  exact (hasDerivAt_plantStorage P hP hR hL hC t).deriv

/-- Finite-horizon passivity: on a network trajectory over an interval,
with continuous supply rate and integrable balance rate, the increase of
storage is at most the integral of the supply rate. -/
lemma plant_finiteHorizonPassive {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hP : IsNetworkTrajectory P)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (a b : ℝ) (hab : a ≤ b)
    (hsupply_cont : ContinuousOn (fun s => plantSupplyRate P s) (Set.Icc a b))
    (hderiv_int : IntervalIntegrable (fun s => plantSupplyRate P s - plantLossRate P s)
      MeasureTheory.volume a b) :
    FiniteHorizonPassiveOn P a b := by
  have hHas : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun s => plantStorage P s)
      (plantSupplyRate P x - plantLossRate P x) x :=
    fun x _ => hasDerivAt_plantStorage P hP hR hL hC x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => plantStorage P s)
    (f' := fun s => plantSupplyRate P s - plantLossRate P s) hHas hderiv_int
  have hSupInt : IntervalIntegrable (fun s => plantSupplyRate P s)
      MeasureTheory.volume a b :=
    hsupply_cont.intervalIntegrable_of_Icc hab
  have hle : ∀ x ∈ Set.Icc a b,
      plantSupplyRate P x - plantLossRate P x ≤ plantSupplyRate P x :=
    fun x _ => sub_le_self _ (plantLossRate_nonneg P hR x)
  have hMono := intervalIntegral.integral_mono_on
    (f := fun s => plantSupplyRate P s - plantLossRate P s)
    (g := fun s => plantSupplyRate P s) hab hderiv_int hSupInt hle
  have hEq : plantStorage P b - plantStorage P a =
      ∫ y in a..b, (plantSupplyRate P y - plantLossRate P y) := hFTC.symm
  change plantStorage P b - plantStorage P a ≤ ∫ s in a..b, plantSupplyRate P s
  rw [hEq]
  exact hMono

/-- Headline passivity correctness: a network trajectory has nonnegative
storage at every time, its storage derivative is supply minus loss, and it
is finite-horizon passive on every interval satisfying the stated
regularity. -/
lemma networkPlant_passivity {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hP : IsNetworkTrajectory P)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) :
    (∀ t : ℝ, 0 ≤ plantStorage P t) ∧
      (∀ t : ℝ, deriv (fun s => plantStorage P s) t =
        plantSupplyRate P t - plantLossRate P t) ∧
      (∀ a b : ℝ, a ≤ b →
        ContinuousOn (fun s => plantSupplyRate P s) (Set.Icc a b) →
        IntervalIntegrable (fun s => plantSupplyRate P s - plantLossRate P s)
          MeasureTheory.volume a b →
        FiniteHorizonPassiveOn P a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact plantStorage_nonneg P (fun e he => le_of_lt (hC e he))
      (fun e he => le_of_lt (hL e he)) t
  · intro t
    exact plantStorage_deriv_eq_supply_sub_loss P hP hR hL hC t
  · intro a b hab hcont hint
    exact plant_finiteHorizonPassive P hP hR hL hC a b hab hcont hint

/-! ### D. Validation cases -/

/-- Undamped case: if supply and loss rates vanish on an interval and the
trajectory hypotheses hold there, storage is constant on that interval, not
decaying. -/
lemma plantStorage_constant_of_zero_supply_loss {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hP : IsNetworkTrajectory P)
    (hR : ∀ e ∈ P.resistorSet, 0 ≤ P.resistance e)
    (hL : ∀ e ∈ P.inductorSet, 0 < P.inductance e)
    (hC : ∀ e ∈ P.capacitorSet, 0 < P.capacitance e) (a b : ℝ) (hab : a ≤ b)
    (hsupply : ∀ s ∈ Set.Icc a b, plantSupplyRate P s = 0)
    (hloss : ∀ s ∈ Set.Icc a b, plantLossRate P s = 0)
    (hderiv_int : IntervalIntegrable (fun s => plantSupplyRate P s - plantLossRate P s)
      MeasureTheory.volume a b) :
    plantStorage P b = plantStorage P a := by
  have hHas : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun s => plantStorage P s)
      (plantSupplyRate P x - plantLossRate P x) x :=
    fun x _ => hasDerivAt_plantStorage P hP hR hL hC x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => plantStorage P s)
    (f' := fun s => plantSupplyRate P s - plantLossRate P s) hHas hderiv_int
  have hEqOn : Set.EqOn (fun s => plantSupplyRate P s - plantLossRate P s)
      (fun _ => (0 : ℝ)) (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    change plantSupplyRate P x - plantLossRate P x = 0
    rw [hsupply x hx, hloss x hx, sub_self]
  have hcongr : (∫ y in a..b, (plantSupplyRate P y - plantLossRate P y)) =
      (∫ y in a..b, (0 : ℝ)) :=
    intervalIntegral.integral_congr hEqOn
  have hEq : plantStorage P b - plantStorage P a = ∫ y in a..b, (0 : ℝ) := by
    have h1 : plantStorage P b - plantStorage P a =
        ∫ y in a..b, (plantSupplyRate P y - plantLossRate P y) := hFTC.symm
    rw [h1]
    exact hcongr
  have hzero : (∫ y in a..b, (0 : ℝ)) = 0 := intervalIntegral.integral_zero
  have hsub : plantStorage P b - plantStorage P a = 0 := by rw [hEq, hzero]
  exact sub_eq_zero.mp hsub

/-- Zero-length interval: passivity on a degenerate interval is the
statement that zero storage increase is at most zero supplied energy. -/
lemma finiteHorizonPassive_zeroLength {nN nB : ℕ} (P : NetworkPlant nN nB) (a : ℝ) :
    plantStorage P a - plantStorage P a ≤ ∫ s in a..a, plantSupplyRate P s := by
  simp [intervalIntegral.integral_same]

/-- Exact accounting: under the branch partition no branch lies in two
classes, so no source branch is also counted as a resistor, inductor or
capacitor branch. -/
lemma partition_no_branch_counted_twice {nN nB : ℕ} (P : NetworkPlant nN nB)
    (hpart : IsBranchPartition nB P.resistorSet P.inductorSet P.capacitorSet P.sourceSet)
    (e : Fin nB) (he : e ∈ P.sourceSet) :
    e ∉ P.resistorSet ∧ e ∉ P.inductorSet ∧ e ∉ P.capacitorSet := by
  unfold IsBranchPartition at hpart
  obtain ⟨-, -, hRS, -, hLS, hCS, -⟩ := hpart
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact absurd he (Finset.disjoint_left.mp hRS h)
  · intro h
    exact absurd he (Finset.disjoint_left.mp hLS h)
  · intro h
    exact absurd he (Finset.disjoint_left.mp hCS h)

end PhyslibExt.Circuits.NetworkPlantPassivity
