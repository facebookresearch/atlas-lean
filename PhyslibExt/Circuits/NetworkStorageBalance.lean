/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import PhyslibExt.Circuits.TellegenPowerBalance
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Network storage balance

## i. Overview

The sole lumped R/L/C/source branch-partition carrier for ECE
network energy accounting. Branches are partitioned exactly once
into resistor, inductor, capacitor and source classes; branch
voltages come from node potentials through the (head-positive)
incidence transpose `v = Bᵀ *ᵥ phi` and branch currents satisfy
KCL `B *ᵥ iB = j` with independently supplied node injections `j`.
Stored energy is diagonal only:
`∑_C C_e * v_e^2 / 2 + ∑_L L_e * i_e^2 / 2`, no mutual inductance.
Source branches and injections are separate binders and are each
counted once. Real model only; no complex AC or SPD argument is
used.

## ii. Key results

- `branch_power_eq_node_power`: Tellegen's identity
  `v ⬝ᵥ iB = phi ⬝ᵥ j` from KVL and KCL, the `Fin`-indexed
  specialization of
  `PhyslibExt.Circuits.TellegenPowerBalance.branchPower_eq_nodePower`.
- `storedEnergy_nonneg`: stored energy is nonnegative for
  nonnegative capacitance and inductance values.
- `hasDerivAt_storedEnergy`: the stored-energy derivative is the
  sum of capacitor and inductor branch powers.
- `network_storage_deriv_eq_supplied_minus_losses`: the headline
  balance `dE/dt = phi ⬝ᵥ j - sourceAbsorbedPower - resistiveLoss`.
- `network_energy_sub_le_integral_supplied`: the finite-horizon
  FTC corollary bounding the stored-energy increase by the
  integral of supplied power under nonnegative losses.

## iii. Table of contents

- A. The branch-partition storage carrier

## iv. References

- J. W. Nilsson and S. A. Riedel, *Electric Circuits*, eleventh
  edition, Pearson, 2019: branch power balance (Tellegen's
  theorem), capacitor and inductor stored energy, and absorbed
  power sign conventions.

## A. The branch-partition storage carrier
-/

@[expose] public section

namespace PhyslibExt.Circuits.NetworkStorageBalance

/-- Branch partition carrier: `Rset`, `Lset`, `Cset`, `Sset` are
pairwise disjoint and cover every branch exactly once. This is the
sole lumped R/L/C/source partition owned by this leaf. -/
def IsBranchPartition (nB : ℕ) (Rset Lset Cset Sset : Finset (Fin nB)) :
    Prop :=
  Disjoint Rset Lset ∧ Disjoint Rset Cset ∧ Disjoint Rset Sset ∧
    Disjoint Lset Cset ∧ Disjoint Lset Sset ∧ Disjoint Cset Sset ∧
    Rset ∪ Lset ∪ Cset ∪ Sset = Finset.univ

/-- Stored energy: capacitor energy plus inductor energy,
`sum_C C_e * (v_e)^2 / 2 + sum_L L_e * (i_e)^2 / 2`. Diagonal only;
no mutual inductance. -/
noncomputable def storedEnergy (nB : ℕ) (Cset Lset : Finset (Fin nB))
    (Cval Lval : Fin nB → ℝ) (v iB : Fin nB → ℝ) : ℝ :=
  (∑ e ∈ Cset, Cval e * (v e) ^ 2 / 2) +
    ∑ e ∈ Lset, Lval e * (iB e) ^ 2 / 2

/-- Resistive absorbed power (loss): `sum_R R_e * (i_e)^2`. -/
def resistiveLoss (nB : ℕ) (Rset : Finset (Fin nB))
    (Rval : Fin nB → ℝ) (iB : Fin nB → ℝ) : ℝ :=
  ∑ e ∈ Rset, Rval e * (iB e) ^ 2

/-- Source absorbed power: `sum_source v_e * i_e`. Delivered source
power is minus this quantity. -/
def sourceAbsorbedPower (nB : ℕ) (Sset : Finset (Fin nB))
    (v iB : Fin nB → ℝ) : ℝ :=
  ∑ e ∈ Sset, v e * iB e

/-- Tellegen / matrix power balance: under KVL `v = B^T phi` and
KCL `B i = j`, total branch absorbed power `v ⬝ᵥ i` equals supplied
node power `phi ⬝ᵥ j`. This is the `Fin`-indexed specialization of
`PhyslibExt.Circuits.TellegenPowerBalance.branchPower_eq_nodePower`. -/
lemma branch_power_eq_node_power (nN nB : ℕ)
    (B : Matrix (Fin nN) (Fin nB) ℝ) (phi : Fin nN → ℝ)
    (j : Fin nN → ℝ) (v iB : Fin nB → ℝ)
    (hKVL : v = Matrix.mulVec (Matrix.transpose B) phi)
    (hKCL : Matrix.mulVec B iB = j) :
    dotProduct v iB = dotProduct phi j :=
  PhyslibExt.Circuits.TellegenPowerBalance.branchPower_eq_nodePower B phi j v iB hKVL hKCL

/-- Total branch absorbed power splits over the four partition
classes exactly once. -/
lemma total_branch_power_eq_sum_classes (nB : ℕ)
    (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset)
    (v iB : Fin nB → ℝ) :
    (∑ e : Fin nB, v e * iB e) =
      (∑ e ∈ Rset, v e * iB e) + (∑ e ∈ Lset, v e * iB e) +
        (∑ e ∈ Cset, v e * iB e) + (∑ e ∈ Sset, v e * iB e) := by
  obtain ⟨hRL, hRC, hRS, hLC, hLS, hCS, hunion⟩ := hpart
  have hRL_disj_C : Disjoint (Rset ∪ Lset) Cset :=
    Finset.disjoint_union_left.mpr ⟨hRC, hLC⟩
  have hRL_disj_S : Disjoint (Rset ∪ Lset) Sset :=
    Finset.disjoint_union_left.mpr ⟨hRS, hLS⟩
  have hRLC_disj_S : Disjoint (Rset ∪ Lset ∪ Cset) Sset :=
    Finset.disjoint_union_left.mpr ⟨hRL_disj_S, hCS⟩
  have huniv : (∑ e : Fin nB, v e * iB e)
      = ∑ e ∈ Rset ∪ Lset ∪ Cset ∪ Sset, v e * iB e := by
    rw [hunion]
  rw [huniv, Finset.sum_union hRLC_disj_S, Finset.sum_union hRL_disj_C,
    Finset.sum_union hRL]

/-- Stored energy is nonnegative when capacitance and inductance
values are nonnegative on their classes. -/
lemma storedEnergy_nonneg (nB : ℕ) (Cset Lset : Finset (Fin nB))
    (Cval Lval : Fin nB → ℝ) (v iB : Fin nB → ℝ)
    (hC : ∀ e ∈ Cset, 0 ≤ Cval e) (hL : ∀ e ∈ Lset, 0 ≤ Lval e) :
    0 ≤ storedEnergy nB Cset Lset Cval Lval v iB := by
  unfold storedEnergy
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro e he
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (hC e he)
    exact sq_nonneg _
  · apply Finset.sum_nonneg
    intro e he
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg (hL e he)
    exact sq_nonneg _

/-- Derivative of stored energy is the absorbed power of the
capacitor and inductor branches, under their constitutive laws and
differentiability of the storage coordinates at `t`. -/
lemma hasDerivAt_storedEnergy (nB : ℕ)
    (Cset Lset : Finset (Fin nB)) (Cval Lval : Fin nB → ℝ)
    (v iB : ℝ → Fin nB → ℝ) (t : ℝ)
    (hClaw : ∀ e ∈ Cset, iB t e = Cval e * deriv (fun s => v s e) t)
    (hLlaw : ∀ e ∈ Lset, v t e = Lval e * deriv (fun s => iB s e) t)
    (hCdiff : ∀ e ∈ Cset, DifferentiableAt ℝ (fun s => v s e) t)
    (hLdiff : ∀ e ∈ Lset, DifferentiableAt ℝ (fun s => iB s e) t) :
    HasDerivAt (fun s => storedEnergy nB Cset Lset Cval Lval (v s) (iB s))
      ((∑ e ∈ Cset, v t e * iB t e) + ∑ e ∈ Lset, v t e * iB t e) t := by
  have hC_branch : ∀ e ∈ Cset,
      HasDerivAt (fun s => Cval e * (v s e) ^ 2 / 2) (v t e * iB t e) t := by
    intro e he
    have hdiff : HasDerivAt (fun s => v s e) (deriv (fun s => v s e) t) t :=
      (hCdiff e he).hasDerivAt
    have hmul := hdiff.fun_mul hdiff
    have hpow : HasDerivAt (fun s => (v s e) ^ 2)
        (deriv (fun s => v s e) t * v t e + v t e * deriv (fun s => v s e) t) t := by
      simpa only [← pow_two] using hmul
    have hcmul := hpow.const_mul (Cval e)
    have hdiv := hcmul.div_const 2
    have hclaw := hClaw e he
    have hder : Cval e * (deriv (fun s => v s e) t * v t e +
        v t e * deriv (fun s => v s e) t) / 2 = v t e * iB t e := by
      rw [hclaw]
      ring
    convert hdiv using 1
    exact hder.symm
  have hL_branch : ∀ e ∈ Lset,
      HasDerivAt (fun s => Lval e * (iB s e) ^ 2 / 2) (v t e * iB t e) t := by
    intro e he
    have hdiff : HasDerivAt (fun s => iB s e) (deriv (fun s => iB s e) t) t :=
      (hLdiff e he).hasDerivAt
    have hmul := hdiff.fun_mul hdiff
    have hpow : HasDerivAt (fun s => (iB s e) ^ 2)
        (deriv (fun s => iB s e) t * iB t e + iB t e * deriv (fun s => iB s e) t) t := by
      simpa only [← pow_two] using hmul
    have hcmul := hpow.const_mul (Lval e)
    have hdiv := hcmul.div_const 2
    have hllaw := hLlaw e he
    have hder : Lval e * (deriv (fun s => iB s e) t * iB t e +
        iB t e * deriv (fun s => iB s e) t) / 2 = v t e * iB t e := by
      rw [hllaw]
      ring
    convert hdiv using 1
    exact hder.symm
  have hC_sum : HasDerivAt (fun s => ∑ e ∈ Cset, Cval e * (v s e) ^ 2 / 2)
      (∑ e ∈ Cset, v t e * iB t e) t :=
    HasDerivAt.fun_sum hC_branch
  have hL_sum : HasDerivAt (fun s => ∑ e ∈ Lset, Lval e * (iB s e) ^ 2 / 2)
      (∑ e ∈ Lset, v t e * iB t e) t :=
    HasDerivAt.fun_sum hL_branch
  have hadd := hC_sum.fun_add hL_sum
  simpa only [storedEnergy] using hadd

/-- **Network storage balance.** Under KVL, KCL, the branch
partition and the R/C/L branch laws, the derivative of stored energy
equals supplied node power minus source absorbed power minus
resistive loss:
`dE/dt = phi ⬝ᵥ j - sum_source (v_e * i_e) - sum_R R_e * (i_e)^2`. -/
lemma network_storage_deriv_eq_supplied_minus_losses (nN nB : ℕ)
    (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset)
    (Rval Lval Cval : Fin nB → ℝ)
    (hR : ∀ e ∈ Rset, 0 ≤ Rval e) (hL : ∀ e ∈ Lset, 0 < Lval e)
    (hC : ∀ e ∈ Cset, 0 < Cval e)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ) (t : ℝ)
    (hKVL : v t = Matrix.mulVec (Matrix.transpose B) (phi t))
    (hKCL : Matrix.mulVec B (iB t) = j t)
    (hRlaw : ∀ e ∈ Rset, v t e = Rval e * iB t e)
    (hClaw : ∀ e ∈ Cset, iB t e = Cval e * deriv (fun s => v s e) t)
    (hLlaw : ∀ e ∈ Lset, v t e = Lval e * deriv (fun s => iB s e) t)
    (hCdiff : ∀ e ∈ Cset, DifferentiableAt ℝ (fun s => v s e) t)
    (hLdiff : ∀ e ∈ Lset, DifferentiableAt ℝ (fun s => iB s e) t) :
    deriv (fun s => storedEnergy nB Cset Lset Cval Lval (v s) (iB s)) t =
      dotProduct (phi t) (j t) -
        sourceAbsorbedPower nB Sset (v t) (iB t) -
        resistiveLoss nB Rset Rval (iB t) := by
  have hE := hasDerivAt_storedEnergy nB Cset Lset Cval Lval v iB t
    hClaw hLlaw hCdiff hLdiff
  have hder := hE.deriv
  rw [hder]
  have hpower := branch_power_eq_node_power nN nB B (phi t) (j t) (v t) (iB t)
    hKVL hKCL
  have hsplit := total_branch_power_eq_sum_classes nB Rset Lset Cset Sset
    hpart (v t) (iB t)
  have hdot : dotProduct (v t) (iB t)
      = ∑ e : Fin nB, (v t) e * (iB t) e := rfl
  have hRsum : (∑ e ∈ Rset, (v t) e * (iB t) e)
      = resistiveLoss nB Rset Rval (iB t) := by
    unfold resistiveLoss
    apply Finset.sum_congr rfl
    intro e he
    rw [hRlaw e he]
    ring
  have hSsum : (∑ e ∈ Sset, (v t) e * (iB t) e)
      = sourceAbsorbedPower nB Sset (v t) (iB t) := rfl
  rw [hdot] at hpower
  have hcombine : dotProduct (phi t) (j t) =
      (∑ e ∈ Rset, (v t) e * (iB t) e) +
        (∑ e ∈ Lset, (v t) e * (iB t) e) +
        (∑ e ∈ Cset, (v t) e * (iB t) e) +
        (∑ e ∈ Sset, (v t) e * (iB t) e) := by
    rw [← hpower, hsplit]
  rw [hRsum, hSsum] at hcombine
  linarith

/-- **Finite-horizon energy inequality (FTC / nonnegative loss).**
If the circuit laws (KVL, KCL, and the resistor, capacitor and
inductor branch laws) hold at every `s ∈ [a, b]`, so that the
storage-balance identity is derived from the network model there
rather than assumed, with integrable supplied power, then
`E(b) - E(a) <= ∫ s in a..b, (phi ⬝ᵥ j - sum_source v_e * i_e)`. -/
lemma network_energy_sub_le_integral_supplied (nN nB : ℕ)
    (B : Matrix (Fin nN) (Fin nB) ℝ)
    (Rset Lset Cset Sset : Finset (Fin nB))
    (hpart : IsBranchPartition nB Rset Lset Cset Sset)
    (Rval Lval Cval : Fin nB → ℝ)
    (hR : ∀ e ∈ Rset, 0 ≤ Rval e) (hL : ∀ e ∈ Lset, 0 < Lval e)
    (hC : ∀ e ∈ Cset, 0 < Cval e)
    (phi j : ℝ → Fin nN → ℝ) (v iB : ℝ → Fin nB → ℝ)
    (a b : ℝ) (hab : a ≤ b)
    (hKVL : ∀ s ∈ Set.Icc a b,
      v s = Matrix.mulVec (Matrix.transpose B) (phi s))
    (hKCL : ∀ s ∈ Set.Icc a b, Matrix.mulVec B (iB s) = j s)
    (hRlaw : ∀ s ∈ Set.Icc a b, ∀ e ∈ Rset, v s e = Rval e * iB s e)
    (hClaw : ∀ s ∈ Set.Icc a b, ∀ e ∈ Cset,
      iB s e = Cval e * deriv (fun τ => v τ e) s)
    (hLlaw : ∀ s ∈ Set.Icc a b, ∀ e ∈ Lset,
      v s e = Lval e * deriv (fun τ => iB τ e) s)
    (hCdiff : ∀ s ∈ Set.Icc a b, ∀ e ∈ Cset,
      DifferentiableAt ℝ (fun τ => v τ e) s)
    (hLdiff : ∀ s ∈ Set.Icc a b, ∀ e ∈ Lset,
      DifferentiableAt ℝ (fun τ => iB τ e) s)
    (hsupplied_cont : ContinuousOn
      (fun s => dotProduct (phi s) (j s) -
        sourceAbsorbedPower nB Sset (v s) (iB s)) (Set.Icc a b))
    (hderiv_int : IntervalIntegrable
      (fun s => dotProduct (phi s) (j s) -
        sourceAbsorbedPower nB Sset (v s) (iB s) -
        resistiveLoss nB Rset Rval (iB s))
      MeasureTheory.volume a b) :
    storedEnergy nB Cset Lset Cval Lval (v b) (iB b) -
        storedEnergy nB Cset Lset Cval Lval (v a) (iB a) ≤
      ∫ s in a..b, (dotProduct (phi s) (j s) -
        sourceAbsorbedPower nB Sset (v s) (iB s)) := by
  have hderiv : ∀ s ∈ Set.Icc a b,
      HasDerivAt (fun τ => storedEnergy nB Cset Lset Cval Lval (v τ) (iB τ))
        (dotProduct (phi s) (j s) -
          sourceAbsorbedPower nB Sset (v s) (iB s) -
          resistiveLoss nB Rset Rval (iB s)) s := by
    intro s hs
    have hE := hasDerivAt_storedEnergy nB Cset Lset Cval Lval v iB s
      (hClaw s hs) (hLlaw s hs) (hCdiff s hs) (hLdiff s hs)
    have hval : (∑ e ∈ Cset, v s e * iB s e) + ∑ e ∈ Lset, v s e * iB s e =
        dotProduct (phi s) (j s) -
          sourceAbsorbedPower nB Sset (v s) (iB s) -
          resistiveLoss nB Rset Rval (iB s) := by
      have hbal := network_storage_deriv_eq_supplied_minus_losses nN nB B
        Rset Lset Cset Sset hpart Rval Lval Cval hR hL hC phi j v iB s
        (hKVL s hs) (hKCL s hs) (hRlaw s hs) (hClaw s hs) (hLlaw s hs)
        (hCdiff s hs) (hLdiff s hs)
      exact hE.deriv.symm.trans hbal
    rw [hval] at hE
    exact hE
  have hloss_nonneg : ∀ s ∈ Set.Icc a b,
      0 ≤ resistiveLoss nB Rset Rval (iB s) := by
    intro s hs
    unfold resistiveLoss
    apply Finset.sum_nonneg
    intro e he
    apply mul_nonneg (hR e he)
    exact sq_nonneg _
  have hderiv' : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun τ => storedEnergy nB Cset Lset Cval Lval (v τ) (iB τ))
        (dotProduct (phi x) (j x) -
          sourceAbsorbedPower nB Sset (v x) (iB x) -
          resistiveLoss nB Rset Rval (iB x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hderiv x hx
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hderiv_int
  have hsupplied_int : IntervalIntegrable
      (fun s => dotProduct (phi s) (j s) -
        sourceAbsorbedPower nB Sset (v s) (iB s))
      MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hsupplied_cont
  have hle : ∀ x ∈ Set.Icc a b,
      (dotProduct (phi x) (j x) -
        sourceAbsorbedPower nB Sset (v x) (iB x) -
        resistiveLoss nB Rset Rval (iB x)) ≤
      (dotProduct (phi x) (j x) -
        sourceAbsorbedPower nB Sset (v x) (iB x)) := by
    intro x hx
    exact sub_le_self _ (hloss_nonneg x hx)
  have hmono := intervalIntegral.integral_mono_on hab hderiv_int hsupplied_int hle
  rw [← hFTC]
  exact hmono

end PhyslibExt.Circuits.NetworkStorageBalance
