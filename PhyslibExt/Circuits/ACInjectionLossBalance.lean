/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedThreePhase
public import PhyslibExt.Circuits.PerUnitBases
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# AC injection and loss balance

## i. Overview

A finite alternating-current network is given by a real signed
incidence matrix between finitely many nodes and branches, a
complex root-mean-square node-voltage phasor at every node, a
complex admittance for every branch, and a complex shunt
admittance at every node. The voltage drop on a branch is the
signed sum of the node voltages at its ends, the branch current
is the branch admittance times that drop, and the current
injected at a node is the signed sum of the incident branch
currents plus the shunt current at that node.

Sign convention. The incidence coefficients that form a branch
drop also assemble the nodal current, so the injected current at
a node is the current leaving the node into its incident branches
and its shunt. The node voltage times the conjugate of that
current is therefore the complex power supplied by the node to the
branch and shunt network, which is the power the network absorbs
through that node in the convention of
`PhyslibExt.Circuits.BalancedThreePhase.complexPower`. For a
single unit-conductance branch from node `0` to node `1` with
voltages `1` and `0`, the supplied power at node `0` is `+1`: the
node supplies the power that the branch dissipates.

Phase convention. Every node carries one voltage phasor, so the
network is single-phase, or one phase of a balanced three-phase
network (its per-phase equivalent). The supplied power and every
balance below are therefore per-phase quantities. Driving the same
network with the balanced phase set of every node voltage rotates
each injection by the same phase factor, so the three phases supply
`3` times the per-phase power at every node, and the three-phase
balance is `3` times the per-phase balance
(`sum_nodeComplexPower_balancedPhases`,
`total_threePhase_realPower_eq_three_mul_losses`).

The total supplied real power over all nodes equals the sum over
branches of the real part of the branch admittance times the
squared magnitude of the branch drop, plus the sum over nodes of
the real part of the shunt admittance times the squared magnitude
of the node voltage, that is, the total real power absorbed by the
network. The same calculation gives the complex and reactive
forms. Nonnegativity of the total supplied real power is a
separate consequence that needs nonnegative real parts of all
admittances. No specified-power load-flow problem is solved:
voltages and currents obey a linear admittance relation, and
different voltage solutions or infeasible demanded powers are
neither constructed nor excluded.

The complex identity is proved by expanding the nodal power,
interchanging the finite sums over nodes and branches, and
collecting each branch drop against its conjugate to obtain a
`Complex.normSq` term; the shunt terms collect in the same way.
The real and reactive identities are the real and imaginary
parts of that complex identity, and the sign and validation
results are direct consequences of those forms. The per-unit
power on a direct real base is the existing
`PhyslibExt.Circuits.PerUnitBases.powerPerUnit` at phase bases
`1` and `Sbase / 3`, that is, the power divided by `Sbase`. The base
must be the base of the same quantity: the per-phase base `Vb * Ib`
for per-phase power, or the three-phase base
`PhyslibExt.Circuits.PerUnitBases.threePhasePowerBase` for
three-phase power. Both give the same per-unit value
(`perUnitComplexPower_three_mul_threePhasePowerBase`).

## ii. Key results

- `total_complexPower_eq_branch_add_shunt`: the total supplied
  complex power splits into branch and shunt parts.
- `total_realPower_eq_branch_add_shunt_losses`: the headline
  balance of total supplied real power against branch and shunt
  conductive losses.
- `total_threePhase_realPower_eq_three_mul_losses`: the balanced
  three-phase form, `3` times the per-phase balance.

## iii. Table of contents

- A. Network data and supplied power
- B. Total power balance
- C. Nodal injection equations
- D. Sign, reactive, and per-unit consequences
- E. Balanced three-phase operation

## iv. References

- J. J. Grainger and W. D. Stevenson, *Power System Analysis*,
  McGraw-Hill, 1994: nodal power injections, complex power
  balance, and per-unit quantities.

## A. Network data and supplied power
-/

@[expose] public section

open ComplexConjugate
open PhyslibExt.Circuits.BalancedThreePhase
open PhyslibExt.Circuits.PerUnitBases

namespace PhyslibExt.Circuits.ACInjectionLossBalance


/-- Branch voltage drop: the signed sum of node voltages through the real
incidence transpose, with each real incidence entry read as a complex
scalar. New definition owned by this module. -/
def branchDrop (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (e : Fin nE) : ℂ :=
  ∑ v : Fin nN, (B v e : ℂ) * V v

/-- Current injected at a node: the signed sum of incident branch currents
`admittance * drop` plus the shunt current `shunt * voltage`. New
definition owned by this module. -/
def nodeInjection (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (v : Fin nN) : ℂ :=
  (∑ e : Fin nE, (B v e : ℂ) * (y e * branchDrop nN nE B V e)) + ys v * V v

/-- Complex power supplied by a node to the branch and shunt network:
voltage times conjugated injection, in the canonical root-mean-square
convention. The injection is the current leaving the node into the
network, so this is the power the network absorbs through that node.
It is a per-phase quantity: in balanced three-phase operation the three
phases supply `3` times this value (`sum_nodeComplexPower_balancedPhases`).
New definition owned by this module. -/
def nodeComplexPower (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (v : Fin nN) : ℂ :=
  complexPower (V v) (nodeInjection nN nE B V y ys v)

/-- Complex power in per-unit on a direct real base power `Sbase`: the
existing `powerPerUnit` with phase voltage base `1` and phase current base
`Sbase / 3`, that is, `S / Sbase`. `Sbase` is the base of the same
quantity as `S`: a per-phase base for per-phase power such as
`nodeComplexPower`, a three-phase base for three-phase power. Dividing by
a positive real base scales the real and reactive parts by the same
positive factor and does not rotate them. -/
noncomputable def perUnitComplexPower (S : ℂ) (Sbase : ℝ) : ℂ :=
  powerPerUnit 1 (Sbase / 3) S

private theorem re_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t hmem ih
    rw [Finset.sum_insert hmem, Finset.sum_insert hmem, Complex.add_re, ih]

private theorem im_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t hmem ih
    rw [Finset.sum_insert hmem, Finset.sum_insert hmem, Complex.add_im, ih]

private theorem conj_mul_ofReal_re (z : ℂ) (r : ℝ) :
    (conj z * ((r : ℝ) : ℂ)).re = z.re * r := by
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

private theorem conj_mul_ofReal_im (z : ℂ) (r : ℝ) :
    (conj z * ((r : ℝ) : ℂ)).im = -(z.im * r) := by
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

private theorem mul_conj_factor (a b : ℂ) :
    a * (conj b * conj a) = conj b * ((Complex.normSq a : ℝ) : ℂ) := by
  have h := Complex.mul_conj a
  calc a * (conj b * conj a) = conj b * (a * conj a) := by ring
    _ = conj b * ((Complex.normSq a : ℝ) : ℂ) := by rw [h]

private theorem conj_mul_normSq (u : ℂ) :
    conj u * u = ((Complex.normSq u : ℝ) : ℂ) := by
  rw [mul_comm]
  exact Complex.mul_conj u

/-! ## B. Total power balance -/

/-- Total supplied complex power splits into a branch part and a shunt
part: each branch contributes conjugated admittance times squared drop
magnitude, and each node contributes conjugated shunt admittance times
squared voltage magnitude. -/
theorem total_complexPower_eq_branch_add_shunt (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) :
    (∑ v : Fin nN, nodeComplexPower nN nE B V y ys v) =
      (∑ e : Fin nE, conj (y e) * (Complex.normSq (branchDrop nN nE B V e) : ℂ)) +
        ∑ v : Fin nN, conj (ys v) * (Complex.normSq (V v) : ℂ) := by
  unfold nodeComplexPower complexPower nodeInjection
  simp only [map_add, map_sum, map_mul, Complex.conj_ofReal, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hconj : conj (branchDrop nN nE B V e) * branchDrop nN nE B V e
        = ((Complex.normSq (branchDrop nN nE B V e) : ℝ) : ℂ) :=
      conj_mul_normSq _
    have hfactor : (∑ v : Fin nN, V v * (↑(B v e) *
          (conj (y e) * conj (branchDrop nN nE B V e)))) =
        conj (y e) * conj (branchDrop nN nE B V e) *
          (∑ v : Fin nN, ↑(B v e) * V v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => by ring)
    rw [hfactor]
    have hdrop : (∑ v : Fin nN, ((B v e : ℝ) : ℂ) * V v)
        = branchDrop nN nE B V e := rfl
    rw [hdrop, mul_assoc, hconj]
  · refine Finset.sum_congr rfl (fun v _ => mul_conj_factor _ _)

/-- Headline balance: total supplied real power equals total branch
conductive loss plus total shunt conductive loss, with squared magnitudes
in the form of squared complex norms. No sign hypothesis on any admittance
is needed for this identity. -/
theorem total_realPower_eq_branch_add_shunt_losses (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) :
    (∑ v : Fin nN, (nodeComplexPower nN nE B V y ys v).re) =
      (∑ e : Fin nE, (y e).re * Complex.normSq (branchDrop nN nE B V e)) +
        ∑ v : Fin nN, (ys v).re * Complex.normSq (V v) := by
  have h := total_complexPower_eq_branch_add_shunt nN nE B V y ys
  have h2 := congrArg Complex.re h
  simp only [re_sum, Complex.add_re] at h2
  simp only [conj_mul_ofReal_re] at h2
  exact h2

/-- Total supplied reactive power equals minus the branch susceptive part
minus the shunt susceptive part: conjugation flips the sign of every
imaginary admittance part. -/
lemma total_reactivePower_eq_neg_susceptive (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) :
    (∑ v : Fin nN, (nodeComplexPower nN nE B V y ys v).im) =
      -(∑ e : Fin nE, (y e).im * Complex.normSq (branchDrop nN nE B V e)) -
        ∑ v : Fin nN, (ys v).im * Complex.normSq (V v) := by
  have h := total_complexPower_eq_branch_add_shunt nN nE B V y ys
  have h2 := congrArg Complex.im h
  simp only [im_sum, Complex.add_im] at h2
  simp only [conj_mul_ofReal_im] at h2
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at h2
  rw [sub_eq_add_neg]
  exact h2

/-! ## C. Nodal injection equations -/

/-- Real injection equation at one node: the real supplied power is the
real part of voltage times conjugated branch injection, plus the shunt
conductance times squared voltage magnitude. -/
lemma node_realPower_eq_branch_add_shunt (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) (v : Fin nN) :
    (nodeComplexPower nN nE B V y ys v).re =
      (V v * conj (∑ e : Fin nE,
        (B v e : ℂ) * (y e * branchDrop nN nE B V e))).re +
        (ys v).re * Complex.normSq (V v) := by
  unfold nodeComplexPower complexPower nodeInjection
  rw [map_add, mul_add, Complex.add_re]
  congr 1
  rw [map_mul, mul_conj_factor]
  exact conj_mul_ofReal_re _ _

/-- Reactive injection equation at one node: the imaginary supplied power
is the imaginary part of voltage times conjugated branch injection, minus
the shunt susceptance times squared voltage magnitude. -/
lemma node_reactivePower_eq_branch_sub_shunt (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) (v : Fin nN) :
    (nodeComplexPower nN nE B V y ys v).im =
      (V v * conj (∑ e : Fin nE,
        (B v e : ℂ) * (y e * branchDrop nN nE B V e))).im -
        (ys v).im * Complex.normSq (V v) := by
  unfold nodeComplexPower complexPower nodeInjection
  rw [map_add, mul_add, Complex.add_im, sub_eq_add_neg]
  congr 1
  rw [map_mul, mul_conj_factor]
  exact conj_mul_ofReal_im _ _

/-! ## D. Sign, reactive, and per-unit consequences -/

/-- With nonnegative conductance in every branch and shunt, the total
supplied real power is nonnegative. This sign conclusion is separate from
the balance identity above. -/
lemma total_realPower_nonneg (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ)
    (hy : ∀ e : Fin nE, 0 ≤ (y e).re) (hys : ∀ v : Fin nN, 0 ≤ (ys v).re) :
    0 ≤ ∑ v : Fin nN, (nodeComplexPower nN nE B V y ys v).re := by
  rw [total_realPower_eq_branch_add_shunt_losses]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (hy e) (Complex.normSq_nonneg _)
  · apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (hys v) (Complex.normSq_nonneg _)

/-- Purely reactive validation case: if every branch and shunt admittance
has zero real part, the total supplied real power is zero, for resistive
losses at the endpoints and the branches agree on zero. -/
lemma total_realPower_eq_zero_of_purely_reactive (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) (hy : ∀ e : Fin nE, (y e).re = 0)
    (hys : ∀ v : Fin nN, (ys v).re = 0) :
    (∑ v : Fin nN, (nodeComplexPower nN nE B V y ys v).re) = 0 := by
  rw [total_realPower_eq_branch_add_shunt_losses]
  have hb : (∑ e : Fin nE,
      (y e).re * Complex.normSq (branchDrop nN nE B V e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [hy e, zero_mul]
  have hs : (∑ v : Fin nN, (ys v).re * Complex.normSq (V v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rw [hys v, zero_mul]
  rw [hb, hs, add_zero]

/-- Recovery from per-unit on a positive real base: multiplying the per-unit
value by the base, read as a complex number, returns the original complex
power. Positivity gives the nonzero side condition the division needs. -/
lemma perUnitComplexPower_mul_base_eq (S : ℂ) (Sbase : ℝ) (hbase : 0 < Sbase) :
    perUnitComplexPower S Sbase * (Sbase : ℂ) = S := by
  have hbase' : (Sbase : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hbase
  have hb : threePhasePowerBase 1 (Sbase / 3) = Sbase := by
    unfold threePhasePowerBase
    ring
  unfold perUnitComplexPower powerPerUnit
  rw [hb]
  exact div_mul_cancel₀ S hbase'

/-- The direct-base per-unit power is the existing `powerPerUnit` on every
three-phase power base, so both views give the same per-unit value. -/
lemma perUnitComplexPower_threePhasePowerBase (S : ℂ) (Vb Ib : ℝ) :
    perUnitComplexPower S (threePhasePowerBase Vb Ib) = powerPerUnit Vb Ib S := by
  have hb : threePhasePowerBase 1 (threePhasePowerBase Vb Ib / 3) =
      threePhasePowerBase Vb Ib := by
    unfold threePhasePowerBase
    ring
  unfold perUnitComplexPower powerPerUnit
  rw [hb]

/-- Three-phase power on the three-phase base and per-phase power on the
per-phase base `Vb * Ib` have the same per-unit value. -/
lemma perUnitComplexPower_three_mul_threePhasePowerBase (S : ℂ) (Vb Ib : ℝ) :
    perUnitComplexPower (3 * S) (threePhasePowerBase Vb Ib) =
      perUnitComplexPower S (Vb * Ib) := by
  unfold perUnitComplexPower powerPerUnit threePhasePowerBase
  push_cast
  ring

/-! ## E. Balanced three-phase operation -/

private theorem branchDrop_const_mul (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (c : ℂ) (e : Fin nE) :
    branchDrop nN nE B (fun w => c * V w) e = c * branchDrop nN nE B V e := by
  unfold branchDrop
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun v _ => by ring)

private theorem nodeInjection_const_mul (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (c : ℂ) (v : Fin nN) :
    nodeInjection nN nE B (fun w => c * V w) y ys v =
      c * nodeInjection nN nE B V y ys v := by
  unfold nodeInjection
  simp only [branchDrop_const_mul, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun e _ => by ring)
  · ring

private theorem balancedPhases_eq_mul (X : ℂ) (p : ZMod 3) :
    balancedPhases X p = balancedPhases 1 p * X := by
  fin_cases p <;> simp [balancedPhases]

/-- Balanced three-phase operation at one node: driving the network with
the balanced phase set of every node voltage, the three phases together
supply `3` times the per-phase power `nodeComplexPower`. -/
theorem sum_nodeComplexPower_balancedPhases (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) (v : Fin nN) :
    (∑ p : ZMod 3, nodeComplexPower nN nE B (fun w => balancedPhases (V w) p) y ys v) =
      3 * nodeComplexPower nN nE B V y ys v := by
  have h : ∀ p : ZMod 3,
      nodeComplexPower nN nE B (fun w => balancedPhases (V w) p) y ys v =
        complexPower (balancedPhases (V v) p)
          (balancedPhases (nodeInjection nN nE B V y ys v) p) := by
    intro p
    have hV : (fun w => balancedPhases (V w) p) = fun w => balancedPhases 1 p * V w :=
      funext fun w => balancedPhases_eq_mul (V w) p
    unfold nodeComplexPower
    rw [hV, nodeInjection_const_mul, balancedPhases_eq_mul (V v),
      balancedPhases_eq_mul (nodeInjection nN nE B V y ys v)]
  rw [Finset.sum_congr rfl (fun p _ => h p), sum_complexPower_balancedPhases]
  rfl

/-- Balanced three-phase real power balance: the real power the three
phases supply over all nodes is `3` times the per-phase branch and shunt
conductive losses. -/
theorem total_threePhase_realPower_eq_three_mul_losses (nN nE : ℕ)
    (B : Matrix (Fin nN) (Fin nE) ℝ) (V : Fin nN → ℂ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) :
    (∑ v : Fin nN,
        (∑ p : ZMod 3,
          nodeComplexPower nN nE B (fun w => balancedPhases (V w) p) y ys v).re) =
      3 * ((∑ e : Fin nE, (y e).re * Complex.normSq (branchDrop nN nE B V e)) +
        ∑ v : Fin nN, (ys v).re * Complex.normSq (V v)) := by
  simp only [sum_nodeComplexPower_balancedPhases]
  rw [← total_realPower_eq_branch_add_shunt_losses, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp [Complex.mul_re]

end PhyslibExt.Circuits.ACInjectionLossBalance
