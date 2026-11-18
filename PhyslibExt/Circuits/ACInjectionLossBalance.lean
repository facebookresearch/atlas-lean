/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.BalancedThreePhase
public import PhyslibExt.Circuits.PhasorElementLaws
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

With the absorbed complex power at a node defined as the node
voltage times the conjugate of its injected current, in the
convention of `PhyslibExt.Circuits.BalancedThreePhase.complexPower`
and the phasor element laws of
`PhyslibExt.Circuits.PhasorElementLaws`, the total absorbed real
power over all nodes equals the sum over branches of the real
part of the branch admittance times the squared magnitude of
the branch drop, plus the sum over nodes of the real part of
the shunt admittance times the squared magnitude of the node
voltage. The same calculation gives the complex and reactive
forms. Nonnegativity of the total real power is a separate
consequence that needs nonnegative real parts of all
admittances. No specified-power load-flow problem is solved:
voltages and currents obey a linear admittance relation, and
different voltage solutions or infeasible demanded powers are
neither constructed nor excluded.

The complex identity is proved by expanding the nodal power,
interchanging the finite sums over nodes and branches, and
collecting each branch drop against its conjugate to obtain a
`Complex.normSq` term; the shunt terms collect in the same way.
The real and reactive identities are the real and imaginary
parts of that complex identity, and the remaining results are
direct consequences of those forms or of the per-unit
definition.

## ii. Key results

- `total_complexPower_eq_branch_add_shunt`: the total absorbed
  complex power splits into branch and shunt parts.
- `total_realPower_eq_branch_add_shunt_losses`: the headline
  balance of total absorbed real power against branch and shunt
  conductive losses.

## iii. Table of contents

- A. Network data and absorbed power
- B. Total power balance
- C. Nodal injection equations
- D. Sign, reactive, and per-unit consequences

## iv. References

- J. J. Grainger and W. D. Stevenson, *Power System Analysis*,
  McGraw-Hill, 1994: nodal power injections, complex power
  balance, and per-unit quantities.

## A. Network data and absorbed power
-/

@[expose] public section

open ComplexConjugate
open PhyslibExt.Circuits.BalancedThreePhase

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

/-- Absorbed complex power at a node, voltage times conjugated injection,
in the canonical root-mean-square convention. New definition owned by this
module. -/
def nodeComplexPower (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (v : Fin nN) : ℂ :=
  complexPower (V v) (nodeInjection nN nE B V y ys v)

/-- Complex power in per-unit on a positive real base power: dividing by a
positive real base scales the real and reactive parts by the same positive
factor and does not rotate them. -/
noncomputable def perUnitComplexPower (S : ℂ) (Sbase : ℝ) : ℂ :=
  S / (Sbase : ℂ)

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

/-- Total absorbed complex power splits into a branch part and a shunt
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

/-- Headline balance: total absorbed real power equals total branch
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

/-- Total absorbed reactive power equals minus the branch susceptive part
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

/-- Real injection equation at one node: the real absorbed power is the
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

/-- Reactive injection equation at one node: the imaginary absorbed power
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
absorbed real power is nonnegative. This sign conclusion is separate from
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
has zero real part, the total absorbed real power is zero, for resistive
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
  unfold perUnitComplexPower
  have hbase' : (Sbase : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hbase
  exact div_mul_cancel₀ S hbase'

end PhyslibExt.Circuits.ACInjectionLossBalance
