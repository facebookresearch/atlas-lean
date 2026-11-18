/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import PhyslibExt.Circuits.ACInjectionLossBalance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Lossless DC load-flow model and its per-line angle error

## i. Overview

A finite network has nodes `Fin nN` and labeled oriented branches
`Fin nE` with tail and head maps, real branch susceptances `b e`, and
real node phase angles `θ`. The electrical incidence `B` is
tail-positive: `B v e = 1` at the tail, `-1` at the head, the negation
of the head-positive arc incidence
`MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix`. The
lossless DC model is the branch flow `f = diag(b) * Bᵀ * θ`, so
`f e = b e * (θ tail - θ head)`, and the nodal injection `p = B * f`,
which equals `L_b * θ` for the full weighted Laplacian
`L_b = B * diag(b) * Bᵀ`. The injections sum to zero, and a uniform
angle shift changes no flow.

The nonlinear comparison is the lossless unit-magnitude AC model built
on the network of `PhyslibExt.Circuits.ACInjectionLossBalance`: node
voltages `V v = exp(i * θ v)`, branch admittances `y e = -i * b e`,
branch currents `I e = y e * (V tail - V head)` through the canonical
branch drop, and sending-end real power
`P e = Re(V tail * conj (I e)) = b e * sin(θ tail - θ head)`, with the
complex power of `PhyslibExt.Circuits.BalancedThreePhase.complexPower`.
The cubic sine bound `|x - sin x| ≤ |x| ^ 3 / 6` then gives
`|P e - f e| ≤ b e * |θ tail - θ head| ^ 3 / 6` for positive
susceptances, and the nodal AC real power of the canonical injection
differs from `p` by at most the incidence-weighted sum of these
bounds. A phase reference `θ v = 0` gives `V v = 1`, not a zero
voltage.

The comparison is between the two formulas at the same angles, not
between two solved operating points: no grounded solve, feasibility,
small-angle, or relative-error claim is made. Nonunit magnitudes and
resistive admittances leave the model; validation lemmas record the
resulting real-power formulas, which the DC flow does not represent.

## ii. Key results

- `model_correct`: the DC flow formula, `p = L_b * θ`, the AC
  real-power formula `b e * sin(θ tail - θ head)`, and the cubic
  per-line bound, together.
- `abs_acBranchRealPower_sub_dcBranchFlow_le`: the per-line angle
  error bound.
- `abs_nodeRealPower_sub_dcInjection_le`: the nodal angle error bound.

## iii. Table of contents

- A. The lossless DC model
- B. The lossless unit-magnitude AC comparison model
- C. Incidence, drop, and injection identities
- D. The AC comparison
- E. Validation: reversed lines and out-of-model admittances
- F. Headline

## iv. References

- B. Stott, J. Jardim, and O. Alsaç, "DC Power Flow Revisited,"
  *IEEE Transactions on Power Systems* 24(3), 2009, 1290-1300: the
  lossless DC model, its susceptance-weighted Laplacian, and its
  angle approximation error.
- J. J. Grainger and W. D. Stevenson, *Power System Analysis*,
  McGraw-Hill, 1994: nodal power injections and the DC load flow.

## A. The lossless DC model
-/

@[expose] public section

open ComplexConjugate

namespace PhyslibExt.Circuits.LosslessDCFlowModel

open PhyslibExt.Circuits.BalancedThreePhase
open PhyslibExt.Circuits.ACInjectionLossBalance

/-- Electrical tail-positive incidence: `1` at the tail of a branch, `-1`
at its head, the negation of the canonical head-positive arc incidence.
Loop columns vanish. -/
noncomputable def electricalIncidence (nN nE : ℕ) (tail head : Fin nE → Fin nN) :
    Matrix (Fin nN) (Fin nE) ℝ :=
  -MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head

/-- DC branch flow `f = diag(b) * Bᵀ * θ` for branch susceptances `b` and
node phase angles `θ`. -/
noncomputable def dcBranchFlow (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) : Fin nE → ℝ :=
  Matrix.mulVec
    (Matrix.diagonal b * Matrix.transpose (electricalIncidence nN nE tail head)) θ

/-- DC nodal injection `p = B * f`. -/
noncomputable def dcInjection (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) : Fin nN → ℝ :=
  Matrix.mulVec (electricalIncidence nN nE tail head) (dcBranchFlow nN nE tail head b θ)

/-- Full susceptance-weighted Laplacian `L_b = B * diag(b) * Bᵀ`, with no
reference row or column deleted. -/
noncomputable def weightedLaplacian (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) : Matrix (Fin nN) (Fin nN) ℝ :=
  electricalIncidence nN nE tail head * Matrix.diagonal b *
    Matrix.transpose (electricalIncidence nN nE tail head)

/-! ## B. The lossless unit-magnitude AC comparison model -/

/-- Unit-magnitude node voltage phasor `V v = exp(i * θ v)`. -/
noncomputable def unitVoltage (nN : ℕ) (θ : Fin nN → ℝ) (v : Fin nN) : ℂ :=
  Complex.exp ((θ v : ℂ) * Complex.I)

/-- Lossless branch admittance `y e = -i * b e`: a pure series susceptance
with no conductance. -/
def losslessAdmittance (nE : ℕ) (b : Fin nE → ℝ) (e : Fin nE) : ℂ :=
  -Complex.I * (b e : ℂ)

/-- Branch current `admittance * drop`, the summand of the canonical nodal
injection. -/
def branchCurrent (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (e : Fin nE) : ℂ :=
  y e * branchDrop nN nE B V e

/-- Sending-end real power `Re(V tail * conj (I e))` of a branch in the
lossless unit-magnitude AC model. -/
noncomputable def acBranchRealPower (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) : ℝ :=
  (complexPower (unitVoltage nN θ (tail e))
    (branchCurrent nN nE (electricalIncidence nN nE tail head) (unitVoltage nN θ)
      (losslessAdmittance nE b) e)).re

private lemma sum_incidence_indicator (nN : ℕ) (V : Fin nN → ℂ) (a : Fin nN) :
    (∑ v : Fin nN, ((if a = v then (1 : ℝ) else 0 : ℝ) : ℂ) * V v) = V a := by
  have hconv : ∀ v : Fin nN, (((if a = v then (1 : ℝ) else 0 : ℝ) : ℂ) * V v) =
      (if a = v then V v else 0) := by
    intro v
    by_cases h : a = v <;> simp [h]
  simp only [hconv]
  simp

private lemma sum_incidence_indicator_real (nN : ℕ) (θ : Fin nN → ℝ) (a : Fin nN) :
    (∑ v : Fin nN, (if a = v then (1 : ℝ) else 0) * θ v) = θ a := by
  have hconv : ∀ v : Fin nN, ((if a = v then (1 : ℝ) else 0) * θ v) =
      (if a = v then θ v else 0) := by
    intro v
    by_cases h : a = v <;> simp [h]
  simp only [hconv]
  simp

private lemma sum_indicator_eq_one (nN : ℕ) (a : Fin nN) :
    (∑ v : Fin nN, (if a = v then (1 : ℝ) else 0)) = 1 := by
  simp

private lemma ofReal_mul_re (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-! ## C. Incidence, drop, and injection identities -/

/-- Entry formula of the electrical incidence. -/
lemma electricalIncidence_apply (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (v : Fin nN) (e : Fin nE) :
    electricalIncidence nN nE tail head v e =
      (if tail e = v then (1 : ℝ) else 0) - (if head e = v then 1 else 0) := by
  change -(((if head e = v then (1 : ℝ) else 0) - (if tail e = v then 1 else 0))) = _
  ring

private lemma sum_electricalIncidence_column (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (e : Fin nE) : (∑ v : Fin nN, electricalIncidence nN nE tail head v e) = 0 := by
  simp only [electricalIncidence_apply, Finset.sum_sub_distrib, sum_indicator_eq_one,
    sub_self]

/-- The canonical branch drop through the electrical incidence is the
tail voltage minus the head voltage, loops included. -/
lemma branchDrop_electricalIncidence (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (V : Fin nN → ℂ) (e : Fin nE) :
    branchDrop nN nE (electricalIncidence nN nE tail head) V e = V (tail e) - V (head e) := by
  simp only [branchDrop, electricalIncidence_apply, Complex.ofReal_sub, sub_mul,
    Finset.sum_sub_distrib, sum_incidence_indicator]

/-- The canonical nodal injection is the signed sum of branch currents plus
the shunt current. -/
lemma nodeInjection_eq_sum_branchCurrent (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (v : Fin nN) :
    nodeInjection nN nE B V y ys v =
      (∑ e : Fin nE, (B v e : ℂ) * branchCurrent nN nE B V y e) + ys v * V v := by
  simp only [nodeInjection, branchCurrent]

/-- DC branch flow formula `f e = b e * (θ tail - θ head)`. -/
lemma dcBranchFlow_apply (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) :
    dcBranchFlow nN nE tail head b θ e = b e * (θ (tail e) - θ (head e)) := by
  have hrow : ∀ v : Fin nN,
      (Matrix.diagonal b * Matrix.transpose (electricalIncidence nN nE tail head)) e v =
        b e * electricalIncidence nN nE tail head v e := by
    intro v
    rw [Matrix.diagonal_mul, Matrix.transpose_apply]
  simp only [dcBranchFlow, Matrix.mulVec, dotProduct, hrow, mul_assoc,
    ← Finset.mul_sum]
  congr 1
  simp only [electricalIncidence_apply, sub_mul, Finset.sum_sub_distrib,
    sum_incidence_indicator_real]

/-- DC injection is the full weighted Laplacian applied to the angles,
`p = B * f = L_b * θ`. -/
lemma dcInjection_eq_weightedLaplacian_mulVec (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    dcInjection nN nE tail head b θ =
      Matrix.mulVec (weightedLaplacian nN nE tail head b) θ := by
  simp only [dcInjection, dcBranchFlow, weightedLaplacian, ← Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- DC injections are balanced: they sum to zero over all nodes, which is
the full reference equation a grounded solve must respect. -/
lemma sum_dcInjection_eq_zero (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    ∑ v : Fin nN, dcInjection nN nE tail head b θ v = 0 := by
  simp only [dcInjection, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_electricalIncidence_column, zero_mul,
    Finset.sum_const_zero]

/-- A uniform angle shift changes no DC flow: the full weighted Laplacian
kills constant angle vectors. -/
lemma weightedLaplacian_mulVec_const (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (c : ℝ) :
    Matrix.mulVec (weightedLaplacian nN nE tail head b) (fun _ => c) = 0 := by
  have htrans : Matrix.mulVec (Matrix.transpose (electricalIncidence nN nE tail head))
      (fun _ => c) = 0 := by
    funext e
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
    rw [← Finset.sum_mul, sum_electricalIncidence_column, zero_mul]
  simp only [weightedLaplacian, ← Matrix.mulVec_mulVec, htrans, Matrix.mulVec_zero]

/-! ## D. The AC comparison -/

/-- Unit-magnitude voltages have norm one. -/
lemma norm_unitVoltage (nN : ℕ) (θ : Fin nN → ℝ) (v : Fin nN) :
    ‖unitVoltage nN θ v‖ = 1 := by
  simp [unitVoltage]

/-- A phase reference `θ v = 0` gives the unit voltage `1`, not a zero AC
voltage. -/
lemma unitVoltage_eq_one_of_angle_eq_zero (nN : ℕ) (θ : Fin nN → ℝ) (v : Fin nN)
    (hθ : θ v = 0) :
    unitVoltage nN θ v = 1 := by
  simp only [unitVoltage, hθ, Complex.ofReal_zero, zero_mul, Complex.exp_zero]

/-- Sending-end real power of a lossless unit-magnitude branch:
`P e = b e * sin(θ tail - θ head)`. -/
lemma acBranchRealPower_eq_mul_sin (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) :
    acBranchRealPower nN nE tail head b θ e =
      b e * Real.sin (θ (tail e) - θ (head e)) := by
  simp only [acBranchRealPower, branchCurrent, branchDrop_electricalIncidence,
    losslessAdmittance, unitVoltage, complexPower, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [Real.sin_sub]
  ring

/-- The branch is lossless: real power at the receiving end equals real
power at the sending end. -/
lemma receivingRealPower_eq_acBranchRealPower (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) :
    (complexPower (unitVoltage nN θ (head e))
      (branchCurrent nN nE (electricalIncidence nN nE tail head) (unitVoltage nN θ)
        (losslessAdmittance nE b) e)).re =
      acBranchRealPower nN nE tail head b θ e := by
  rw [acBranchRealPower_eq_mul_sin]
  simp only [branchCurrent, branchDrop_electricalIncidence, losslessAdmittance, unitVoltage,
    complexPower, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [Real.sin_sub]
  ring

/-- AC nodal real power of the canonical nodal injection with lossless
branches and no shunts is the signed sum of branch sine flows, the
nonlinear counterpart of `p = B * f`. -/
lemma nodeRealPower_eq_sum_mul_sin (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (v : Fin nN) :
    (nodeComplexPower nN nE (electricalIncidence nN nE tail head) (unitVoltage nN θ)
      (losslessAdmittance nE b) (fun _ => 0) v).re =
      ∑ e : Fin nE, electricalIncidence nN nE tail head v e *
        (b e * Real.sin (θ (tail e) - θ (head e))) := by
  have hbranch : ∀ e : Fin nE, electricalIncidence nN nE tail head v e *
        ((unitVoltage nN θ v) * conj (branchCurrent nN nE
          (electricalIncidence nN nE tail head) (unitVoltage nN θ)
          (losslessAdmittance nE b) e)).re =
        electricalIncidence nN nE tail head v e *
          (b e * Real.sin (θ (tail e) - θ (head e))) := by
    intro e
    by_cases ht : tail e = v
    · by_cases hh : head e = v
      · have hB : electricalIncidence nN nE tail head v e = 0 := by
          simp [electricalIncidence_apply, ht, hh]
        simp [hB]
      · have hP : ((unitVoltage nN θ v) * conj (branchCurrent nN nE
            (electricalIncidence nN nE tail head) (unitVoltage nN θ)
            (losslessAdmittance nE b) e)).re =
            acBranchRealPower nN nE tail head b θ e := by
          simp only [← ht, acBranchRealPower, complexPower]
        rw [hP, acBranchRealPower_eq_mul_sin]
    · by_cases hh : head e = v
      · have hP : ((unitVoltage nN θ v) * conj (branchCurrent nN nE
            (electricalIncidence nN nE tail head) (unitVoltage nN θ)
            (losslessAdmittance nE b) e)).re =
            acBranchRealPower nN nE tail head b θ e := by
          rw [← hh]
          exact receivingRealPower_eq_acBranchRealPower nN nE tail head b θ e
        rw [hP, acBranchRealPower_eq_mul_sin]
      · have hB : electricalIncidence nN nE tail head v e = 0 := by
          simp [electricalIncidence_apply, ht, hh]
        simp [hB]
  simp only [nodeComplexPower, complexPower, nodeInjection_eq_sum_branchCurrent, zero_mul,
    add_zero, map_sum, map_mul, Complex.conj_ofReal]
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_left_comm, ofReal_mul_re]
  exact hbranch e

/-- Total AC real power of the lossless network is zero. -/
lemma sum_nodeRealPower_eq_zero (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    ∑ v : Fin nN, (nodeComplexPower nN nE (electricalIncidence nN nE tail head)
      (unitVoltage nN θ) (losslessAdmittance nE b) (fun _ => 0) v).re = 0 :=
  total_realPower_eq_zero_of_purely_reactive nN nE _ _ _ _
    (fun _ => by simp [losslessAdmittance]) (fun _ => Complex.zero_re)

/-- Per-line angle error: the sending-end AC real power and the DC flow
differ by at most `b e * |θ tail - θ head| ^ 3 / 6`. -/
theorem abs_acBranchRealPower_sub_dcBranchFlow_le (nN nE : ℕ)
    (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ) (hb : ∀ e, 0 < b e)
    (θ : Fin nN → ℝ) (e : Fin nE) :
    |acBranchRealPower nN nE tail head b θ e - dcBranchFlow nN nE tail head b θ e| ≤
      b e * |θ (tail e) - θ (head e)| ^ 3 / 6 := by
  have hbe : 0 < b e := hb e
  rw [acBranchRealPower_eq_mul_sin, dcBranchFlow_apply]
  have hfactor : b e * Real.sin (θ (tail e) - θ (head e)) - b e * (θ (tail e) - θ (head e)) =
      b e * (Real.sin (θ (tail e) - θ (head e)) - (θ (tail e) - θ (head e))) := by
    ring
  rw [hfactor, abs_mul, abs_of_pos hbe]
  have hsin : |Real.sin (θ (tail e) - θ (head e)) - (θ (tail e) - θ (head e))| ≤
      |θ (tail e) - θ (head e)| ^ 3 / 6 := by
    have h := Real.abs_sub_sin_le (θ (tail e) - θ (head e))
    rw [abs_sub_comm (θ (tail e) - θ (head e)) (Real.sin (θ (tail e) - θ (head e)))] at h
    exact h
  calc b e * |Real.sin (θ (tail e) - θ (head e)) - (θ (tail e) - θ (head e))|
        ≤ b e * (|θ (tail e) - θ (head e)| ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left hsin (le_of_lt hbe)
    _ = b e * |θ (tail e) - θ (head e)| ^ 3 / 6 := by ring

/-- Nodal angle error: AC nodal real power and DC injection differ by at
most the incidence-weighted sum of per-line bounds. -/
theorem abs_nodeRealPower_sub_dcInjection_le (nN nE : ℕ)
    (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ) (hb : ∀ e, 0 < b e)
    (θ : Fin nN → ℝ) (v : Fin nN) :
    |(nodeComplexPower nN nE (electricalIncidence nN nE tail head) (unitVoltage nN θ)
        (losslessAdmittance nE b) (fun _ => 0) v).re -
        dcInjection nN nE tail head b θ v| ≤
      ∑ e : Fin nE, |electricalIncidence nN nE tail head v e| *
        (b e * |θ (tail e) - θ (head e)| ^ 3 / 6) := by
  have hdc : dcInjection nN nE tail head b θ v =
      ∑ e : Fin nE, electricalIncidence nN nE tail head v e *
        dcBranchFlow nN nE tail head b θ e := by
    simp only [dcInjection, Matrix.mulVec, dotProduct]
  rw [nodeRealPower_eq_sum_mul_sin, hdc, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) ?_
  refine Finset.sum_le_sum fun e _ => ?_
  have hP := acBranchRealPower_eq_mul_sin nN nE tail head b θ e
  have hf := dcBranchFlow_apply nN nE tail head b θ e
  have hbound := abs_acBranchRealPower_sub_dcBranchFlow_le nN nE tail head b hb θ e
  rw [hP, hf] at hbound
  have hfactor : electricalIncidence nN nE tail head v e *
        (b e * Real.sin (θ (tail e) - θ (head e))) -
        electricalIncidence nN nE tail head v e * dcBranchFlow nN nE tail head b θ e =
        electricalIncidence nN nE tail head v e *
          (b e * Real.sin (θ (tail e) - θ (head e)) - b e * (θ (tail e) - θ (head e))) := by
    rw [hf]
    ring
  rw [hfactor, abs_mul]
  exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

/-! ## E. Validation: reversed lines and out-of-model admittances -/

/-- Reversing every branch orientation negates every DC flow. -/
lemma dcBranchFlow_reverse (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) :
    dcBranchFlow nN nE head tail b θ e = -dcBranchFlow nN nE tail head b θ e := by
  simp only [dcBranchFlow_apply]
  ring

/-- Reversing every branch orientation negates every sending-end AC real
power. -/
lemma acBranchRealPower_reverse (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) :
    acBranchRealPower nN nE head tail b θ e = -acBranchRealPower nN nE tail head b θ e := by
  simp only [acBranchRealPower_eq_mul_sin]
  have h : θ (head e) - θ (tail e) = -(θ (tail e) - θ (head e)) := by ring
  rw [h, Real.sin_neg]
  ring

/-- Out of model, nonunit magnitudes: for `V v = m v * exp(i * θ v)` and a
lossless branch, the sending-end real power carries the factor
`m tail * m head`, so the cubic bound does not transfer. -/
lemma realPower_scaledVoltage (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (m θ : Fin nN → ℝ) (e : Fin nE) :
    (complexPower ((m (tail e) : ℂ) * unitVoltage nN θ (tail e))
      (branchCurrent nN nE (electricalIncidence nN nE tail head)
        (fun v => (m v : ℂ) * unitVoltage nN θ v) (losslessAdmittance nE b) e)).re =
      b e * m (tail e) * m (head e) * Real.sin (θ (tail e) - θ (head e)) := by
  simp only [branchCurrent, branchDrop_electricalIncidence, losslessAdmittance, unitVoltage,
    complexPower, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [Real.sin_sub]
  ring

/-- Out of model, resistive admittance: a real conductance `g` on a
unit-magnitude branch absorbs `g * (1 - cos(θ tail - θ head))` at the
sending end, which no lossless DC flow represents. -/
lemma realPower_conductance (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (g : Fin nE → ℝ) (θ : Fin nN → ℝ) (e : Fin nE) :
    (complexPower (unitVoltage nN θ (tail e))
      (branchCurrent nN nE (electricalIncidence nN nE tail head) (unitVoltage nN θ)
        (fun e => (g e : ℂ)) e)).re =
      g e * (1 - Real.cos (θ (tail e) - θ (head e))) := by
  simp only [branchCurrent, branchDrop_electricalIncidence, unitVoltage, complexPower,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sub]
  have hcs2 : (g e) * (Real.cos (θ (tail e)) ^ 2 + Real.sin (θ (tail e)) ^ 2) = g e := by
    rw [Real.cos_sq_add_sin_sq, mul_one]
  linear_combination hcs2

/-! ## F. Headline -/

/-- Lossless DC load-flow model and its per-line angle error. The DC flow
is `f e = b e * (θ tail - θ head)`, the DC injection is `L_b * θ` for the
full weighted Laplacian, the lossless unit-magnitude AC sending-end real
power is `b e * sin(θ tail - θ head)`, and the two differ by at most
`b e * |θ tail - θ head| ^ 3 / 6` on every branch. -/
theorem model_correct (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 < b e) (θ : Fin nN → ℝ) :
    (∀ e, dcBranchFlow nN nE tail head b θ e = b e * (θ (tail e) - θ (head e))) ∧
      dcInjection nN nE tail head b θ =
        Matrix.mulVec (weightedLaplacian nN nE tail head b) θ ∧
      (∀ e, acBranchRealPower nN nE tail head b θ e =
        b e * Real.sin (θ (tail e) - θ (head e))) ∧
      (∀ e, |acBranchRealPower nN nE tail head b θ e - dcBranchFlow nN nE tail head b θ e| ≤
        b e * |θ (tail e) - θ (head e)| ^ 3 / 6) :=
  ⟨fun e => dcBranchFlow_apply nN nE tail head b θ e,
    dcInjection_eq_weightedLaplacian_mulVec nN nE tail head b θ,
    fun e => acBranchRealPower_eq_mul_sin nN nE tail head b θ e,
    fun e => abs_acBranchRealPower_sub_dcBranchFlow_le nN nE tail head b hb θ e⟩

end PhyslibExt.Circuits.LosslessDCFlowModel
