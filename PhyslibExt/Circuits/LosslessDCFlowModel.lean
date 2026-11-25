/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ArcPortSigns
public import MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
public import PhyslibExt.Circuits.ACInjectionLossBalance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Lossless DC load-flow model and its per-line angle error

## i. Overview

A finite network has nodes `Fin nN` and labeled oriented branches
`Fin nE` with tail and head maps, real branch susceptances `b e`, and
real node phase angles `θ`. The electrical incidence `B` is the
tail-positive `PhyslibExt.Circuits.ArcPortSigns.electricalIncidence`:
`B v e = 1` at the tail, `-1` at the head, the negation of the
head-positive arc incidence
`MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix`. The
lossless DC model is the branch flow `f = diag(b) * Bᵀ * θ`, so
`f e = b e * (θ tail - θ head)`, and the nodal injection `p = B * f`,
which equals `L_b * θ` for the full weighted Laplacian
`L_b = B * diag(b) * Bᵀ`. The two tail-positive signs cancel, so `L_b`
is the arc-network weighted Laplacian of
`MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian`, and its energy
identity, its kernel for nonnegative susceptances, and the positive
definiteness of its grounded block are restated here for `L_b`. The
injections sum to zero, and a uniform angle shift changes no flow, for
susceptances of any sign.

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
- `dotProduct_weightedLaplacian_mulVec`,
  `weightedLaplacian_mulVec_eq_zero_iff`, and
  `grounded_weightedLaplacian_isUnit`: the energy identity, the kernel for
  nonnegative susceptances, and the invertibility of the grounded block,
  transferred from the arc-network Laplacian.

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
open PhyslibExt.Circuits.ArcPortSigns
open MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian (positiveArcGraph)

/-- DC branch flow `f = diag(b) * Bᵀ * θ` for branch susceptances `b` and
node phase angles `θ`. -/
noncomputable def dcBranchFlow (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) : Fin nE → ℝ :=
  Matrix.mulVec
    (Matrix.diagonal b * Matrix.transpose (electricalIncidence tail head)) θ

/-- DC nodal injection `p = B * f`. -/
noncomputable def dcInjection (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) : Fin nN → ℝ :=
  Matrix.mulVec (electricalIncidence tail head) (dcBranchFlow nN nE tail head b θ)

/-- Full susceptance-weighted Laplacian `L_b = B * diag(b) * Bᵀ`, with no
reference row or column deleted. -/
noncomputable def weightedLaplacian (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) : Matrix (Fin nN) (Fin nN) ℝ :=
  electricalIncidence tail head * Matrix.diagonal b *
    Matrix.transpose (electricalIncidence tail head)

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
    (branchCurrent nN nE (electricalIncidence tail head) (unitVoltage nN θ)
      (losslessAdmittance nE b) e)).re

private lemma sum_incidence_indicator (nN : ℕ) (V : Fin nN → ℂ) (a : Fin nN) :
    (∑ v : Fin nN, ((if a = v then (1 : ℝ) else 0 : ℝ) : ℂ) * V v) = V a := by
  have hconv : ∀ v : Fin nN, (((if a = v then (1 : ℝ) else 0 : ℝ) : ℂ) * V v) =
      (if a = v then V v else 0) := by
    intro v
    by_cases h : a = v <;> simp [h]
  simp only [hconv]
  simp

private lemma ofReal_mul_re (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

/-! ## C. Incidence, drop, and injection identities -/

/-- The canonical branch drop through the electrical incidence is the
tail voltage minus the head voltage, loops included. -/
lemma branchDrop_electricalIncidence (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (V : Fin nN → ℂ) (e : Fin nE) :
    branchDrop nN nE (electricalIncidence tail head) V e = V (tail e) - V (head e) := by
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
  rw [dcBranchFlow, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal,
    branchVoltage_eq_tail_sub_head tail head θ _ rfl e]

/-- DC injection is the full weighted Laplacian applied to the angles,
`p = B * f = L_b * θ`. -/
lemma dcInjection_eq_weightedLaplacian_mulVec (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    dcInjection nN nE tail head b θ =
      Matrix.mulVec (weightedLaplacian nN nE tail head b) θ := by
  simp only [dcInjection, dcBranchFlow, weightedLaplacian, ← Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- The full weighted Laplacian is the arc-network weighted Laplacian
`incidenceMatrix * diag(b) * incidenceMatrixᵀ` of
`MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian`: the two
tail-positive signs cancel. -/
lemma weightedLaplacian_eq_incidenceMatrix (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) :
    weightedLaplacian nN nE tail head b =
      MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head *
        Matrix.diagonal b *
        Matrix.transpose (MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head) := by
  rw [weightedLaplacian, electricalIncidence_eq_neg_incidence, Matrix.transpose_neg,
    Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- Energy identity: `θ ⬝ᵥ L_b θ` is the susceptance-weighted sum of
squared angle differences across the branches. -/
lemma dotProduct_weightedLaplacian_mulVec (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    dotProduct θ (Matrix.mulVec (weightedLaplacian nN nE tail head b) θ) =
      ∑ e : Fin nE, b e * (θ (tail e) - θ (head e)) ^ 2 := by
  rw [weightedLaplacian_eq_incidenceMatrix,
    MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.dotProduct_weightedLaplacian_mulVec]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- Kernel for nonnegative susceptances: `L_b * θ = 0` iff `θ` is constant
on every connected component of the graph of positive-susceptance
branches. -/
lemma weightedLaplacian_mulVec_eq_zero_iff (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 ≤ b e) (θ : Fin nN → ℝ) :
    Matrix.mulVec (weightedLaplacian nN nE tail head b) θ = 0 ↔
      ∀ u v, (positiveArcGraph tail head b).Reachable u v → θ u = θ v := by
  rw [weightedLaplacian_eq_incidenceMatrix]
  exact MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.weightedLaplacian_mulVec_eq_zero_iff
    tail head b hb θ

open MathlibExt.Combinatorics.Graph in
/-- Kernel for nonnegative susceptances with every node reachable from `r`
through positive-susceptance branches: `L_b * θ = 0` iff `θ` is constant. -/
lemma weightedLaplacian_mulVec_eq_zero_iff_of_reachable (nN nE : ℕ)
    (tail head : Fin nE → Fin nN) (b : Fin nE → ℝ) (hb : ∀ e, 0 ≤ b e) (r : Fin nN)
    (hconn : ∀ v, (positiveArcGraph tail head b).Reachable r v) (θ : Fin nN → ℝ) :
    Matrix.mulVec (weightedLaplacian nN nE tail head b) θ = 0 ↔ ∀ v, θ v = θ r := by
  rw [weightedLaplacian_eq_incidenceMatrix]
  exact ArcNetworkLaplacian.weightedLaplacian_mulVec_eq_zero_iff_of_reachable
    tail head b hb r hconn θ

/-- Grounded block: with nonnegative susceptances and every node reachable
from the reference `r` through positive-susceptance branches, `L_b` with
the row and column of `r` deleted is positive definite. -/
theorem grounded_weightedLaplacian_posDef (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 ≤ b e) (r : Fin nN)
    (hconn : ∀ v, (positiveArcGraph tail head b).Reachable r v) :
    ((weightedLaplacian nN nE tail head b).submatrix
      (Subtype.val : {v // v ≠ r} → Fin nN) Subtype.val).PosDef := by
  rw [weightedLaplacian_eq_incidenceMatrix]
  exact MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian.grounded_weightedLaplacian_posDef
    tail head b hb r hconn

/-- The grounded block of `L_b` is invertible under the hypotheses of
`grounded_weightedLaplacian_posDef`. -/
theorem grounded_weightedLaplacian_isUnit (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (hb : ∀ e, 0 ≤ b e) (r : Fin nN)
    (hconn : ∀ v, (positiveArcGraph tail head b).Reachable r v) :
    IsUnit ((weightedLaplacian nN nE tail head b).submatrix
      (Subtype.val : {v // v ≠ r} → Fin nN) (Subtype.val : {v // v ≠ r} → Fin nN)) :=
  (grounded_weightedLaplacian_posDef nN nE tail head b hb r hconn).isUnit

/-- DC injections are balanced: they sum to zero over all nodes, which is
the full reference equation a grounded solve must respect. -/
lemma sum_dcInjection_eq_zero (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (θ : Fin nN → ℝ) :
    ∑ v : Fin nN, dcInjection nN nE tail head b θ v = 0 := by
  rw [dcInjection, electricalIncidence_eq_neg_incidence, Matrix.neg_mulVec]
  simp only [Pi.neg_apply, Finset.sum_neg_distrib,
    MathlibExt.Combinatorics.Graph.ArcNetwork.sum_incidenceMatrix_mulVec_eq_zero, neg_zero]

/-- A uniform angle shift changes no DC flow: the full weighted Laplacian
kills constant angle vectors. Unlike `weightedLaplacian_mulVec_eq_zero_iff`,
this holds for susceptances of any sign. -/
lemma weightedLaplacian_mulVec_const (nN nE : ℕ) (tail head : Fin nE → Fin nN)
    (b : Fin nE → ℝ) (c : ℝ) :
    Matrix.mulVec (weightedLaplacian nN nE tail head b) (fun _ => c) = 0 := by
  have htrans : Matrix.mulVec (Matrix.transpose (electricalIncidence tail head))
      (fun _ : Fin nN => c) = 0 := by
    funext e
    rw [branchVoltage_eq_tail_sub_head tail head (fun _ => c) _ rfl e, sub_self, Pi.zero_apply]
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
      (branchCurrent nN nE (electricalIncidence tail head) (unitVoltage nN θ)
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
    (nodeComplexPower nN nE (electricalIncidence tail head) (unitVoltage nN θ)
      (losslessAdmittance nE b) (fun _ => 0) v).re =
      ∑ e : Fin nE, electricalIncidence tail head v e *
        (b e * Real.sin (θ (tail e) - θ (head e))) := by
  have hbranch : ∀ e : Fin nE, electricalIncidence tail head v e *
        ((unitVoltage nN θ v) * conj (branchCurrent nN nE
          (electricalIncidence tail head) (unitVoltage nN θ)
          (losslessAdmittance nE b) e)).re =
        electricalIncidence tail head v e *
          (b e * Real.sin (θ (tail e) - θ (head e))) := by
    intro e
    by_cases ht : tail e = v
    · by_cases hh : head e = v
      · have hB : electricalIncidence tail head v e = 0 := by
          simp [electricalIncidence_apply, ht, hh]
        simp [hB]
      · have hP : ((unitVoltage nN θ v) * conj (branchCurrent nN nE
            (electricalIncidence tail head) (unitVoltage nN θ)
            (losslessAdmittance nE b) e)).re =
            acBranchRealPower nN nE tail head b θ e := by
          simp only [← ht, acBranchRealPower, complexPower]
        rw [hP, acBranchRealPower_eq_mul_sin]
    · by_cases hh : head e = v
      · have hP : ((unitVoltage nN θ v) * conj (branchCurrent nN nE
            (electricalIncidence tail head) (unitVoltage nN θ)
            (losslessAdmittance nE b) e)).re =
            acBranchRealPower nN nE tail head b θ e := by
          rw [← hh]
          exact receivingRealPower_eq_acBranchRealPower nN nE tail head b θ e
        rw [hP, acBranchRealPower_eq_mul_sin]
      · have hB : electricalIncidence tail head v e = 0 := by
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
    ∑ v : Fin nN, (nodeComplexPower nN nE (electricalIncidence tail head)
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
    |(nodeComplexPower nN nE (electricalIncidence tail head) (unitVoltage nN θ)
        (losslessAdmittance nE b) (fun _ => 0) v).re -
        dcInjection nN nE tail head b θ v| ≤
      ∑ e : Fin nE, |electricalIncidence tail head v e| *
        (b e * |θ (tail e) - θ (head e)| ^ 3 / 6) := by
  have hdc : dcInjection nN nE tail head b θ v =
      ∑ e : Fin nE, electricalIncidence tail head v e *
        dcBranchFlow nN nE tail head b θ e := by
    simp only [dcInjection, Matrix.mulVec, dotProduct]
  rw [nodeRealPower_eq_sum_mul_sin, hdc, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ Finset.univ) ?_
  refine Finset.sum_le_sum fun e _ => ?_
  have hP := acBranchRealPower_eq_mul_sin nN nE tail head b θ e
  have hf := dcBranchFlow_apply nN nE tail head b θ e
  have hbound := abs_acBranchRealPower_sub_dcBranchFlow_le nN nE tail head b hb θ e
  rw [hP, hf] at hbound
  have hfactor : electricalIncidence tail head v e *
        (b e * Real.sin (θ (tail e) - θ (head e))) -
        electricalIncidence tail head v e * dcBranchFlow nN nE tail head b θ e =
        electricalIncidence tail head v e *
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
      (branchCurrent nN nE (electricalIncidence tail head)
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
      (branchCurrent nN nE (electricalIncidence tail head) (unitVoltage nN θ)
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
