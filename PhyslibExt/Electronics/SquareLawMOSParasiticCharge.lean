/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.DynamicTerminalKCL
public import PhyslibExt.Electronics.TerminalChargeJacobian
public import PhyslibExt.Electronics.IdealSquareLawMOS
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Square-law nMOS with fixed parasitic capacitors

## i. Overview

A three-terminal nMOS with terminals gate `0`, drain `1` and source `2`
and terminal voltages `w : Fin 3 → ℝ` stores charge on three fixed
pairwise parasitic capacitors `Cgs`, `Cgd`, `Cds`. The charges are the
generic pairwise-capacitor charges of the terminal-charge Jacobian
module for the symmetric capacitance matrix
`!![0, Cgd, Cgs; Cgd, 0, Cds; Cgs, Cds, 0]`, which reduce to
`qg = Cgs (Vg - Vs) + Cgd (Vg - Vd)`, `qd = Cgd (Vd - Vg) + Cds (Vd - Vs)`
and `qs = Cgs (Vs - Vg) + Cds (Vs - Vd)`. Its static conduction currents
are `Ig = 0`, the ideal square-law drain current `Id = I(u, Vds)` with
overdrive `u = Vg - Vs - Vth` and `Vds = Vd - Vs`, and `Is = -Id`.

Specializing the pairwise-capacitor results, the charge map conserves
charge (`qg + qd + qs = 0`), is invariant under common-mode voltage
shifts in the form the terminal-charge Jacobian theorem takes, and the static
currents sum to zero. The dynamic terminal Kirchhoff current law then
applies: along a differentiable bias path, in particular one that stays
in an open forward regime (cutoff, triode or saturation, each with
`Vds > 0`), the dynamic terminal currents `I_cond,i + d q_i / dt` sum to
zero at every time. The capacitances model fixed parasitic or overlap
storage only, not an intrinsic channel-charge partition; the pairwise
matrix is symmetric by construction, and no symmetry of an intrinsic
capacitance matrix or short-channel model is claimed.

The absorbed displacement power equals the rate of change of the stored
energy `(Cgs (Vg - Vs)² + Cgd (Vg - Vd)² + Cds (Vd - Vs)²) / 2`, which
is nonnegative for nonnegative capacitances. Validation cases: a
saturation bias path with nonzero gate displacement current and zero
total current; flipping the sign of the gate charge formula breaks
conservation and the dynamic law; and a concrete negative capacitance
satisfies the dynamic law while storing negative energy at some voltage.
A single negative capacitance does not by itself force negative energy,
since the three pairwise voltages are dependent, so only this concrete
case is stated.

## ii. Key results

- `parasiticCapacitance`, `parasiticCharge`, `parasiticCharge_eq`: the
  capacitance matrix, the pairwise-capacitor charges it determines, and
  their explicit formulas.
- `parasiticCharge_sum_eq_zero`, `parasiticCharge_gauge`: the
  conservation and gauge premises, from the pairwise-capacitor results.
- `parasiticCharge_jacobian_sums_eq_zero`: zero row and column sums of
  the charge Jacobian at every voltage, from the pairwise-capacitor results.
- `conductionCurrent_sum_eq_zero`: static current conservation.
- `sum_dynamicTerminalCurrent_eq_zero`: the dynamic Kirchhoff current
  law along every differentiable path, for all real capacitances.
- `squareLawMOSParasiticCharge_dynamicKCL`: the bundled statement on an
  open forward regime, with nonnegative stored energy and nonnegative
  drain current along the path.
- `sum_mul_displacementCurrent_eq_deriv_energy`: displacement power is
  the rate of change of stored energy.
- `saturation_path_example`, `flippedGateCharge_dynamic_sum_ne_zero`,
  `negativeCapacitance_negative_energy_and_kcl`: validation cases.

## iii. Table of contents

- A. The device model
- B. Conservation and gauge premises
- C. Static conduction currents and forward regimes
- D. Displacement currents along a bias path
- E. Dynamic terminal Kirchhoff law
- F. Stored energy
- G. Validation

## iv. References

- Y. Tsividis and C. McAndrew, *Operation and Modeling of the MOS
  Transistor*, third edition, Oxford University Press, 2011: extrinsic
  overlap capacitances, charge-based terminal currents as transport
  current plus the time derivative of terminal charge, and charge
  conservation.
- A. S. Sedra and K. C. Smith, *Microelectronic Circuits*, eighth
  edition, Oxford University Press, 2020: the square-law drain current
  in cutoff, triode and saturation.
-/

@[expose] public section

namespace PhyslibExt.Electronics.SquareLawMOSParasiticCharge

open PhyslibExt.Electronics.DynamicTerminalKCL
open PhyslibExt.Electronics.TerminalChargeJacobian

/-! ## A. The device model -/

/-- Symmetric pairwise capacitance matrix on terminals gate `0`, drain `1`, source `2`:
`Cgd` joins gate and drain, `Cgs` gate and source, `Cds` drain and source. -/
def parasiticCapacitance (Cgs Cgd Cds : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, Cgd, Cgs; Cgd, 0, Cds; Cgs, Cds, 0]

/-- Terminal charges of the three fixed parasitic capacitors: the pairwise-capacitor charges
of `parasiticCapacitance`. -/
def parasiticCharge (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  pairwiseCapacitorCharge 3 (parasiticCapacitance Cgs Cgd Cds) w

/-- Static conduction currents: `Ig = 0`, `Id` the square-law drain current at
overdrive `Vg - Vs - Vth` and drain voltage `Vd - Vs`, and `Is = -Id`. -/
noncomputable def conductionCurrent (beta Vth : ℝ) (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![0,
    PhyslibExt.Electronics.IdealSquareLawMOS.current beta (w 0 - w 2 - Vth) (w 1 - w 2),
    -PhyslibExt.Electronics.IdealSquareLawMOS.current beta (w 0 - w 2 - Vth) (w 1 - w 2)]

/-- The three open forward operating regimes. -/
inductive ForwardRegion
  /-- Open cutoff: negative overdrive, positive drain voltage. -/
  | cutoff
  /-- Open triode: `0 < Vds < u`. -/
  | triode
  /-- Open saturation: `0 < u < Vds`. -/
  | saturation

/-- The open set of terminal voltages in a forward regime, with `u = Vg - Vs - Vth` and
`Vds = Vd - Vs`. -/
def forwardRegion (Vth : ℝ) : ForwardRegion → Set (Fin 3 → ℝ)
  | .cutoff => {w | w 0 - w 2 - Vth < 0 ∧ 0 < w 1 - w 2}
  | .triode => {w | 0 < w 1 - w 2 ∧ w 1 - w 2 < w 0 - w 2 - Vth}
  | .saturation => {w | 0 < w 0 - w 2 - Vth ∧ w 0 - w 2 - Vth < w 1 - w 2}

/-- Energy stored in the three parasitic capacitors. -/
noncomputable def parasiticEnergy (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) : ℝ :=
  (Cgs * (w 0 - w 2) ^ 2 + Cgd * (w 0 - w 1) ^ 2 + Cds * (w 1 - w 2) ^ 2) / 2

/-- The charge map with the sign of the gate charge formula flipped, a violated
conservation premise. -/
def flippedGateCharge (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-(Cgs * (w 0 - w 2) + Cgd * (w 0 - w 1)),
    Cgd * (w 1 - w 0) + Cds * (w 1 - w 2),
    Cgs * (w 2 - w 0) + Cds * (w 2 - w 1)]

/-- The capacitance matrix is symmetric. -/
lemma parasiticCapacitance_symm (Cgs Cgd Cds : ℝ) (i k : Fin 3) :
    parasiticCapacitance Cgs Cgd Cds i k = parasiticCapacitance Cgs Cgd Cds k i := by
  fin_cases i <;> fin_cases k <;> simp [parasiticCapacitance]

/-- The explicit charge formulas: `qg = Cgs (Vg - Vs) + Cgd (Vg - Vd)`,
`qd = Cgd (Vd - Vg) + Cds (Vd - Vs)`, `qs = Cgs (Vs - Vg) + Cds (Vs - Vd)`. -/
lemma parasiticCharge_eq (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) :
    parasiticCharge Cgs Cgd Cds w =
      ![Cgs * (w 0 - w 2) + Cgd * (w 0 - w 1),
        Cgd * (w 1 - w 0) + Cds * (w 1 - w 2),
        Cgs * (w 2 - w 0) + Cds * (w 2 - w 1)] := by
  ext i
  fin_cases i <;>
    simp [parasiticCharge, parasiticCapacitance, pairwiseCapacitorCharge, Fin.sum_univ_three]
  ring

/-! ## B. Conservation and gauge premises -/

/-- **Charge conservation.** The three terminal charges sum to zero at every voltage. -/
theorem parasiticCharge_sum_eq_zero (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) :
    ∑ i, parasiticCharge Cgs Cgd Cds w i = 0 :=
  pairwiseCapacitorCharge_sum_eq_zero 3 _ (parasiticCapacitance_symm Cgs Cgd Cds) w

/-- A common voltage shift leaves every terminal charge unchanged. -/
lemma parasiticCharge_common_mode (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) (c : ℝ) :
    parasiticCharge Cgs Cgd Cds (w + c • (fun _ => (1 : ℝ))) =
      parasiticCharge Cgs Cgd Cds w :=
  pairwiseCapacitorCharge_common_mode 3 _ w c

/-- **Gauge premise.** Common-mode invariance in the exact form the terminal-charge
Jacobian theorem takes, on any voltage set. -/
theorem parasiticCharge_gauge (Cgs Cgd Cds : ℝ) (U : Set (Fin 3 → ℝ)) :
    ∀ w ∈ U, ∃ δ > 0, ∀ c : ℝ, |c| < δ → w + c • (fun _ => (1 : ℝ)) ∈ U →
      parasiticCharge Cgs Cgd Cds (w + c • (fun _ => (1 : ℝ))) =
        parasiticCharge Cgs Cgd Cds w := by
  intro w _
  exact ⟨1, one_pos, fun c _ _ => parasiticCharge_common_mode _ _ _ _ c⟩

/-- Every charge component is differentiable on any voltage set. -/
lemma parasiticCharge_differentiableOn (Cgs Cgd Cds : ℝ) (U : Set (Fin 3 → ℝ)) :
    ∀ i, DifferentiableOn ℝ (fun w => parasiticCharge Cgs Cgd Cds w i) U := by
  intro i
  simp only [parasiticCharge_eq]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> fun_prop

/-- **Charge Jacobian sums.** The charge Jacobian has zero column sums and zero row sums at
every voltage: `pairwiseCapacitorCharge_jacobian_sums_eq_zero` for `parasiticCapacitance`. -/
theorem parasiticCharge_jacobian_sums_eq_zero (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) :
    (∀ j, ∑ i, MetaMathlibExt.jacobianMatrix (parasiticCharge Cgs Cgd Cds) w i j = 0) ∧
      (∀ i, ∑ j, MetaMathlibExt.jacobianMatrix (parasiticCharge Cgs Cgd Cds) w i j = 0) :=
  pairwiseCapacitorCharge_jacobian_sums_eq_zero 3 _ (parasiticCapacitance_symm Cgs Cgd Cds) w

/-! ## C. Static conduction currents and forward regimes -/

/-- Terminal conduction currents: `Ig = 0`, `Id` the square-law current, `Is = -Id`. -/
lemma conductionCurrent_apply (beta Vth : ℝ) (w : Fin 3 → ℝ) :
    conductionCurrent beta Vth w 0 = 0 ∧
      conductionCurrent beta Vth w 1 =
        PhyslibExt.Electronics.IdealSquareLawMOS.current beta (w 0 - w 2 - Vth) (w 1 - w 2) ∧
      conductionCurrent beta Vth w 2 = -conductionCurrent beta Vth w 1 := by
  simp [conductionCurrent]

/-- **Static current conservation.** The conduction currents sum to zero at every
voltage. -/
theorem conductionCurrent_sum_eq_zero (beta Vth : ℝ) (w : Fin 3 → ℝ) :
    ∑ i, conductionCurrent beta Vth w i = 0 := by
  simp [conductionCurrent, Fin.sum_univ_three]

/-- Each forward regime is open. -/
lemma isOpen_forwardRegion (Vth : ℝ) (r : ForwardRegion) :
    IsOpen (forwardRegion Vth r) := by
  cases r <;> simp only [forwardRegion, Set.ofPred_and]
  · exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt continuous_const (by fun_prop))
  · exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))
  · exact (isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))

/-- Each forward regime has positive drain voltage. -/
lemma forwardRegion_vds_pos (Vth : ℝ) (r : ForwardRegion) (w : Fin 3 → ℝ)
    (hw : w ∈ forwardRegion Vth r) : 0 < w 1 - w 2 := by
  cases r <;> simp only [forwardRegion, Set.mem_ofPred_eq] at hw
  · exact hw.2
  · exact hw.1
  · exact lt_trans hw.1 hw.2

/-- Each forward regime is invariant under common-mode voltage shifts. -/
lemma forwardRegion_common_mode (Vth : ℝ) (r : ForwardRegion) (w : Fin 3 → ℝ) (c : ℝ) :
    w + c • (fun _ => (1 : ℝ)) ∈ forwardRegion Vth r ↔ w ∈ forwardRegion Vth r := by
  cases r <;>
    simp only [forwardRegion, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · constructor <;> intro h <;> obtain ⟨h1, h2⟩ := h <;> constructor <;> linarith
  · constructor <;> intro h <;> obtain ⟨h1, h2⟩ := h <;> constructor <;> linarith
  · constructor <;> intro h <;> obtain ⟨h1, h2⟩ := h <;> constructor <;> linarith

/-- Regional drain current, cutoff. -/
lemma conductionCurrent_drain_of_cutoff (beta Vth : ℝ) (w : Fin 3 → ℝ)
    (hw : w ∈ forwardRegion Vth .cutoff) :
    conductionCurrent beta Vth w 1 = 0 := by
  simp only [forwardRegion, Set.mem_ofPred_eq] at hw
  rw [(conductionCurrent_apply beta Vth w).2.1]
  exact PhyslibExt.Electronics.IdealSquareLawMOS.current_of_nonpos _ _ _ hw.1.le

/-- Regional drain current, triode. -/
lemma conductionCurrent_drain_of_triode (beta Vth : ℝ) (w : Fin 3 → ℝ)
    (hw : w ∈ forwardRegion Vth .triode) :
    conductionCurrent beta Vth w 1 =
      PhyslibExt.Electronics.IdealSquareLawMOS.triodeCurrent beta (w 0 - w 2 - Vth)
        (w 1 - w 2) := by
  simp only [forwardRegion, Set.mem_ofPred_eq] at hw
  obtain ⟨h1, h2⟩ := hw
  rw [(conductionCurrent_apply beta Vth w).2.1]
  exact PhyslibExt.Electronics.IdealSquareLawMOS.current_of_triode _ _ _ (lt_trans h1 h2)
    h1.le h2.le

/-- Regional drain current, saturation. -/
lemma conductionCurrent_drain_of_saturation (beta Vth : ℝ) (w : Fin 3 → ℝ)
    (hw : w ∈ forwardRegion Vth .saturation) :
    conductionCurrent beta Vth w 1 =
      PhyslibExt.Electronics.IdealSquareLawMOS.saturationCurrent beta (w 0 - w 2 - Vth) := by
  simp only [forwardRegion, Set.mem_ofPred_eq] at hw
  obtain ⟨h1, h2⟩ := hw
  rw [(conductionCurrent_apply beta Vth w).2.1]
  exact PhyslibExt.Electronics.IdealSquareLawMOS.current_of_saturation _ _ _ h1 h2.le

/-- The conduction currents are differentiable on each open forward regime. -/
lemma conductionCurrent_differentiableOn (beta Vth : ℝ) (r : ForwardRegion) :
    ∀ i, DifferentiableOn ℝ (fun w => conductionCurrent beta Vth w i) (forwardRegion Vth r) := by
  have h1 : DifferentiableOn ℝ (fun w => conductionCurrent beta Vth w 1)
      (forwardRegion Vth r) := by
    cases r
    · exact (differentiableOn_const 0).congr
        (fun w hw => conductionCurrent_drain_of_cutoff beta Vth w hw)
    · have hF : DifferentiableOn ℝ
          (fun w : Fin 3 → ℝ => PhyslibExt.Electronics.IdealSquareLawMOS.triodeCurrent beta
            (w 0 - w 2 - Vth) (w 1 - w 2)) (forwardRegion Vth .triode) := by
        simp only [PhyslibExt.Electronics.IdealSquareLawMOS.triodeCurrent]
        fun_prop
      exact hF.congr (fun w hw => conductionCurrent_drain_of_triode beta Vth w hw)
    · have hF : DifferentiableOn ℝ
          (fun w : Fin 3 → ℝ =>
            PhyslibExt.Electronics.IdealSquareLawMOS.saturationCurrent beta
              (w 0 - w 2 - Vth)) (forwardRegion Vth .saturation) := by
        simp only [PhyslibExt.Electronics.IdealSquareLawMOS.saturationCurrent]
        fun_prop
      exact hF.congr (fun w hw => conductionCurrent_drain_of_saturation beta Vth w hw)
  intro i
  fin_cases i
  · exact (differentiableOn_const 0).congr (fun w _ => (conductionCurrent_apply _ _ _).1)
  · exact h1
  · exact h1.neg.congr (fun w _ => (conductionCurrent_apply _ _ _).2.2)

/-! ## D. Displacement currents along a bias path -/

/-- Explicit displacement currents of the parasitic charges along a differentiable path. -/
lemma displacementCurrent_parasiticCharge (Cgs Cgd Cds : ℝ) (v : ℝ → (Fin 3 → ℝ))
    (hv : Differentiable ℝ v) (t : ℝ) :
    displacementCurrent 3 (parasiticCharge Cgs Cgd Cds) v t 0 =
        Cgs * (deriv (fun s => v s 0) t - deriv (fun s => v s 2) t) +
          Cgd * (deriv (fun s => v s 0) t - deriv (fun s => v s 1) t) ∧
      displacementCurrent 3 (parasiticCharge Cgs Cgd Cds) v t 1 =
        Cgd * (deriv (fun s => v s 1) t - deriv (fun s => v s 0) t) +
          Cds * (deriv (fun s => v s 1) t - deriv (fun s => v s 2) t) ∧
      displacementCurrent 3 (parasiticCharge Cgs Cgd Cds) v t 2 =
        Cgs * (deriv (fun s => v s 2) t - deriv (fun s => v s 0) t) +
          Cds * (deriv (fun s => v s 2) t - deriv (fun s => v s 1) t) := by
  have hd : ∀ j, HasDerivAt (fun s => v s j) (deriv (fun s => v s j) t) t :=
    fun j => (differentiableAt_pi.mp (hv t) j).hasDerivAt
  have q0 : (fun s => parasiticCharge Cgs Cgd Cds (v s) 0)
      = fun s => Cgs * (v s 0 - v s 2) + Cgd * (v s 0 - v s 1) := by
    funext s
    simp [parasiticCharge_eq]
  have q1 : (fun s => parasiticCharge Cgs Cgd Cds (v s) 1)
      = fun s => Cgd * (v s 1 - v s 0) + Cds * (v s 1 - v s 2) := by
    funext s
    simp [parasiticCharge_eq]
  have q2 : (fun s => parasiticCharge Cgs Cgd Cds (v s) 2)
      = fun s => Cgs * (v s 2 - v s 0) + Cds * (v s 2 - v s 1) := by
    funext s
    simp [parasiticCharge_eq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [displacementCurrent, q0]
    exact ((((hd 0).sub (hd 2)).const_mul Cgs).add (((hd 0).sub (hd 1)).const_mul Cgd)).deriv
  · simp only [displacementCurrent, q1]
    exact ((((hd 1).sub (hd 0)).const_mul Cgd).add (((hd 1).sub (hd 2)).const_mul Cds)).deriv
  · simp only [displacementCurrent, q2]
    exact ((((hd 2).sub (hd 0)).const_mul Cgs).add (((hd 2).sub (hd 1)).const_mul Cds)).deriv

/-- The displacement currents sum to zero along every differentiable path, by the general
zero-total-displacement law on the whole voltage space. -/
lemma sum_displacementCurrent_parasiticCharge_eq_zero (Cgs Cgd Cds : ℝ)
    (v : ℝ → (Fin 3 → ℝ)) (hv : Differentiable ℝ v) (t : ℝ) :
    ∑ i, displacementCurrent 3 (parasiticCharge Cgs Cgd Cds) v t i = 0 :=
  PhyslibExt.Electronics.DynamicTerminalKCL.sum_displacementCurrent_eq_zero 3 Set.univ
    isOpen_univ _ (parasiticCharge_differentiableOn Cgs Cgd Cds Set.univ)
    (fun w _ => parasiticCharge_sum_eq_zero Cgs Cgd Cds w) v hv (fun _ => Set.mem_univ _) t

/-! ## E. Dynamic terminal Kirchhoff law -/

/-- **Dynamic terminal KCL.** For the parasitic-capacitor square-law nMOS, the dynamic
terminal currents sum to zero along any differentiable path, with no sign hypothesis on the
capacitances. -/
theorem sum_dynamicTerminalCurrent_eq_zero (Cgs Cgd Cds beta Vth : ℝ)
    (v : ℝ → (Fin 3 → ℝ)) (hv : Differentiable ℝ v) (t : ℝ) :
    ∑ i, dynamicTerminalCurrent 3 (parasiticCharge Cgs Cgd Cds) (conductionCurrent beta Vth)
      v t i = 0 :=
  PhyslibExt.Electronics.DynamicTerminalKCL.sum_dynamicTerminalCurrent_eq_zero 3 Set.univ
    isOpen_univ _ (parasiticCharge_differentiableOn Cgs Cgd Cds Set.univ)
    (fun w _ => parasiticCharge_sum_eq_zero Cgs Cgd Cds w) _
    (fun w _ => conductionCurrent_sum_eq_zero beta Vth w) v hv (fun _ => Set.mem_univ _) t

/-- Nonnegative capacitances store nonnegative energy. -/
lemma parasiticEnergy_nonneg (Cgs Cgd Cds : ℝ) (hCgs : 0 ≤ Cgs) (hCgd : 0 ≤ Cgd)
    (hCds : 0 ≤ Cds) (w : Fin 3 → ℝ) :
    0 ≤ parasiticEnergy Cgs Cgd Cds w := by
  unfold parasiticEnergy
  refine div_nonneg ?_ (by norm_num)
  exact add_nonneg (add_nonneg (mul_nonneg hCgs (sq_nonneg _)) (mul_nonneg hCgd (sq_nonneg _)))
    (mul_nonneg hCds (sq_nonneg _))

/-- **Square-law nMOS with fixed parasitic capacitors.** Under nonnegative capacitances,
`beta > 0`, and a differentiable bias path staying in one open forward regime: the charge
formulas conserve charge and satisfy the gauge premise on the regime, the static currents
are conserved, the dynamic terminal currents sum to zero at every time, the stored
parasitic energy is nonnegative at every time, and the drain conduction current is
nonnegative at every time. The dynamic law itself needs none of the sign hypotheses
(`sum_dynamicTerminalCurrent_eq_zero`); the capacitance signs give the energy bound and
`beta > 0` with the forward regime gives the current bound. -/
theorem squareLawMOSParasiticCharge_dynamicKCL (Cgs Cgd Cds beta Vth : ℝ)
    (hCgs : 0 ≤ Cgs) (hCgd : 0 ≤ Cgd) (hCds : 0 ≤ Cds) (hbeta : 0 < beta)
    (r : ForwardRegion) (v : ℝ → (Fin 3 → ℝ)) (hv : Differentiable ℝ v)
    (hvr : ∀ t, v t ∈ forwardRegion Vth r) :
    (∀ w ∈ forwardRegion Vth r, ∑ i, parasiticCharge Cgs Cgd Cds w i = 0) ∧
      (∀ w ∈ forwardRegion Vth r, ∃ δ > 0, ∀ c : ℝ, |c| < δ →
        w + c • (fun _ => (1 : ℝ)) ∈ forwardRegion Vth r →
          parasiticCharge Cgs Cgd Cds (w + c • (fun _ => (1 : ℝ))) =
            parasiticCharge Cgs Cgd Cds w) ∧
      (∀ w ∈ forwardRegion Vth r, ∑ i, conductionCurrent beta Vth w i = 0) ∧
      (∀ t, ∑ i, dynamicTerminalCurrent 3 (parasiticCharge Cgs Cgd Cds)
        (conductionCurrent beta Vth) v t i = 0) ∧
      (∀ t, 0 ≤ parasiticEnergy Cgs Cgd Cds (v t)) ∧
      (∀ t, 0 ≤ conductionCurrent beta Vth (v t) 1) :=
  ⟨fun w _ => parasiticCharge_sum_eq_zero _ _ _ w, parasiticCharge_gauge _ _ _ _,
    fun w _ => conductionCurrent_sum_eq_zero _ _ w,
    PhyslibExt.Electronics.DynamicTerminalKCL.sum_dynamicTerminalCurrent_eq_zero 3
      (forwardRegion Vth r) (isOpen_forwardRegion Vth r) _
      (parasiticCharge_differentiableOn Cgs Cgd Cds _)
      (fun w _ => parasiticCharge_sum_eq_zero Cgs Cgd Cds w) _
      (fun w _ => conductionCurrent_sum_eq_zero beta Vth w) v hv hvr,
    fun t => parasiticEnergy_nonneg Cgs Cgd Cds hCgs hCgd hCds (v t),
    fun t => by
      rw [(conductionCurrent_apply beta Vth (v t)).2.1]
      exact PhyslibExt.Electronics.IdealSquareLawMOS.current_nonneg _ _ _ hbeta
        (forwardRegion_vds_pos Vth r (v t) (hvr t)).le⟩

/-! ## F. Stored energy -/

/-- Charge-energy identity: `∑ i, w i * q i (w)` is twice the stored energy. -/
lemma sum_mul_parasiticCharge_eq_two_mul_energy (Cgs Cgd Cds : ℝ) (w : Fin 3 → ℝ) :
    ∑ i, w i * parasiticCharge Cgs Cgd Cds w i = 2 * parasiticEnergy Cgs Cgd Cds w := by
  simp only [Fin.sum_univ_three, parasiticCharge_eq, parasiticEnergy, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **Energy balance.** Absorbed displacement power equals the rate of change of stored
energy along a differentiable path. -/
theorem sum_mul_displacementCurrent_eq_deriv_energy (Cgs Cgd Cds : ℝ)
    (v : ℝ → (Fin 3 → ℝ)) (hv : Differentiable ℝ v) (t : ℝ) :
    ∑ i, v t i * displacementCurrent 3 (parasiticCharge Cgs Cgd Cds) v t i =
      deriv (fun s => parasiticEnergy Cgs Cgd Cds (v s)) t := by
  have hd : ∀ j, HasDerivAt (fun s => v s j) (deriv (fun s => v s j) t) t :=
    fun j => (differentiableAt_pi.mp (hv t) j).hasDerivAt
  obtain ⟨e0, e1, e2⟩ := displacementCurrent_parasiticCharge Cgs Cgd Cds v hv t
  have hE : (fun s => parasiticEnergy Cgs Cgd Cds (v s))
      = fun s => (Cgs * (v s 0 - v s 2) ^ 2 + Cgd * (v s 0 - v s 1) ^ 2 +
        Cds * (v s 1 - v s 2) ^ 2) / 2 := by
    funext s
    simp [parasiticEnergy]
  have hFull : HasDerivAt
      (fun s => (Cgs * ((v s 0 - v s 2) * (v s 0 - v s 2)) +
        Cgd * ((v s 0 - v s 1) * (v s 0 - v s 1)) +
        Cds * ((v s 1 - v s 2) * (v s 1 - v s 2))) / 2)
      ((Cgs * ((deriv (fun s => v s 0) t - deriv (fun s => v s 2) t) * (v t 0 - v t 2) +
          (v t 0 - v t 2) * (deriv (fun s => v s 0) t - deriv (fun s => v s 2) t)) +
        Cgd * ((deriv (fun s => v s 0) t - deriv (fun s => v s 1) t) * (v t 0 - v t 1) +
          (v t 0 - v t 1) * (deriv (fun s => v s 0) t - deriv (fun s => v s 1) t)) +
        Cds * ((deriv (fun s => v s 1) t - deriv (fun s => v s 2) t) * (v t 1 - v t 2) +
          (v t 1 - v t 2) * (deriv (fun s => v s 1) t - deriv (fun s => v s 2) t))) / 2)
      t := by
    have m02 := ((hd 0).sub (hd 2)).mul ((hd 0).sub (hd 2))
    have m01 := ((hd 0).sub (hd 1)).mul ((hd 0).sub (hd 1))
    have m12 := ((hd 1).sub (hd 2)).mul ((hd 1).sub (hd 2))
    exact (((m02.const_mul Cgs).add (m01.const_mul Cgd)).add (m12.const_mul Cds)).div_const 2
  rw [hE]
  simp only [pow_two]
  rw [Fin.sum_univ_three, e0, e1, e2, hFull.deriv]
  ring

/-! ## G. Validation -/

/-- Positive case: with unit capacitances, `beta = 2`, `Vth = 1`, the gate bias path
`(2 + sin s / 2, 5, 0)` stays in saturation, the gate displacement current at time `0` is
`1`, and the dynamic currents sum to zero. -/
lemma saturation_path_example :
    (∀ t, (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) t ∈ forwardRegion 1 .saturation) ∧
      displacementCurrent 3 (parasiticCharge 1 1 1) (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0])
        0 0 = 1 ∧
      ∑ i, dynamicTerminalCurrent 3 (parasiticCharge 1 1 1) (conductionCurrent 2 1)
        (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) 0 i = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simp only [forwardRegion, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    constructor <;> linarith [Real.neg_one_le_sin t, Real.sin_le_one t]
  · have hq : (fun s => parasiticCharge 1 1 1
          ((fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) s) 0)
        = fun s => Real.sin s - 1 := by
      funext s
      simp only [parasiticCharge_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    simp only [displacementCurrent, hq]
    rw [((Real.hasDerivAt_sin 0).sub_const 1).deriv, Real.cos_zero]
  · have hv : Differentiable ℝ (fun s : ℝ => ![2 + Real.sin s / 2, 5, 0]) := by
      rw [differentiable_pi]
      intro i
      fin_cases i <;> simp
    exact PhyslibExt.Electronics.SquareLawMOSParasiticCharge.sum_dynamicTerminalCurrent_eq_zero
      1 1 1 2 1 _ hv 0

/-- Violated premise, static: flipping the sign of the gate charge formula breaks charge
conservation at some voltage when `Cgs > 0` and `Cgd ≥ 0`. -/
lemma exists_sum_flippedGateCharge_ne_zero (Cgs Cgd Cds : ℝ) (hCgs : 0 < Cgs)
    (hCgd : 0 ≤ Cgd) :
    ∃ w : Fin 3 → ℝ, ∑ i, flippedGateCharge Cgs Cgd Cds w i ≠ 0 := by
  refine ⟨![1, 0, 0], ?_⟩
  have hsum : ∑ i, flippedGateCharge Cgs Cgd Cds ![1, 0, 0] i = -2 * Cgs - 2 * Cgd := by
    simp only [Fin.sum_univ_three, flippedGateCharge, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hsum]
  intro h
  linarith

/-- **Violated premise, dynamic.** With the flipped gate charge, the gate ramp `(s, 0, 0)`
has nonzero summed dynamic current at time `0`. -/
lemma flippedGateCharge_dynamic_sum_ne_zero (Cgs Cgd Cds beta Vth : ℝ) (hCgs : 0 < Cgs)
    (hCgd : 0 ≤ Cgd) :
    ∑ i, dynamicTerminalCurrent 3 (flippedGateCharge Cgs Cgd Cds) (conductionCurrent beta Vth)
      (fun s : ℝ => ![s, 0, 0]) 0 i ≠ 0 := by
  have hlin : ∀ c : ℝ, deriv (fun s : ℝ => c * s) 0 = c := by
    intro c
    have h : HasDerivAt (fun s : ℝ => c * s) (c * 1) 0 := (hasDerivAt_id 0).const_mul c
    rw [h.deriv, mul_one]
  have d0 : displacementCurrent 3 (flippedGateCharge Cgs Cgd Cds)
      (fun s : ℝ => ![s, 0, 0]) 0 0 = -(Cgs + Cgd) := by
    have hq : (fun s => flippedGateCharge Cgs Cgd Cds ((fun s : ℝ => ![s, 0, 0]) s) 0)
        = fun s => (-(Cgs + Cgd)) * s := by
      funext s
      simp only [flippedGateCharge, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    simp only [displacementCurrent, hq]
    exact hlin _
  have d1 : displacementCurrent 3 (flippedGateCharge Cgs Cgd Cds)
      (fun s : ℝ => ![s, 0, 0]) 0 1 = -Cgd := by
    have hq : (fun s => flippedGateCharge Cgs Cgd Cds ((fun s : ℝ => ![s, 0, 0]) s) 1)
        = fun s => (-Cgd) * s := by
      funext s
      simp [flippedGateCharge]
    simp only [displacementCurrent, hq]
    exact hlin _
  have d2 : displacementCurrent 3 (flippedGateCharge Cgs Cgd Cds)
      (fun s : ℝ => ![s, 0, 0]) 0 2 = -Cgs := by
    have hq : (fun s => flippedGateCharge Cgs Cgd Cds ((fun s : ℝ => ![s, 0, 0]) s) 2)
        = fun s => (-Cgs) * s := by
      funext s
      simp [flippedGateCharge]
    simp only [displacementCurrent, hq]
    exact hlin _
  simp only [dynamicTerminalCurrent]
  rw [Finset.sum_add_distrib, conductionCurrent_sum_eq_zero, zero_add, Fin.sum_univ_three,
    d0, d1, d2]
  intro h
  linarith

/-- **Negative capacitance.** With `Cgs = -1`, `Cgd = 0`, `Cds = 1` the dynamic law still
holds along every differentiable path, while the stored energy `parasiticEnergy` is
negative at `(1, 0, 0)`. -/
lemma negativeCapacitance_negative_energy_and_kcl :
    (∀ v : ℝ → (Fin 3 → ℝ), Differentiable ℝ v → ∀ t,
      ∑ i, dynamicTerminalCurrent 3 (parasiticCharge (-1) 0 1) (conductionCurrent 1 0)
        v t i = 0) ∧
      parasiticEnergy (-1) 0 1 ![1, 0, 0] < 0 :=
  ⟨fun v hv t =>
    PhyslibExt.Electronics.SquareLawMOSParasiticCharge.sum_dynamicTerminalCurrent_eq_zero
      (-1) 0 1 1 0 v hv t,
    by norm_num [parasiticEnergy]⟩

end PhyslibExt.Electronics.SquareLawMOSParasiticCharge
