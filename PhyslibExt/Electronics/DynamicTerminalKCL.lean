/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.TerminalChargeJacobian
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.NormNum

/-!
# Dynamic terminal Kirchhoff current law

## i. Overview

A charge-based compact device model gives each terminal a static
conduction current `iCond_i(v)` and a terminal charge `q_i(v)`. Along a
voltage trajectory `v(t)`, the current entering terminal `i` is the
static current plus the displacement current `d/dt q_i(v(t))`. This
file derives Kirchhoff's current law for these dynamic currents: if
total terminal charge and total static current both vanish on an open
voltage domain, the dynamic terminal currents sum to zero at every
time. The law is a theorem, not a field of the model. The proof runs
through the chain rule and the zero Jacobian column sums of a
charge-conserving map. A leaking static current breaks the
conclusion, and a two-terminal capacitor shows nonzero individual
displacement currents with zero total.

## ii. Key results

- `sum_displacementCurrent_eq_zero`: conserved terminal charge makes
  the displacement currents sum to zero along any differentiable
  trajectory in the domain.
- `sum_dynamicTerminalCurrent_eq_zero`: separately conserved charge
  and static current give the dynamic Kirchhoff current law.

## iii. Table of contents

- A. Dynamic terminal currents
- A.1 Displacement currents
- A.2 Dynamic Kirchhoff current law
- A.3 A two-terminal capacitor

## iv. References

- Y. Tsividis and C. McAndrew, *Operation and Modeling of the MOS
  Transistor*, third edition, Oxford University Press, 2011:
  charge-based quasi-static modeling, where each terminal current is a
  transport current plus the time derivative of the terminal charge,
  and charge conservation makes the terminal currents sum to zero.

## A. Dynamic terminal currents

-/

@[expose] public section

namespace PhyslibExt.Electronics.DynamicTerminalKCL

open MetaMathlibExt PhyslibExt.Electronics.TerminalChargeJacobian

/-- The displacement current of terminal `i` along a voltage trajectory `v`: the time
derivative `d/dt q_i(v(t))` of its terminal charge. -/
noncomputable def displacementCurrent (n : ℕ) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (v : ℝ → (Fin n → ℝ)) (t : ℝ) (i : Fin n) : ℝ :=
  deriv (fun s => q (v s) i) t

/-- The dynamic terminal current of terminal `i`: static conduction current plus
displacement current. It is defined from the two maps, not taken as a model field. -/
noncomputable def dynamicTerminalCurrent (n : ℕ) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (iCond : (Fin n → ℝ) → (Fin n → ℝ)) (v : ℝ → (Fin n → ℝ)) (t : ℝ) (i : Fin n) : ℝ :=
  iCond (v t) i + displacementCurrent n q v t i

/-! ### A.1 Displacement currents -/

/-- The derivative of total charge along the trajectory is the sum of the displacement
currents, when each charge component along the trajectory is differentiable at `t`. -/
lemma deriv_totalCharge_eq_sum_displacementCurrent (n : ℕ)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (v : ℝ → (Fin n → ℝ)) (t : ℝ)
    (hq : ∀ i, DifferentiableAt ℝ (fun s => q (v s) i) t) :
    deriv (fun s => ∑ i, q (v s) i) t = ∑ i, displacementCurrent n q v t i := by
  unfold displacementCurrent
  exact deriv_fun_sum fun i _ => hq i

/-- Chain rule: a displacement current is the Jacobian row of the charge map at `v t`
applied to the trajectory velocity. -/
lemma displacementCurrent_eq_jacobian_mulVec (n : ℕ)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (v : ℝ → (Fin n → ℝ)) (t : ℝ)
    (hq : DifferentiableAt ℝ q (v t)) (hv : DifferentiableAt ℝ v t) (i : Fin n) :
    displacementCurrent n q v t i =
      ∑ j, jacobianMatrix q (v t) i j * (deriv v t) j := by
  have hc : HasDerivAt (q ∘ v) (fderiv ℝ q (v t) (deriv v t)) t :=
    hq.hasFDerivAt.comp_hasDerivAt t hv.hasDerivAt
  have hi : HasDerivAt (fun s => q (v s) i) (fderiv ℝ q (v t) (deriv v t) i) t :=
    (hasFDerivAt_apply i ((q ∘ v) t)).comp_hasDerivAt t hc
  unfold displacementCurrent
  rw [hi.deriv]
  have hmv := congrFun (jacobianMatrix_mulVec_eq_fderiv q (v t) hq (deriv v t)) i
  simp only [Matrix.mulVec, dotProduct] at hmv
  exact hmv.symm

/-- The summed displacement current is the Jacobian column sums contracted with the
trajectory velocity. -/
lemma sum_displacementCurrent_eq_sum_jacobian (n : ℕ)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (v : ℝ → (Fin n → ℝ)) (t : ℝ)
    (hq : DifferentiableAt ℝ q (v t)) (hv : DifferentiableAt ℝ v t) :
    ∑ i, displacementCurrent n q v t i =
      ∑ j, (∑ i, jacobianMatrix q (v t) i j) * (deriv v t) j := by
  simp only [displacementCurrent_eq_jacobian_mulVec n q v t hq hv, Finset.sum_mul]
  exact Finset.sum_comm

/-- **Zero total displacement current.** Along a differentiable trajectory inside an open
domain on which the terminal charges are differentiable and sum to zero, the displacement
currents sum to zero at every time: the zero Jacobian column sums of a charge-conserving map
annihilate the trajectory velocity. -/
theorem sum_displacementCurrent_eq_zero (n : ℕ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (hq : ∀ i, DifferentiableOn ℝ (fun w => q w i) U)
    (hcons : ∀ w ∈ U, ∑ i, q w i = 0) (v : ℝ → (Fin n → ℝ)) (hv : Differentiable ℝ v)
    (hvU : ∀ t, v t ∈ U) (t : ℝ) :
    ∑ i, displacementCurrent n q v t i = 0 := by
  have hqD : DifferentiableAt ℝ q (v t) :=
    differentiableAt_pi.mpr fun i => (hq i).differentiableAt (hU.mem_nhds (hvU t))
  rw [sum_displacementCurrent_eq_sum_jacobian n q v t hqD (hv t)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jacobian_col_sum_eq_zero_of_charge_conservation n U hU q hq hcons (v t) (hvU t) j,
    zero_mul]

/-- The derivative of total charge along the trajectory is zero, under the hypotheses of
`sum_displacementCurrent_eq_zero`. -/
lemma deriv_totalCharge_eq_zero (n : ℕ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (hq : ∀ i, DifferentiableOn ℝ (fun w => q w i) U)
    (hcons : ∀ w ∈ U, ∑ i, q w i = 0) (v : ℝ → (Fin n → ℝ)) (hv : Differentiable ℝ v)
    (hvU : ∀ t, v t ∈ U) (t : ℝ) :
    deriv (fun s => ∑ i, q (v s) i) t = 0 := by
  have hd : ∀ i, DifferentiableAt ℝ (fun s => q (v s) i) t := fun i =>
    ((hq i).differentiableAt (hU.mem_nhds (hvU t))).comp t (hv t)
  rw [deriv_totalCharge_eq_sum_displacementCurrent n q v t hd]
  exact sum_displacementCurrent_eq_zero n U hU q hq hcons v hv hvU t

/-! ### A.2 Dynamic Kirchhoff current law -/

/-- Under charge conservation alone, the summed dynamic current equals the summed static
conduction current at the trajectory voltage. -/
lemma sum_dynamicTerminalCurrent_eq_static (n : ℕ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (hq : ∀ i, DifferentiableOn ℝ (fun w => q w i) U)
    (hcons : ∀ w ∈ U, ∑ i, q w i = 0) (iCond : (Fin n → ℝ) → (Fin n → ℝ))
    (v : ℝ → (Fin n → ℝ)) (hv : Differentiable ℝ v) (hvU : ∀ t, v t ∈ U) (t : ℝ) :
    ∑ i, dynamicTerminalCurrent n q iCond v t i = ∑ i, iCond (v t) i := by
  simp only [dynamicTerminalCurrent, Finset.sum_add_distrib,
    sum_displacementCurrent_eq_zero n U hU q hq hcons v hv hvU t, add_zero]

/-- **Dynamic terminal Kirchhoff current law.** Along a differentiable voltage trajectory
inside an open domain, separately conserved terminal charge and separately conserved static
conduction current make the dynamic terminal currents sum to zero at every time. -/
theorem sum_dynamicTerminalCurrent_eq_zero (n : ℕ) (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (q : (Fin n → ℝ) → (Fin n → ℝ)) (hq : ∀ i, DifferentiableOn ℝ (fun w => q w i) U)
    (hcons : ∀ w ∈ U, ∑ i, q w i = 0) (iCond : (Fin n → ℝ) → (Fin n → ℝ))
    (hstatic : ∀ w ∈ U, ∑ i, iCond w i = 0) (v : ℝ → (Fin n → ℝ))
    (hv : Differentiable ℝ v) (hvU : ∀ t, v t ∈ U) (t : ℝ) :
    ∑ i, dynamicTerminalCurrent n q iCond v t i = 0 := by
  rw [sum_dynamicTerminalCurrent_eq_static n U hU q hq hcons iCond v hv hvU t]
  exact hstatic _ (hvU t)

/-- Violated premise (static leak): with conserved charge, a nonzero summed static current at
the trajectory voltage makes the summed dynamic current nonzero. -/
lemma sum_dynamicTerminalCurrent_ne_zero_of_static_ne (n : ℕ) (U : Set (Fin n → ℝ))
    (hU : IsOpen U) (q : (Fin n → ℝ) → (Fin n → ℝ))
    (hq : ∀ i, DifferentiableOn ℝ (fun w => q w i) U) (hcons : ∀ w ∈ U, ∑ i, q w i = 0)
    (iCond : (Fin n → ℝ) → (Fin n → ℝ)) (v : ℝ → (Fin n → ℝ)) (hv : Differentiable ℝ v)
    (hvU : ∀ t, v t ∈ U) (t : ℝ) (hleak : ∑ i, iCond (v t) i ≠ 0) :
    ∑ i, dynamicTerminalCurrent n q iCond v t i ≠ 0 := by
  rw [sum_dynamicTerminalCurrent_eq_static n U hU q hq hcons iCond v hv hvU t]
  exact hleak

/-! ### A.3 A two-terminal capacitor -/

/-- On the capacitor charge map `w ↦ (w 0 - w 1, w 1 - w 0)` along `s ↦ (s, 0)`, the
displacement current of terminal `0` is `1` at every time. -/
lemma displacementCurrent_capacitor_zero (t : ℝ) :
    displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
      (fun s : ℝ => ![s, 0]) t 0 = 1 := by
  have hf : (fun s : ℝ => (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
      ((fun s : ℝ => ![s, (0 : ℝ)]) s) 0) = fun s : ℝ => s := by
    funext s
    simp
  unfold displacementCurrent
  rw [hf]
  simp

/-- On the same capacitor and trajectory, the displacement current of terminal `1` is `-1`
at every time. -/
lemma displacementCurrent_capacitor_one (t : ℝ) :
    displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
      (fun s : ℝ => ![s, 0]) t 1 = -1 := by
  have hf : (fun s : ℝ => (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
      ((fun s : ℝ => ![s, (0 : ℝ)]) s) 1) = fun s : ℝ => -s := by
    funext s
    simp
  unfold displacementCurrent
  rw [hf]
  simp

/-- Validation, nonzero displacement currents: with zero static current, the capacitor's
displacement currents at time `0` are `1` and `-1`, and its dynamic currents sum to zero. -/
lemma displacement_pairwise_example :
    displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
        (fun s : ℝ => ![s, 0]) 0 0 = 1 ∧
      displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
        (fun s : ℝ => ![s, 0]) 0 1 = -1 ∧
      ∑ i, dynamicTerminalCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
        (fun _ => 0) (fun s : ℝ => ![s, 0]) 0 i = 0 := by
  refine ⟨displacementCurrent_capacitor_zero 0, displacementCurrent_capacitor_one 0, ?_⟩
  simp only [Fin.sum_univ_two, dynamicTerminalCurrent, displacementCurrent_capacitor_zero,
    displacementCurrent_capacitor_one]
  norm_num

/-- Validation at every time: the capacitor has zero summed dynamic current at every time,
although its individual displacement currents are nonzero. -/
lemma sum_dynamic_pairwise_example (t : ℝ) :
    ∑ i, dynamicTerminalCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
        (fun _ => 0) (fun s : ℝ => ![s, (0 : ℝ)]) t i = 0 ∧
      displacementCurrent 2 (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 1 - w 0])
        (fun s : ℝ => ![s, (0 : ℝ)]) t 0 ≠ 0 := by
  refine ⟨?_, by rw [displacementCurrent_capacitor_zero t]; norm_num⟩
  simp only [Fin.sum_univ_two, dynamicTerminalCurrent, displacementCurrent_capacitor_zero,
    displacementCurrent_capacitor_one]
  norm_num

end PhyslibExt.Electronics.DynamicTerminalKCL
