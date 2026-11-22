/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.ACInjectionLossBalance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Current-limited AC optimal power flow and its voltage lift

## i. Overview

In the bus-injection model of a finite alternating-current network, given by a
real signed incidence matrix, branch admittances and shunt admittances, the
complex power each bus supplies to the network is a quadratic function of the
complex node-voltage vector `V`. Lifting `V` to the matrix `W = V Vᴴ`, entrywise
`W a b = V a * conj (V b)`, makes every such quadratic function linear. The
lift is Hermitian and positive semidefinite, of rank at most one (the zero
vector lifts to the zero matrix, of rank zero), and it does not see a global
unit-modulus phase factor on `V`.

With the bus admittance matrix `Y`, the complex power supplied by bus `k` is
`∑ j, conj (Y k j) * W k j`. Every constraint of a current-limited optimal power
flow problem, with one aggregate generator per bus, fixed demands, box limits
on active and reactive generation, bounds on squared voltage magnitudes and
upper bounds on squared branch-current magnitudes, is a real affine constraint
`Re (trace (A * W))` in `W` for an explicit Hermitian coefficient matrix `A`,
and it is exact on lifts. A linear active-generation cost is preserved. Hence a
voltage vector is feasible for the AC problem if and only if its lift is
feasible for the semidefinite problem, with equal cost, and dropping the
rank-at-most-one condition gives a sound relaxation: every lower bound on the
semidefinite cost bounds the AC cost.

Line limits are squared current limits only; apparent-power circles and
phase-difference limits are not modeled. No voltage is recovered from an
arbitrary positive semidefinite `W`: on a two-bus network the identity matrix
is feasible for the relaxation and is the lift of no voltage vector. A
nonzero, hence rank-one, witness on the same network is AC feasible with equal costs.

The injections, branch drops and nodal power are those of
`PhyslibExt.Circuits.ACInjectionLossBalance`, in the root-mean-square
convention of `PhyslibExt.Circuits.BalancedThreePhase.complexPower`.

## ii. Key results

- `voltageLift_rank_le_one`: every lift `V Vᴴ` has rank at most one; the zero
  vector lifts to the zero matrix (`voltageLift_zero`).

- `nodeComplexPower_eq_liftedInjection`: the complex power supplied by a bus is
  the lifted injection `∑ j, conj (Y k j) * W k j` at `W = V Vᴴ`.
- `acFeasible_iff_sdpFeasible_voltageLift`: a voltage vector is AC feasible iff
  its lift is feasible for the semidefinite relaxation.
- `currentLimitedACLift_sound`: the lift of an AC-feasible point is relaxation
  feasible with the same cost, so the relaxation is sound.

## iii. Table of contents

- A. Network matrices and the optimal power flow problem
- B. The voltage lift
- C. Injections through the bus admittance matrix
- D. Hermitian coefficient matrices and real affine constraints
- E. Exactness on lifts
- F. Feasibility, cost and the sound relaxation
- G. Two-bus validation

## iv. References

- J. Lavaei and S. H. Low, "Zero duality gap in optimal power flow problems",
  *IEEE Transactions on Power Systems* 27(1) (2012), 92-107.
- S. H. Low, "Convex relaxation of optimal power flow, Part I: Formulations and
  equivalence", *IEEE Transactions on Control of Network Systems* 1(1) (2014),
  15-27.

## A. Network matrices and the optimal power flow problem
-/

@[expose] public section

open ComplexConjugate Matrix
open scoped ComplexOrder

namespace PhyslibExt.Circuits.CurrentLimitedACLift

open PhyslibExt.Circuits.ACInjectionLossBalance

/-- Bus admittance matrix of the network: `∑ e, B a e * y e * B b e` plus the shunt
admittance on the diagonal. -/
def busAdmittance (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ) (y : Fin nE → ℂ)
    (ys : Fin nN → ℂ) : Matrix (Fin nN) (Fin nN) ℂ :=
  fun a b => (∑ e : Fin nE, (B a e : ℂ) * y e * (B b e : ℂ)) + Matrix.diagonal ys a b

/-- Voltage lift `W = V Vᴴ`, entrywise `W a b = V a * conj (V b)`; of rank at most one. -/
def voltageLift (n : ℕ) (V : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec V (star V)

/-- Lifted complex injection at bus `k`: `∑ j, conj (Y k j) * W k j`. -/
def liftedInjection (n : ℕ) (Y W : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) : ℂ :=
  ∑ j : Fin n, conj (Y k j) * W k j

/-- Real Frobenius pairing `Re (trace (A * W))`, the form of every lifted constraint. -/
noncomputable def pairing (n : ℕ) (A W : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (Matrix.trace (A * W)).re

/-- Row `k` of `Y`, all other rows zero. -/
def rowSelect (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a = k then Y k b else 0

/-- Hermitian coefficient matrix of the active injection at bus `k`. -/
noncomputable def activeCoeff (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • ((rowSelect n Y k)ᴴ + rowSelect n Y k)

/-- Hermitian coefficient matrix of the reactive injection at bus `k`. -/
noncomputable def reactiveCoeff (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • ((rowSelect n Y k)ᴴ - rowSelect n Y k)

/-- Coefficient matrix of the squared voltage magnitude at bus `k`. -/
def voltageCoeff (n : ℕ) (k : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => if a = k ∧ b = k then 1 else 0

/-- Coefficient matrix of the squared current magnitude on branch `e`:
`|y e|² * B a e * B b e`. -/
noncomputable def branchCurrentCoeff (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (y : Fin nE → ℂ) (e : Fin nE) : Matrix (Fin nN) (Fin nN) ℂ :=
  fun a b => (Complex.normSq (y e) : ℂ) * ((B a e : ℂ) * (B b e : ℂ))

/-- Data of a current-limited AC optimal power flow problem: one aggregate generator per
bus with box limits, fixed demands, squared voltage-magnitude bounds, squared
branch-current limits and a linear active-generation cost. -/
structure CurrentLimitedOPF (nN nE : ℕ) where
  /-- Real signed node-branch incidence matrix. -/
  incidence : Matrix (Fin nN) (Fin nE) ℝ
  /-- Branch admittances. -/
  branchAdmittance : Fin nE → ℂ
  /-- Shunt admittances. -/
  shuntAdmittance : Fin nN → ℂ
  /-- Fixed active demand per bus. -/
  activeDemand : Fin nN → ℝ
  /-- Fixed reactive demand per bus. -/
  reactiveDemand : Fin nN → ℝ
  /-- Lower active-generation limit per bus. -/
  activeGenMin : Fin nN → ℝ
  /-- Upper active-generation limit per bus. -/
  activeGenMax : Fin nN → ℝ
  /-- Lower reactive-generation limit per bus. -/
  reactiveGenMin : Fin nN → ℝ
  /-- Upper reactive-generation limit per bus. -/
  reactiveGenMax : Fin nN → ℝ
  /-- Lower bound on the squared voltage magnitude per bus. -/
  voltageSqMin : Fin nN → ℝ
  /-- Upper bound on the squared voltage magnitude per bus. -/
  voltageSqMax : Fin nN → ℝ
  /-- Upper bound on the squared branch-current magnitude per branch. -/
  currentSqMax : Fin nE → ℝ
  /-- Linear cost coefficient of active generation per bus. -/
  costCoeff : Fin nN → ℝ

/-- Bus admittance matrix of a problem instance. -/
def CurrentLimitedOPF.admittance {nN nE : ℕ} (P : CurrentLimitedOPF nN nE) :
    Matrix (Fin nN) (Fin nN) ℂ :=
  busAdmittance nN nE P.incidence P.branchAdmittance P.shuntAdmittance

/-- AC feasibility of a voltage vector: generation `S k + Sd k` within limits, squared
voltage magnitudes within bounds, squared branch currents within limits. -/
def acFeasible (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) (V : Fin nN → ℂ) : Prop :=
  (∀ k : Fin nN,
    P.activeGenMin k ≤ (nodeComplexPower nN nE P.incidence V P.branchAdmittance
        P.shuntAdmittance k).re + P.activeDemand k ∧
      (nodeComplexPower nN nE P.incidence V P.branchAdmittance
        P.shuntAdmittance k).re + P.activeDemand k ≤ P.activeGenMax k) ∧
  (∀ k : Fin nN,
    P.reactiveGenMin k ≤ (nodeComplexPower nN nE P.incidence V P.branchAdmittance
        P.shuntAdmittance k).im + P.reactiveDemand k ∧
      (nodeComplexPower nN nE P.incidence V P.branchAdmittance
        P.shuntAdmittance k).im + P.reactiveDemand k ≤ P.reactiveGenMax k) ∧
  (∀ k : Fin nN,
    P.voltageSqMin k ≤ Complex.normSq (V k) ∧ Complex.normSq (V k) ≤ P.voltageSqMax k) ∧
  (∀ e : Fin nE,
    Complex.normSq (P.branchAdmittance e * branchDrop nN nE P.incidence V e) ≤
      P.currentSqMax e)

/-- Linear active-generation cost of a voltage vector. -/
def acCost (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) (V : Fin nN → ℂ) : ℝ :=
  ∑ k : Fin nN, P.costCoeff k *
    ((nodeComplexPower nN nE P.incidence V P.branchAdmittance P.shuntAdmittance k).re +
      P.activeDemand k)

/-- Feasibility of a matrix for the semidefinite relaxation: `W` positive semidefinite and
every constraint written as a real pairing with its coefficient matrix. No rank
constraint. -/
def sdpFeasible (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (W : Matrix (Fin nN) (Fin nN) ℂ) : Prop :=
  W.PosSemidef ∧
  (∀ k : Fin nN,
    P.activeGenMin k ≤ pairing nN (activeCoeff nN P.admittance k) W + P.activeDemand k ∧
      pairing nN (activeCoeff nN P.admittance k) W + P.activeDemand k ≤ P.activeGenMax k) ∧
  (∀ k : Fin nN,
    P.reactiveGenMin k ≤ pairing nN (reactiveCoeff nN P.admittance k) W +
        P.reactiveDemand k ∧
      pairing nN (reactiveCoeff nN P.admittance k) W + P.reactiveDemand k ≤
        P.reactiveGenMax k) ∧
  (∀ k : Fin nN,
    P.voltageSqMin k ≤ pairing nN (voltageCoeff nN k) W ∧
      pairing nN (voltageCoeff nN k) W ≤ P.voltageSqMax k) ∧
  (∀ e : Fin nE,
    pairing nN (branchCurrentCoeff nN nE P.incidence P.branchAdmittance e) W ≤
      P.currentSqMax e)

/-- Linear active-generation cost of a matrix in the relaxation. -/
noncomputable def sdpCost (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (W : Matrix (Fin nN) (Fin nN) ℂ) : ℝ :=
  ∑ k : Fin nN, P.costCoeff k * (pairing nN (activeCoeff nN P.admittance k) W +
    P.activeDemand k)

/-! ## B. The voltage lift -/

/-- Entries of the lift. -/
lemma voltageLift_apply (n : ℕ) (V : Fin n → ℂ) (a b : Fin n) :
    voltageLift n V a b = V a * conj (V b) := by
  rfl

/-- The lift is positive semidefinite. -/
lemma voltageLift_posSemidef (n : ℕ) (V : Fin n → ℂ) :
    (voltageLift n V).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star V

/-- The lift is Hermitian. -/
lemma voltageLift_isHermitian (n : ℕ) (V : Fin n → ℂ) :
    (voltageLift n V).IsHermitian :=
  (voltageLift_posSemidef n V).isHermitian

/-- The lift has rank at most one. -/
lemma voltageLift_rank_le_one (n : ℕ) (V : Fin n → ℂ) :
    (voltageLift n V).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le V (star V)

/-- The zero voltage vector lifts to the zero matrix, so a lift can have rank zero. -/
lemma voltageLift_zero (n : ℕ) : voltageLift n 0 = 0 := by
  simp [voltageLift]

/-- The lift quotients the global phase: a unit-modulus factor on every voltage leaves
`W` unchanged. -/
lemma voltageLift_unit_mul (n : ℕ) (V : Fin n → ℂ) (u : ℂ) (hu : ‖u‖ = 1) :
    voltageLift n (fun k => u * V k) = voltageLift n V := by
  have hns : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]
    norm_num
  have hu1 : u * conj u = 1 := by
    rw [Complex.mul_conj, hns]
    norm_cast
  ext a b
  simp only [voltageLift_apply, map_mul]
  calc u * V a * (conj u * conj (V b)) = u * conj u * (V a * conj (V b)) := by ring
    _ = V a * conj (V b) := by rw [hu1, one_mul]

/-! ## C. Injections through the bus admittance matrix -/

/-- The bus admittance matrix reproduces the nodal injection. -/
lemma busAdmittance_mulVec_eq_nodeInjection (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (k : Fin nN) :
    (busAdmittance nN nE B y ys *ᵥ V) k = nodeInjection nN nE B V y ys k := by
  have hdiag : (∑ j : Fin nN, Matrix.diagonal ys k j * V j) = ys k * V k := by
    simp [Matrix.diagonal_apply]
  simp only [busAdmittance, nodeInjection, branchDrop, Matrix.mulVec, dotProduct,
    add_mul, Finset.sum_add_distrib, hdiag, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Lifted injection: the complex power supplied by bus `k` is
`∑ j, conj (Y k j) * W k j` at `W = V Vᴴ`. -/
theorem nodeComplexPower_eq_liftedInjection (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (k : Fin nN) :
    nodeComplexPower nN nE B V y ys k =
      liftedInjection nN (busAdmittance nN nE B y ys) (voltageLift nN V) k := by
  unfold nodeComplexPower PhyslibExt.Circuits.BalancedThreePhase.complexPower
    liftedInjection
  rw [← busAdmittance_mulVec_eq_nodeInjection]
  simp only [voltageLift_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## D. Hermitian coefficient matrices and real affine constraints -/

private lemma re_half_add_conj (z : ℂ) : ((1 / 2 : ℂ) * (z + conj z)).re = z.re := by
  rw [Complex.add_conj]
  simp

private lemma re_div_two_I_sub_conj (z : ℂ) :
    ((1 / (2 * Complex.I)) * (z - conj z)).re = z.im := by
  rw [Complex.sub_conj]
  have h : (1 / (2 * Complex.I)) * (((2 * z.im : ℝ) : ℂ) * Complex.I) = (z.im : ℂ) := by
    push_cast
    field_simp
  rw [h, Complex.ofReal_re]

private lemma trace_rowSelect_mul (n : ℕ) (Y W : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    Matrix.trace (rowSelect n Y k * W) = ∑ j : Fin n, Y k j * W j k := by
  simp [Matrix.trace, Matrix.mul_apply, rowSelect, ite_mul]

private lemma trace_conjTranspose_rowSelect_mul (n : ℕ) (Y W : Matrix (Fin n) (Fin n) ℂ)
    (k : Fin n) :
    Matrix.trace ((rowSelect n Y k)ᴴ * W) = ∑ j : Fin n, conj (Y k j) * W k j := by
  simp [Matrix.trace, Matrix.mul_apply, rowSelect, apply_ite]

private lemma sum_row_eq_conj_liftedInjection (n : ℕ) (Y W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W.IsHermitian) (k : Fin n) :
    ∑ j : Fin n, Y k j * W j k = conj (liftedInjection n Y W k) := by
  rw [liftedInjection, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_conj, ← hW.apply k j]
  simp

/-- The pairing with a fixed coefficient matrix is real-linear in `W`. -/
lemma isLinearMap_pairing (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    IsLinearMap ℝ (fun W : Matrix (Fin n) (Fin n) ℂ => pairing n A W) := by
  refine ⟨fun X Y => ?_, fun c X => ?_⟩
  · simp only [pairing, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  · simp only [pairing, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- The active-injection coefficient matrix is Hermitian. -/
lemma activeCoeff_isHermitian (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    (activeCoeff n Y k).IsHermitian := by
  unfold Matrix.IsHermitian
  ext a b
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp [activeCoeff, rowSelect, ha, hb]
  ring

/-- The reactive-injection coefficient matrix is Hermitian. -/
lemma reactiveCoeff_isHermitian (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    (reactiveCoeff n Y k).IsHermitian := by
  unfold Matrix.IsHermitian
  ext a b
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp [reactiveCoeff, rowSelect, ha, hb]
  ring

/-- The voltage coefficient matrix is Hermitian. -/
lemma voltageCoeff_isHermitian (n : ℕ) (k : Fin n) :
    (voltageCoeff n k).IsHermitian := by
  unfold Matrix.IsHermitian
  ext a b
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp [voltageCoeff, ha, hb]

/-- The branch-current coefficient matrix is Hermitian. -/
lemma branchCurrentCoeff_isHermitian (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (y : Fin nE → ℂ) (e : Fin nE) :
    (branchCurrentCoeff nN nE B y e).IsHermitian := by
  unfold Matrix.IsHermitian
  ext a b
  simp only [conjTranspose_apply, branchCurrentCoeff, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  ring

/-- On Hermitian `W`, the real part of the lifted injection is the active pairing. -/
lemma re_liftedInjection_eq_pairing (n : ℕ) (Y W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W.IsHermitian) (k : Fin n) :
    (liftedInjection n Y W k).re = pairing n (activeCoeff n Y k) W := by
  rw [pairing, activeCoeff, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul,
    Matrix.trace_add, trace_rowSelect_mul, trace_conjTranspose_rowSelect_mul,
    sum_row_eq_conj_liftedInjection n Y W hW k, smul_eq_mul]
  exact (re_half_add_conj _).symm

/-- On Hermitian `W`, the imaginary part of the lifted injection is the reactive
pairing. -/
lemma im_liftedInjection_eq_pairing (n : ℕ) (Y W : Matrix (Fin n) (Fin n) ℂ)
    (hW : W.IsHermitian) (k : Fin n) :
    (liftedInjection n Y W k).im = pairing n (reactiveCoeff n Y k) W := by
  rw [pairing, reactiveCoeff, Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul,
    Matrix.trace_sub, trace_rowSelect_mul, trace_conjTranspose_rowSelect_mul,
    sum_row_eq_conj_liftedInjection n Y W hW k, smul_eq_mul]
  exact (re_div_two_I_sub_conj _).symm

/-- The voltage pairing reads the real diagonal entry of `W`. -/
lemma pairing_voltageCoeff (n : ℕ) (W : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) :
    pairing n (voltageCoeff n k) W = (W k k).re := by
  simp [pairing, Matrix.trace, Matrix.mul_apply, voltageCoeff, ite_and, ite_mul]

/-! ## E. Exactness on lifts -/

/-- Exact active injection on a lift. -/
lemma pairing_activeCoeff_voltageLift (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (k : Fin nN) :
    pairing nN (activeCoeff nN (busAdmittance nN nE B y ys) k) (voltageLift nN V) =
      (nodeComplexPower nN nE B V y ys k).re := by
  rw [nodeComplexPower_eq_liftedInjection]
  exact (re_liftedInjection_eq_pairing nN (busAdmittance nN nE B y ys) (voltageLift nN V)
    (voltageLift_isHermitian nN V) k).symm

/-- Exact reactive injection on a lift. -/
lemma pairing_reactiveCoeff_voltageLift (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (ys : Fin nN → ℂ) (k : Fin nN) :
    pairing nN (reactiveCoeff nN (busAdmittance nN nE B y ys) k) (voltageLift nN V) =
      (nodeComplexPower nN nE B V y ys k).im := by
  rw [nodeComplexPower_eq_liftedInjection]
  exact (im_liftedInjection_eq_pairing nN (busAdmittance nN nE B y ys) (voltageLift nN V)
    (voltageLift_isHermitian nN V) k).symm

/-- Exact squared voltage magnitude on a lift. -/
lemma pairing_voltageCoeff_voltageLift (n : ℕ) (V : Fin n → ℂ) (k : Fin n) :
    pairing n (voltageCoeff n k) (voltageLift n V) = Complex.normSq (V k) := by
  rw [pairing_voltageCoeff, voltageLift_apply, Complex.mul_conj, Complex.ofReal_re]

/-- Exact squared branch-current magnitude on a lift. -/
lemma pairing_branchCurrentCoeff_voltageLift (nN nE : ℕ) (B : Matrix (Fin nN) (Fin nE) ℝ)
    (V : Fin nN → ℂ) (y : Fin nE → ℂ) (e : Fin nE) :
    pairing nN (branchCurrentCoeff nN nE B y e) (voltageLift nN V) =
      Complex.normSq (y e * branchDrop nN nE B V e) := by
  have h : Matrix.trace (branchCurrentCoeff nN nE B y e * voltageLift nN V) =
      (Complex.normSq (y e) : ℂ) *
        (branchDrop nN nE B V e * conj (branchDrop nN nE B V e)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, branchCurrentCoeff,
      voltageLift_apply, branchDrop, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [pairing, h, Complex.mul_conj, Complex.normSq_mul, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-! ## F. Feasibility, cost and the sound relaxation -/

/-- A voltage vector is AC feasible iff its lift is feasible for the relaxation. -/
theorem acFeasible_iff_sdpFeasible_voltageLift (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (V : Fin nN → ℂ) :
    acFeasible nN nE P V ↔ sdpFeasible nN nE P (voltageLift nN V) := by
  simp only [acFeasible, sdpFeasible, CurrentLimitedOPF.admittance,
    pairing_activeCoeff_voltageLift, pairing_reactiveCoeff_voltageLift,
    pairing_voltageCoeff_voltageLift, pairing_branchCurrentCoeff_voltageLift]
  exact ⟨fun h => ⟨voltageLift_posSemidef nN V, h⟩, fun h => h.2⟩

/-- The lift preserves the linear active-generation cost. -/
lemma sdpCost_voltageLift (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) (V : Fin nN → ℂ) :
    sdpCost nN nE P (voltageLift nN V) = acCost nN nE P V := by
  simp only [sdpCost, acCost, CurrentLimitedOPF.admittance, pairing_activeCoeff_voltageLift]

/-- **Current-limited AC lift.** The lift of every AC-feasible voltage vector is
relaxation-feasible with the same cost, so every lower bound on the relaxation cost is a
lower bound on the AC cost: dropping the rank-at-most-one constraint gives a sound
relaxation. -/
theorem currentLimitedACLift_sound (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) :
    (∀ V : Fin nN → ℂ, acFeasible nN nE P V →
      sdpFeasible nN nE P (voltageLift nN V) ∧
        sdpCost nN nE P (voltageLift nN V) = acCost nN nE P V) ∧
    (∀ L : ℝ, (∀ W : Matrix (Fin nN) (Fin nN) ℂ, sdpFeasible nN nE P W → L ≤ sdpCost nN nE P W) →
      ∀ V : Fin nN → ℂ, acFeasible nN nE P V → L ≤ acCost nN nE P V) := by
  refine ⟨fun V hV => ⟨(acFeasible_iff_sdpFeasible_voltageLift nN nE P V).mp hV,
    sdpCost_voltageLift nN nE P V⟩, fun L hL V hV => ?_⟩
  rw [← sdpCost_voltageLift]
  exact hL _ ((acFeasible_iff_sdpFeasible_voltageLift nN nE P V).mp hV)

/-- Bundled contract: lift PSD, Hermitian coefficient matrices with real-linear pairings,
lifted injection formula, exactness of every constraint on lifts, and the sound
relaxation. -/
lemma currentLimitedACLift_spec (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) :
    (∀ V : Fin nN → ℂ, (voltageLift nN V).PosSemidef) ∧
    (∀ A : Matrix (Fin nN) (Fin nN) ℂ,
      IsLinearMap ℝ (fun W : Matrix (Fin nN) (Fin nN) ℂ => pairing nN A W)) ∧
    (∀ k : Fin nN, (activeCoeff nN P.admittance k).IsHermitian ∧
      (reactiveCoeff nN P.admittance k).IsHermitian ∧ (voltageCoeff nN k).IsHermitian) ∧
    (∀ e : Fin nE,
      (branchCurrentCoeff nN nE P.incidence P.branchAdmittance e).IsHermitian) ∧
    (∀ (V : Fin nN → ℂ) (k : Fin nN),
      nodeComplexPower nN nE P.incidence V P.branchAdmittance P.shuntAdmittance k =
        liftedInjection nN P.admittance (voltageLift nN V) k) ∧
    (∀ V : Fin nN → ℂ, acFeasible nN nE P V ↔ sdpFeasible nN nE P (voltageLift nN V)) ∧
    (∀ V : Fin nN → ℂ, sdpCost nN nE P (voltageLift nN V) = acCost nN nE P V) ∧
    (∀ L : ℝ, (∀ W : Matrix (Fin nN) (Fin nN) ℂ, sdpFeasible nN nE P W → L ≤ sdpCost nN nE P W) →
      ∀ V : Fin nN → ℂ, acFeasible nN nE P V → L ≤ acCost nN nE P V) :=
  ⟨voltageLift_posSemidef nN, isLinearMap_pairing nN,
    fun k => ⟨activeCoeff_isHermitian nN P.admittance k,
      reactiveCoeff_isHermitian nN P.admittance k, voltageCoeff_isHermitian nN k⟩,
    fun e => branchCurrentCoeff_isHermitian nN nE P.incidence P.branchAdmittance e,
    fun V k => nodeComplexPower_eq_liftedInjection nN nE P.incidence V P.branchAdmittance
      P.shuntAdmittance k,
    acFeasible_iff_sdpFeasible_voltageLift nN nE P, sdpCost_voltageLift nN nE P,
    (currentLimitedACLift_sound nN nE P).2⟩

/-! ## G. Two-bus validation -/

/-- Two buses joined by one unit-conductance branch, no shunts, zero demand, loose limits,
unit cost per bus. -/
noncomputable def twoBusExample : CurrentLimitedOPF 2 1 where
  incidence := Matrix.of ![![1], ![-1]]
  branchAdmittance := fun _ => 1
  shuntAdmittance := fun _ => 0
  activeDemand := fun _ => 0
  reactiveDemand := fun _ => 0
  activeGenMin := fun _ => -2
  activeGenMax := fun _ => 2
  reactiveGenMin := fun _ => -1
  reactiveGenMax := fun _ => 1
  voltageSqMin := fun _ => 1 / 8
  voltageSqMax := fun _ => 2
  currentSqMax := fun _ => 4
  costCoeff := fun _ => 1

/-- Two-bus rank-one witness: `V = (1, 1/2)` is AC feasible, its lift is
relaxation-feasible, and both costs are `1/4`. -/
lemma twoBus_rankOne_witness :
    acFeasible 2 1 twoBusExample ![1, 1 / 2] ∧
      sdpFeasible 2 1 twoBusExample (voltageLift 2 ![1, 1 / 2]) ∧
      acCost 2 1 twoBusExample ![1, 1 / 2] = 1 / 4 ∧
      sdpCost 2 1 twoBusExample (voltageLift 2 ![1, 1 / 2]) = 1 / 4 := by
  have hS0re : (nodeComplexPower 2 1 twoBusExample.incidence ![1, 1 / 2]
      twoBusExample.branchAdmittance twoBusExample.shuntAdmittance 0).re = 1 / 2 := by
    simp [twoBusExample, nodeComplexPower,
      PhyslibExt.Circuits.BalancedThreePhase.complexPower, nodeInjection, branchDrop,
      Fin.sum_univ_two, Matrix.of_apply]
    norm_num
  have hS0im : (nodeComplexPower 2 1 twoBusExample.incidence ![1, 1 / 2]
      twoBusExample.branchAdmittance twoBusExample.shuntAdmittance 0).im = 0 := by
    simp [twoBusExample, nodeComplexPower,
      PhyslibExt.Circuits.BalancedThreePhase.complexPower, nodeInjection, branchDrop,
      Fin.sum_univ_two, Matrix.of_apply]
  have hS1re : (nodeComplexPower 2 1 twoBusExample.incidence ![1, 1 / 2]
      twoBusExample.branchAdmittance twoBusExample.shuntAdmittance 1).re = -1 / 4 := by
    simp [twoBusExample, nodeComplexPower,
      PhyslibExt.Circuits.BalancedThreePhase.complexPower, nodeInjection, branchDrop,
      Fin.sum_univ_two, Matrix.of_apply]
    norm_num
  have hS1im : (nodeComplexPower 2 1 twoBusExample.incidence ![1, 1 / 2]
      twoBusExample.branchAdmittance twoBusExample.shuntAdmittance 1).im = 0 := by
    simp [twoBusExample, nodeComplexPower,
      PhyslibExt.Circuits.BalancedThreePhase.complexPower, nodeInjection, branchDrop,
      Fin.sum_univ_two, Matrix.of_apply]
  have hac : acFeasible 2 1 twoBusExample ![1, 1 / 2] := by
    simp only [acFeasible, Fin.forall_fin_two, Fin.forall_fin_one]
    rw [hS0re, hS1re, hS0im, hS1im]
    simp [twoBusExample, branchDrop, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  have hacCost : acCost 2 1 twoBusExample ![1, 1 / 2] = 1 / 4 := by
    simp only [acCost, Fin.sum_univ_two]
    rw [hS0re, hS1re]
    simp [twoBusExample]
    norm_num
  refine ⟨hac, (acFeasible_iff_sdpFeasible_voltageLift 2 1 twoBusExample _).mp hac, hacCost,
    ?_⟩
  rw [sdpCost_voltageLift]
  exact hacCost

/-- A rank-two PSD matrix (the identity) is relaxation-feasible but is the lift of no
voltage vector. -/
lemma twoBus_rankTwo_relaxed_not_lift :
    sdpFeasible 2 1 twoBusExample (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      ∀ V : Fin 2 → ℂ, voltageLift 2 V ≠ 1 := by
  have hY : ∀ k : Fin 2, twoBusExample.admittance k k = 1 := by
    intro k
    fin_cases k <;>
      simp [CurrentLimitedOPF.admittance, busAdmittance, twoBusExample, Matrix.diagonal]
  have hL : ∀ k : Fin 2, liftedInjection 2 twoBusExample.admittance 1 k = 1 := by
    intro k
    simp [liftedInjection, Matrix.one_apply, hY]
  have hsdp : sdpFeasible 2 1 twoBusExample (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    refine ⟨Matrix.PosSemidef.one, fun k => ?_, fun k => ?_, fun k => ?_, fun e => ?_⟩
    · rw [← re_liftedInjection_eq_pairing 2 _ 1 Matrix.isHermitian_one, hL]
      norm_num [twoBusExample]
    · rw [← im_liftedInjection_eq_pairing 2 _ 1 Matrix.isHermitian_one, hL]
      norm_num [twoBusExample]
    · rw [pairing_voltageCoeff]
      norm_num [twoBusExample]
    · fin_cases e
      norm_num [twoBusExample, pairing, branchCurrentCoeff, Matrix.trace, Fin.sum_univ_two]
  refine ⟨hsdp, fun V hV => ?_⟩
  have h00 := congrFun (congrFun hV 0) 0
  have h01 := congrFun (congrFun hV 0) 1
  have h11 := congrFun (congrFun hV 1) 1
  rw [voltageLift_apply, Matrix.one_apply_eq] at h00 h11
  rw [voltageLift_apply, Matrix.one_apply_ne (by decide)] at h01
  rcases mul_eq_zero.mp h01 with hz | hz
  · rw [hz, zero_mul] at h00
    exact zero_ne_one h00
  · rw [hz, mul_zero] at h11
    exact zero_ne_one h11

end PhyslibExt.Circuits.CurrentLimitedACLift
