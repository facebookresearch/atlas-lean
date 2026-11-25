/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.CurrentLimitedACLift
public import MathlibExt.Analysis.Convex.FactoredSDPLowerBound

/-!
# Dual optimality certificates for current-limited AC optimal power flow

## i. Overview

The semidefinite relaxation of a current-limited AC optimal power flow problem
(`PhyslibExt.Circuits.CurrentLimitedACLift`) minimizes a linear cost over Hermitian
positive semidefinite matrices `W` subject to real affine constraints. Written in factored
form, the objective is `Re (trace (C * W)) + c0` with `C = ∑ k, costCoeff k • activeCoeff k`
and `c0 = ∑ k, costCoeff k * activeDemand k`, and the constraints are `6 * nN + nE`
inequalities `Re (trace (A i * W)) ≤ b i`: upper and lower active and reactive generation
limits and upper and lower squared voltage limits at every bus, and the squared
branch-current limit on every branch. There are no equality constraints; a fixed
generation is the pair of inequalities `g ≤ P ≤ g`.

A dual certificate is one nonnegative multiplier per inequality together with a complex
factor `F` such that the dual slack matrix `C + ∑ i, λ i • A i` equals `F * Fᴴ`. By the
factored semidefinite lower bound
(`MathlibExt.Analysis.Convex.FactoredSDPLowerBound.factored_certificate_lower_bound`), the
certified value `c0 - ∑ i, λ i * b i` bounds the relaxation cost from below. Since the lift
`V Vᴴ` of an AC-feasible voltage is relaxation feasible with the same cost, the same value
bounds the AC cost. If a supplied AC-feasible voltage attains the certified value, it is a
global minimizer of the AC problem and its lift minimizes the relaxation. No voltage is
recovered from any other relaxed point.

A stationary point of the nonlinear problem is not a certificate. On a two-bus network an
AC-feasible voltage with a stationary Lagrangian and a would-be bound equal to its own cost
has a negative multiplier and a dual slack with a negative diagonal entry, and it is not
optimal. A DC power flow solution is not AC feasible in general, and the nonlinear AC
Karush-Kuhn-Tucker conditions are not sufficient for global optimality; neither is used.

## ii. Key results

- `certifiedLowerBound_le_sdpCost`: under the sign check and the exact factorization, the
  certified value bounds the cost of every relaxation-feasible matrix.
- `certifiedLowerBound_le_acCost`: the same value bounds the cost of every AC-feasible
  voltage.
- `acOptimal_of_acCost_eq_certifiedLowerBound`: a supplied AC-feasible voltage attaining
  the certified value is globally optimal.
- `acVoltageCertificate_correct`: the three statements above together.
- `twoBus_certificate_exact`, `twoBus_relaxedPoint_not_lift`,
  `twoBus_stationaryPoint_not_certificate`: a two-bus exact certificate with bound `3/2`
  attained at `V = (2, 5/4)`, a relaxed point that is bounded but is not a lift, and a
  stationary point that is not a certificate.

## iii. Table of contents

- A. The lifted problem in factored-certificate form
- B. Dual certificates
- C. Translation into the factored-certificate form
- D. Soundness and optimality
- E. Two-bus validation

## iv. References

- J. Lavaei and S. H. Low, "Zero duality gap in optimal power flow problems",
  *IEEE Transactions on Power Systems* 27(1) (2012), 92-107.
- L. Vandenberghe and S. Boyd, "Semidefinite programming", *SIAM Review* 38(1) (1996),
  49-95.
-/

@[expose] public section

open ComplexConjugate Matrix
open scoped ComplexOrder

namespace PhyslibExt.Circuits.ACVoltageCertificate

open PhyslibExt.Circuits.ACInjectionLossBalance
open PhyslibExt.Circuits.CurrentLimitedACLift

/-! ## A. The lifted problem in factored-certificate form -/

/-- Objective matrix of the relaxation: `C = ∑ k, costCoeff k • activeCoeff k`. -/
noncomputable def objectiveMatrix (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) :
    Matrix (Fin nN) (Fin nN) ℂ :=
  ∑ k : Fin nN, (P.costCoeff k : ℂ) • activeCoeff nN P.admittance k

/-- Constant term of the relaxation objective: `c0 = ∑ k, costCoeff k * activeDemand k`. -/
def objectiveOffset (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) : ℝ :=
  ∑ k : Fin nN, P.costCoeff k * P.activeDemand k

/-- Coefficient matrix of each inequality of the relaxation, written as
`Re (trace (A * W)) ≤ b`. For bus `k` the six groups are: upper active limit, lower active
limit, upper reactive limit, lower reactive limit, upper squared voltage limit, lower
squared voltage limit; then one squared current limit per branch. -/
noncomputable def constraintCoeff (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) :
    (Fin 6 × Fin nN) ⊕ Fin nE → Matrix (Fin nN) (Fin nN) ℂ
  | Sum.inl (g, k) =>
      ![activeCoeff nN P.admittance k, -activeCoeff nN P.admittance k,
        reactiveCoeff nN P.admittance k, -reactiveCoeff nN P.admittance k,
        voltageCoeff nN k, -voltageCoeff nN k] g
  | Sum.inr e => branchCurrentCoeff nN nE P.incidence P.branchAdmittance e

/-- Right-hand side of each inequality of the relaxation, in the order of
`constraintCoeff`. -/
def constraintBound (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) :
    (Fin 6 × Fin nN) ⊕ Fin nE → ℝ
  | Sum.inl (g, k) =>
      ![P.activeGenMax k - P.activeDemand k, P.activeDemand k - P.activeGenMin k,
        P.reactiveGenMax k - P.reactiveDemand k, P.reactiveDemand k - P.reactiveGenMin k,
        P.voltageSqMax k, -P.voltageSqMin k] g
  | Sum.inr e => P.currentSqMax e

/-- Enumeration of the inequalities by `Fin (6 * nN + nE)`, the index type of the factored
certificate bound. -/
def constraintIndex (nN nE : ℕ) : (Fin 6 × Fin nN) ⊕ Fin nE ≃ Fin (6 * nN + nE) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin nE))).trans finSumFinEquiv

/-- Inequality coefficient matrices indexed by `Fin (6 * nN + nE)`. -/
noncomputable def liftedCoeff (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (i : Fin (6 * nN + nE)) : Matrix (Fin nN) (Fin nN) ℂ :=
  constraintCoeff nN nE P ((constraintIndex nN nE).symm i)

/-- Inequality right-hand sides indexed by `Fin (6 * nN + nE)`. -/
def liftedBound (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) (i : Fin (6 * nN + nE)) : ℝ :=
  constraintBound nN nE P ((constraintIndex nN nE).symm i)

/-! ## B. Dual certificates -/

/-- A dual witness for the current-limited OPF relaxation: one real multiplier for every
inequality and a complex factor of width `k` for the dual slack matrix. Nonnegativity and
the factorization are separate hypotheses (`ACDualCertificate.Nonneg`, `dualSlack`). -/
structure ACDualCertificate (nN nE k : ℕ) where
  /-- Multiplier of the upper active-generation limit at each bus. -/
  activeMaxMult : Fin nN → ℝ
  /-- Multiplier of the lower active-generation limit at each bus. -/
  activeMinMult : Fin nN → ℝ
  /-- Multiplier of the upper reactive-generation limit at each bus. -/
  reactiveMaxMult : Fin nN → ℝ
  /-- Multiplier of the lower reactive-generation limit at each bus. -/
  reactiveMinMult : Fin nN → ℝ
  /-- Multiplier of the upper squared-voltage limit at each bus. -/
  voltageMaxMult : Fin nN → ℝ
  /-- Multiplier of the lower squared-voltage limit at each bus. -/
  voltageMinMult : Fin nN → ℝ
  /-- Multiplier of the squared branch-current limit on each branch. -/
  currentMult : Fin nE → ℝ
  /-- Factor `F` of the dual slack matrix `F * Fᴴ`. -/
  factor : Matrix (Fin nN) (Fin k) ℂ

/-- The sign check: every multiplier is nonnegative. -/
def ACDualCertificate.Nonneg {nN nE k : ℕ} (cert : ACDualCertificate nN nE k) : Prop :=
  (∀ b : Fin nN, 0 ≤ cert.activeMaxMult b ∧ 0 ≤ cert.activeMinMult b ∧
    0 ≤ cert.reactiveMaxMult b ∧ 0 ≤ cert.reactiveMinMult b ∧
    0 ≤ cert.voltageMaxMult b ∧ 0 ≤ cert.voltageMinMult b) ∧
  ∀ e : Fin nE, 0 ≤ cert.currentMult e

/-- Multipliers in the order of `constraintCoeff`. -/
def ACDualCertificate.multiplier {nN nE k : ℕ} (cert : ACDualCertificate nN nE k) :
    (Fin 6 × Fin nN) ⊕ Fin nE → ℝ
  | Sum.inl (g, b) =>
      ![cert.activeMaxMult b, cert.activeMinMult b, cert.reactiveMaxMult b,
        cert.reactiveMinMult b, cert.voltageMaxMult b, cert.voltageMinMult b] g
  | Sum.inr e => cert.currentMult e

/-- Multipliers indexed by `Fin (6 * nN + nE)`. -/
def liftedMultiplier (nN nE k : ℕ) (cert : ACDualCertificate nN nE k)
    (i : Fin (6 * nN + nE)) : ℝ :=
  cert.multiplier ((constraintIndex nN nE).symm i)

/-- Dual slack matrix `C + ∑ λ A` of a certificate, grouped by physical quantity. -/
noncomputable def dualSlack (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) : Matrix (Fin nN) (Fin nN) ℂ :=
  objectiveMatrix nN nE P +
    ∑ b : Fin nN, ((cert.activeMaxMult b - cert.activeMinMult b : ℝ) : ℂ) •
      activeCoeff nN P.admittance b +
    ∑ b : Fin nN, ((cert.reactiveMaxMult b - cert.reactiveMinMult b : ℝ) : ℂ) •
      reactiveCoeff nN P.admittance b +
    ∑ b : Fin nN, ((cert.voltageMaxMult b - cert.voltageMinMult b : ℝ) : ℂ) •
      voltageCoeff nN b +
    ∑ e : Fin nE, (cert.currentMult e : ℂ) •
      branchCurrentCoeff nN nE P.incidence P.branchAdmittance e

/-- Certified lower bound `c0 - ∑ λ b` of a certificate, grouped by physical quantity. -/
def certifiedLowerBound (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) : ℝ :=
  objectiveOffset nN nE P -
    ∑ b : Fin nN, (cert.activeMaxMult b * (P.activeGenMax b - P.activeDemand b) +
      cert.activeMinMult b * (P.activeDemand b - P.activeGenMin b) +
      cert.reactiveMaxMult b * (P.reactiveGenMax b - P.reactiveDemand b) +
      cert.reactiveMinMult b * (P.reactiveDemand b - P.reactiveGenMin b) +
      cert.voltageMaxMult b * P.voltageSqMax b -
      cert.voltageMinMult b * P.voltageSqMin b) -
    ∑ e : Fin nE, cert.currentMult e * P.currentSqMax e

/-! ## C. Translation into the factored-certificate form -/

/-- The objective matrix is Hermitian. -/
lemma objectiveMatrix_isHermitian (nN nE : ℕ) (P : CurrentLimitedOPF nN nE) :
    (objectiveMatrix nN nE P).IsHermitian := by
  rw [Matrix.IsHermitian, objectiveMatrix, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_smul, (activeCoeff_isHermitian nN P.admittance k).eq]
  simp

/-- Every inequality coefficient matrix is Hermitian. -/
lemma liftedCoeff_isHermitian (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (i : Fin (6 * nN + nE)) : (liftedCoeff nN nE P i).IsHermitian := by
  unfold liftedCoeff
  rcases (constraintIndex nN nE).symm i with ⟨g, b⟩ | e
  · fin_cases g
    · exact activeCoeff_isHermitian _ _ _
    · exact (activeCoeff_isHermitian _ _ _).neg
    · exact reactiveCoeff_isHermitian _ _ _
    · exact (reactiveCoeff_isHermitian _ _ _).neg
    · exact voltageCoeff_isHermitian _ _
    · exact (voltageCoeff_isHermitian _ _).neg
  · exact branchCurrentCoeff_isHermitian _ _ _ _ _

/-- The relaxation cost is the factored-form objective `Re (trace (C * W)) + c0`, for every
matrix `W`. -/
lemma sdpCost_eq_objective (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (W : Matrix (Fin nN) (Fin nN) ℂ) :
    sdpCost nN nE P W = ((objectiveMatrix nN nE P * W).trace).re + objectiveOffset nN nE P := by
  simp only [sdpCost, objectiveMatrix, objectiveOffset, pairing, Finset.sum_mul,
    Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, mul_add, Finset.sum_add_distrib]

/-- Relaxation feasibility is exactly the factored-form feasibility: `W` positive
semidefinite and every enumerated inequality `Re (trace (A i * W)) ≤ b i`. -/
lemma sdpFeasible_iff_lifted (nN nE : ℕ) (P : CurrentLimitedOPF nN nE)
    (W : Matrix (Fin nN) (Fin nN) ℂ) :
    sdpFeasible nN nE P W ↔
      W.PosSemidef ∧ ∀ i, ((liftedCoeff nN nE P i * W).trace).re ≤ liftedBound nN nE P i := by
  have hall : (∀ i, ((liftedCoeff nN nE P i * W).trace).re ≤ liftedBound nN nE P i) ↔
      ∀ s, ((constraintCoeff nN nE P s * W).trace).re ≤ constraintBound nN nE P s :=
    ⟨fun h s => by simpa [liftedCoeff, liftedBound] using h (constraintIndex nN nE s),
      fun h i => h _⟩
  rw [hall, sdpFeasible]
  simp only [Sum.forall, Prod.forall, Fin.forall_fin_succ, constraintCoeff, constraintBound]
  simp only [pairing, forall_and, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_zero,
    Fin.succ_zero_eq_one, cons_val_one, neg_mul, trace_neg, Complex.neg_re,
    neg_le_sub_iff_le_add, Fin.succ_one_eq_two, cons_val, Fin.reduceSucc, neg_le_neg_iff,
    cons_val_succ, cons_val_fin_one, IsEmpty.forall_iff, and_true, and_congr_right_iff]
  refine fun _ => ⟨fun ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7⟩ =>
      ⟨⟨fun b => by linarith [h2 b], fun b => by linarith [h1 b], fun b => by linarith [h4 b],
        fun b => by linarith [h3 b], h6, h5⟩, h7⟩,
    fun ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ =>
      ⟨⟨fun b => by linarith [h2 b], fun b => by linarith [h1 b]⟩,
        ⟨fun b => by linarith [h4 b], fun b => by linarith [h3 b]⟩, ⟨h6, h5⟩, h7⟩⟩

/-- The sign check gives nonnegative enumerated multipliers. -/
lemma liftedMultiplier_nonneg (nN nE k : ℕ) (cert : ACDualCertificate nN nE k)
    (hcert : cert.Nonneg) (i : Fin (6 * nN + nE)) : 0 ≤ liftedMultiplier nN nE k cert i := by
  obtain ⟨h1, h2⟩ := hcert
  unfold liftedMultiplier
  rcases (constraintIndex nN nE).symm i with ⟨g, b⟩ | e
  · fin_cases g
    · exact (h1 b).1
    · exact (h1 b).2.1
    · exact (h1 b).2.2.1
    · exact (h1 b).2.2.2.1
    · exact (h1 b).2.2.2.2.1
    · exact (h1 b).2.2.2.2.2
  · exact h2 e

private lemma sum_lifted {M : Type*} [AddCommMonoid M] (nN nE : ℕ)
    (f : (Fin 6 × Fin nN) ⊕ Fin nE → M) :
    ∑ i : Fin (6 * nN + nE), f ((constraintIndex nN nE).symm i) =
      ∑ b : Fin nN, (f (Sum.inl (0, b)) + f (Sum.inl (1, b)) + f (Sum.inl (2, b)) +
        f (Sum.inl (3, b)) + f (Sum.inl (4, b)) + f (Sum.inl (5, b))) +
      ∑ e : Fin nE, f (Sum.inr e) := by
  rw [Equiv.sum_comp (constraintIndex nN nE).symm f, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.sum_univ_succ, add_assoc]

/-- The grouped dual slack is the factored-form certificate matrix `C + ∑ i, λ i • A i`. -/
lemma dualSlack_eq_lifted (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) :
    dualSlack nN nE k P cert = objectiveMatrix nN nE P +
      ∑ i, (liftedMultiplier nN nE k cert i : ℂ) • liftedCoeff nN nE P i := by
  simp only [liftedMultiplier, liftedCoeff]
  rw [sum_lifted nN nE (fun s => (cert.multiplier s : ℂ) • constraintCoeff nN nE P s)]
  simp only [ACDualCertificate.multiplier, constraintCoeff, dualSlack]
  simp [sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_neg]
  abel

/-- The grouped certified bound is the factored-form bound `c0 - ∑ i, λ i * b i`. -/
lemma certifiedLowerBound_eq_lifted (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) :
    certifiedLowerBound nN nE k P cert = objectiveOffset nN nE P -
      ∑ i, liftedMultiplier nN nE k cert i * liftedBound nN nE P i := by
  simp only [liftedMultiplier, liftedBound]
  rw [sum_lifted nN nE (fun s => cert.multiplier s * constraintBound nN nE P s)]
  simp only [ACDualCertificate.multiplier, constraintBound, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.isValue, cons_val_zero, cons_val_one, cons_val, mul_neg]
  rw [certifiedLowerBound]
  ring_nf

/-! ## D. Soundness and optimality -/

/-- Relaxation bound: under the sign check and the exact factorization, every
relaxation-feasible matrix has cost at least the certified bound. -/
theorem certifiedLowerBound_le_sdpCost (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) (hnonneg : cert.Nonneg)
    (hfactor : dualSlack nN nE k P cert = cert.factor * cert.factorᴴ)
    (W : Matrix (Fin nN) (Fin nN) ℂ) (hW : sdpFeasible nN nE P W) :
    certifiedLowerBound nN nE k P cert ≤ sdpCost nN nE P W := by
  have hW' := (sdpFeasible_iff_lifted nN nE P W).1 hW
  have h := MathlibExt.Analysis.Convex.FactoredSDPLowerBound.factored_certificate_lower_bound
    nN (6 * nN + nE) 0 k (objectiveMatrix nN nE P) (objectiveOffset nN nE P)
    (liftedCoeff nN nE P) (liftedBound nN nE P) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (objectiveMatrix_isHermitian nN nE P) (liftedCoeff_isHermitian nN nE P)
    (fun j => Fin.elim0 j) (liftedMultiplier nN nE k cert) (fun _ => 0) cert.factor
    (liftedMultiplier_nonneg nN nE k cert hnonneg)
    (by rw [← hfactor, dualSlack_eq_lifted]; simp)
    W hW'.1 hW'.2 (fun j => Fin.elim0 j)
  rw [certifiedLowerBound_eq_lifted, sdpCost_eq_objective]
  simpa using h

/-- AC bound: under the sign check and the exact factorization, every AC-feasible voltage
has cost at least the certified bound. -/
theorem certifiedLowerBound_le_acCost (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) (hnonneg : cert.Nonneg)
    (hfactor : dualSlack nN nE k P cert = cert.factor * cert.factorᴴ)
    (V : Fin nN → ℂ) (hV : acFeasible nN nE P V) :
    certifiedLowerBound nN nE k P cert ≤ acCost nN nE P V := by
  exact (currentLimitedACLift_sound nN nE P).2 _
    (fun W hW => certifiedLowerBound_le_sdpCost nN nE k P cert hnonneg hfactor W hW) V hV

/-- Optimality by equality: a supplied AC-feasible voltage whose cost equals the certified
bound is a global minimizer of the AC problem, and its lift minimizes the relaxation. No
rank-one property of any other relaxed point is assumed. -/
theorem acOptimal_of_acCost_eq_certifiedLowerBound (nN nE k : ℕ)
    (P : CurrentLimitedOPF nN nE) (cert : ACDualCertificate nN nE k) (hnonneg : cert.Nonneg)
    (hfactor : dualSlack nN nE k P cert = cert.factor * cert.factorᴴ)
    (Vstar : Fin nN → ℂ) (hVstar : acFeasible nN nE P Vstar)
    (hcost : acCost nN nE P Vstar = certifiedLowerBound nN nE k P cert) :
    (∀ V : Fin nN → ℂ, acFeasible nN nE P V → acCost nN nE P Vstar ≤ acCost nN nE P V) ∧
      ∀ W : Matrix (Fin nN) (Fin nN) ℂ, sdpFeasible nN nE P W →
        sdpCost nN nE P (voltageLift nN Vstar) ≤ sdpCost nN nE P W := by
  refine ⟨fun V hV => ?_, fun W hW => ?_⟩
  · rw [hcost]
    exact certifiedLowerBound_le_acCost nN nE k P cert hnonneg hfactor V hV
  · rw [((currentLimitedACLift_sound nN nE P).1 Vstar hVstar).2, hcost]
    exact certifiedLowerBound_le_sdpCost nN nE k P cert hnonneg hfactor W hW

/-- **AC voltage certificate.** For a current-limited OPF problem and a dual witness with
nonnegative multipliers and an exact factorization of its dual slack, the certified bound
lies below the cost of every relaxation-feasible matrix and of every AC-feasible voltage,
and a supplied AC-feasible voltage attaining the bound is globally optimal for the AC
problem and its lift for the relaxation. -/
theorem acVoltageCertificate_correct (nN nE k : ℕ) (P : CurrentLimitedOPF nN nE)
    (cert : ACDualCertificate nN nE k) (hnonneg : cert.Nonneg)
    (hfactor : dualSlack nN nE k P cert = cert.factor * cert.factorᴴ) :
    (∀ W : Matrix (Fin nN) (Fin nN) ℂ, sdpFeasible nN nE P W →
      certifiedLowerBound nN nE k P cert ≤ sdpCost nN nE P W) ∧
    (∀ V : Fin nN → ℂ, acFeasible nN nE P V →
      certifiedLowerBound nN nE k P cert ≤ acCost nN nE P V) ∧
    ∀ Vstar : Fin nN → ℂ, acFeasible nN nE P Vstar →
      acCost nN nE P Vstar = certifiedLowerBound nN nE k P cert →
      (∀ V : Fin nN → ℂ, acFeasible nN nE P V → acCost nN nE P Vstar ≤ acCost nN nE P V) ∧
        ∀ W : Matrix (Fin nN) (Fin nN) ℂ, sdpFeasible nN nE P W →
          sdpCost nN nE P (voltageLift nN Vstar) ≤ sdpCost nN nE P W := by
  exact ⟨certifiedLowerBound_le_sdpCost nN nE k P cert hnonneg hfactor,
    certifiedLowerBound_le_acCost nN nE k P cert hnonneg hfactor,
    fun Vstar hVstar hcost => acOptimal_of_acCost_eq_certifiedLowerBound nN nE k P cert hnonneg
      hfactor Vstar hVstar hcost⟩

/-! ## E. Two-bus validation -/

/-- Two buses joined by one unit-conductance branch, no shunts. Generation is paid at bus
`0` only; bus `1` carries the active load `15/16` and no active generation
(`activeGenMin 1 = activeGenMax 1 = 0`). Squared voltages lie in `[1/8, 4]`. -/
noncomputable def twoBusCertExample : CurrentLimitedOPF 2 1 where
  incidence := Matrix.of ![![1], ![-1]]
  branchAdmittance := fun _ => 1
  shuntAdmittance := fun _ => 0
  activeDemand := ![0, 15 / 16]
  reactiveDemand := fun _ => 0
  activeGenMin := ![-2, 0]
  activeGenMax := ![3, 0]
  reactiveGenMin := fun _ => -1
  reactiveGenMax := fun _ => 1
  voltageSqMin := fun _ => 1 / 8
  voltageSqMax := fun _ => 4
  currentSqMax := fun _ => 4
  costCoeff := ![1, 0]

/-- Exact rational certificate for `twoBusCertExample`: multiplier `4` on the upper active
limit at bus `1`, multiplier `9/16` on the upper squared-voltage limit at bus `0`, all other
multipliers zero, and factor `F = (5/4, -2)ᵀ`. -/
noncomputable def twoBusCertificate : ACDualCertificate 2 1 1 where
  activeMaxMult := ![0, 4]
  activeMinMult := fun _ => 0
  reactiveMaxMult := fun _ => 0
  reactiveMinMult := fun _ => 0
  voltageMaxMult := ![9 / 16, 0]
  voltageMinMult := fun _ => 0
  currentMult := fun _ => 0
  factor := !![5 / 4; -2]

/-- The certified optimal voltage `V = (2, 5/4)`. -/
noncomputable def twoBusOptimalVoltage : Fin 2 → ℂ := ![2, 5 / 4]

private lemma nodePower_zero (V : Fin 2 → ℂ) :
    nodeComplexPower 2 1 twoBusCertExample.incidence V twoBusCertExample.branchAdmittance
      twoBusCertExample.shuntAdmittance 0 = V 0 * conj (V 0 - V 1) := by
  simp [nodeComplexPower, PhyslibExt.Circuits.BalancedThreePhase.complexPower,
    nodeInjection, branchDrop, twoBusCertExample, Fin.sum_univ_two, sub_eq_add_neg]

private lemma nodePower_one (V : Fin 2 → ℂ) :
    nodeComplexPower 2 1 twoBusCertExample.incidence V twoBusCertExample.branchAdmittance
      twoBusCertExample.shuntAdmittance 1 = V 1 * conj (V 1 - V 0) := by
  simp [nodeComplexPower, PhyslibExt.Circuits.BalancedThreePhase.complexPower,
    nodeInjection, branchDrop, twoBusCertExample, Fin.sum_univ_two, sub_eq_add_neg]

private lemma drop_eq (V : Fin 2 → ℂ) :
    branchDrop 2 1 twoBusCertExample.incidence V 0 = V 0 - V 1 := by
  simp [branchDrop, twoBusCertExample, Fin.sum_univ_two, sub_eq_add_neg]

private lemma acCost_eq (V : Fin 2 → ℂ) :
    acCost 2 1 twoBusCertExample V = (V 0 * conj (V 0 - V 1)).re := by
  rw [acCost, Fin.sum_univ_two, nodePower_zero]
  simp [twoBusCertExample]

private lemma admittance_apply (a b : Fin 2) :
    twoBusCertExample.admittance a b = if a = b then 1 else -1 := by
  fin_cases a <;> fin_cases b <;>
    simp [CurrentLimitedOPF.admittance, busAdmittance, twoBusCertExample, Matrix.diagonal]

private lemma feasible_real (a b : ℝ) (hP0 : -2 ≤ a * (a - b) ∧ a * (a - b) ≤ 3)
    (hP1 : b * (b - a) + 15 / 16 = 0) (hV0 : 1 / 8 ≤ a ^ 2 ∧ a ^ 2 ≤ 4)
    (hV1 : 1 / 8 ≤ b ^ 2 ∧ b ^ 2 ≤ 4) :
    acFeasible 2 1 twoBusCertExample ![(a : ℂ), (b : ℂ)] := by
  refine ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_one.mpr ?_⟩
  · rw [nodePower_zero]; simp [twoBusCertExample]; constructor <;> nlinarith
  · rw [nodePower_one]; simp [twoBusCertExample]; constructor <;> nlinarith
  · rw [nodePower_zero]; simp [twoBusCertExample]
  · rw [nodePower_one]; simp [twoBusCertExample]
  · simp [twoBusCertExample, Complex.normSq_apply]; constructor <;> nlinarith
  · simp [twoBusCertExample, Complex.normSq_apply]; constructor <;> nlinarith
  · rw [drop_eq]; simp [twoBusCertExample, Complex.normSq_apply]; nlinarith

private lemma optimal_feasible : acFeasible 2 1 twoBusCertExample twoBusOptimalVoltage := by
  have h := feasible_real 2 (5 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simpa [twoBusOptimalVoltage] using h

private lemma optimal_cost : acCost 2 1 twoBusCertExample twoBusOptimalVoltage = 3 / 2 := by
  rw [acCost_eq]; simp [twoBusOptimalVoltage, map_div₀, Complex.div_re]; norm_num

private lemma certificate_nonneg : twoBusCertificate.Nonneg := by
  refine ⟨fun b => ?_, fun e => ?_⟩
  · fin_cases b <;> norm_num [twoBusCertificate]
  · norm_num [twoBusCertificate]

private lemma certifiedLowerBound_certificate :
    certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate = 3 / 2 := by
  simp [certifiedLowerBound, objectiveOffset, twoBusCertificate, twoBusCertExample,
    Fin.sum_univ_two]
  norm_num

private lemma dualSlack_certificate_entries :
    dualSlack 2 1 1 twoBusCertExample twoBusCertificate = !![25 / 16, -5 / 2; -5 / 2, 4] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [dualSlack, objectiveMatrix, activeCoeff, reactiveCoeff, voltageCoeff,
      branchCurrentCoeff, rowSelect, admittance_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply] <;>
    simp [twoBusCertificate, twoBusCertExample, Fin.sum_univ_two] <;> norm_num

private lemma dualSlack_certificate :
    dualSlack 2 1 1 twoBusCertExample twoBusCertificate =
      twoBusCertificate.factor * twoBusCertificate.factorᴴ := by
  rw [dualSlack_certificate_entries]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [twoBusCertificate, Matrix.mul_apply] <;> norm_num

private lemma pairing_entries (A W : Matrix (Fin 2) (Fin 2) ℂ) :
    pairing 2 A W = (A 0 0 * W 0 0 + A 0 1 * W 1 0 + A 1 0 * W 0 1 + A 1 1 * W 1 1).re := by
  simp [pairing, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private lemma activeCoeff_zero :
    activeCoeff 2 twoBusCertExample.admittance 0 = !![1, -1 / 2; -1 / 2, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [activeCoeff, rowSelect, admittance_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply] <;> norm_num

private lemma activeCoeff_one :
    activeCoeff 2 twoBusCertExample.admittance 1 = !![0, -1 / 2; -1 / 2, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [activeCoeff, rowSelect, admittance_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply] <;> norm_num

/-- Validation (positive): the certificate passes the sign and factorization checks, the
voltage `(2, 5/4)` is AC feasible, and its cost equals the certified bound `3/2`. -/
lemma twoBus_certificate_exact :
    twoBusCertificate.Nonneg ∧
      dualSlack 2 1 1 twoBusCertExample twoBusCertificate =
        twoBusCertificate.factor * twoBusCertificate.factorᴴ ∧
      acFeasible 2 1 twoBusCertExample twoBusOptimalVoltage ∧
      acCost 2 1 twoBusCertExample twoBusOptimalVoltage = 3 / 2 ∧
      certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate = 3 / 2 := by
  exact ⟨certificate_nonneg, dualSlack_certificate, optimal_feasible, optimal_cost,
    certifiedLowerBound_certificate⟩

/-- Validation (positive): `(2, 5/4)` is a global minimizer of the two-bus AC problem. -/
lemma twoBus_globalOptimum (V : Fin 2 → ℂ) (hV : acFeasible 2 1 twoBusCertExample V) :
    acCost 2 1 twoBusCertExample twoBusOptimalVoltage ≤ acCost 2 1 twoBusCertExample V := by
  exact (acOptimal_of_acCost_eq_certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate
    certificate_nonneg dualSlack_certificate twoBusOptimalVoltage optimal_feasible
    (by rw [optimal_cost, certifiedLowerBound_certificate])).1 V hV

/-- A relaxed point: the average of the lifts of the AC-feasible voltages `(2, 5/4)` and
`(2, 3/4)`. -/
noncomputable def twoBusRelaxedPoint : Matrix (Fin 2) (Fin 2) ℂ := !![4, 2; 2, 17 / 16]

private lemma pairing_reactive_relaxed (k : Fin 2) :
    pairing 2 (reactiveCoeff 2 twoBusCertExample.admittance k) twoBusRelaxedPoint = 0 := by
  have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
  rcases hk with rfl | rfl <;>
    simp only [pairing_entries, reactiveCoeff, rowSelect, admittance_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.conjTranspose_apply] <;>
    simp [twoBusRelaxedPoint]

private lemma relaxedPoint_eq :
    twoBusRelaxedPoint = (1 / 2 : ℝ) •
      (voltageLift 2 twoBusOptimalVoltage + voltageLift 2 (![2, 3 / 4] : Fin 2 → ℂ)) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [voltageLift, Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.smul_apply,
      Pi.star_apply] <;>
    simp [twoBusRelaxedPoint, twoBusOptimalVoltage] <;>
    norm_num [map_ofNat, map_div₀]

/-- Validation (relaxed, not rank one): the averaged point is relaxation feasible, is the
lift of no voltage vector, and has cost `2`, strictly above the certified bound. The
certificate bounds it without recovering a voltage from it. -/
lemma twoBus_relaxedPoint_not_lift :
    sdpFeasible 2 1 twoBusCertExample twoBusRelaxedPoint ∧
      (∀ V : Fin 2 → ℂ, voltageLift 2 V ≠ twoBusRelaxedPoint) ∧
      sdpCost 2 1 twoBusCertExample twoBusRelaxedPoint = 2 ∧
      certifiedLowerBound 2 1 1 twoBusCertExample twoBusCertificate <
        sdpCost 2 1 twoBusCertExample twoBusRelaxedPoint := by
  have hpsd : twoBusRelaxedPoint.PosSemidef := by
    rw [relaxedPoint_eq]
    exact ((Matrix.posSemidef_vecMulVec_self_star _).add
      (Matrix.posSemidef_vecMulVec_self_star _)).smul (by norm_num)
  have hcost : sdpCost 2 1 twoBusCertExample twoBusRelaxedPoint = 2 := by
    simp only [sdpCost, Fin.sum_univ_two, activeCoeff_zero, activeCoeff_one, pairing_entries]
    simp [twoBusCertExample, twoBusRelaxedPoint]
    norm_num
  refine ⟨⟨hpsd, Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_one.mpr ?_⟩, fun V hV => ?_, hcost, ?_⟩
  · simp only [activeCoeff_zero, pairing_entries]
    simp [twoBusCertExample, twoBusRelaxedPoint]; norm_num
  · simp only [activeCoeff_one, pairing_entries]
    simp [twoBusCertExample, twoBusRelaxedPoint]; norm_num
  · rw [pairing_reactive_relaxed]; norm_num [twoBusCertExample]
  · rw [pairing_reactive_relaxed]; norm_num [twoBusCertExample]
  · simp only [pairing_entries, voltageCoeff]
    simp [twoBusCertExample, twoBusRelaxedPoint]; norm_num
  · simp only [pairing_entries, voltageCoeff]
    simp [twoBusCertExample, twoBusRelaxedPoint]; norm_num
  · simp only [pairing_entries, branchCurrentCoeff]
    simp [twoBusCertExample, twoBusRelaxedPoint]; norm_num
  · have h00 := congrFun (congrFun hV 0) 0
    have h01 := congrFun (congrFun hV 0) 1
    have h11 := congrFun (congrFun hV 1) 1
    simp only [voltageLift, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def] at h00 h01 h11
    have key : (V 0 * conj (V 1)) * conj (V 0 * conj (V 1)) =
        (V 0 * conj (V 0)) * (V 1 * conj (V 1)) := by
      simp only [map_mul, Complex.conj_conj]; ring
    rw [h01, h00, h11] at key
    simp [twoBusRelaxedPoint] at key
    norm_num [map_ofNat] at key
  · rw [hcost, certifiedLowerBound_certificate]; norm_num

/-- The AC-feasible voltage `(2, 3/4)`, a stationary point of the two-bus Lagrangian. -/
noncomputable def twoBusStationaryVoltage : Fin 2 → ℂ := ![2, 3 / 4]

/-- Stationarity multipliers at `(2, 3/4)`: `4` on the lower active limit at bus `1` and
`-25/16` on the upper squared-voltage limit at bus `0`; the factor field is unused. -/
noncomputable def twoBusStationaryMultipliers : ACDualCertificate 2 1 1 where
  activeMaxMult := fun _ => 0
  activeMinMult := ![0, 4]
  reactiveMaxMult := fun _ => 0
  reactiveMinMult := fun _ => 0
  voltageMaxMult := ![-25 / 16, 0]
  voltageMinMult := fun _ => 0
  currentMult := fun _ => 0
  factor := 0

private lemma stationary_feasible : acFeasible 2 1 twoBusCertExample twoBusStationaryVoltage := by
  have h := feasible_real 2 (3 / 4) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  simpa [twoBusStationaryVoltage] using h

private lemma stationary_cost : acCost 2 1 twoBusCertExample twoBusStationaryVoltage = 5 / 2 := by
  rw [acCost_eq]; simp [twoBusStationaryVoltage, map_div₀, Complex.div_re]; norm_num

private lemma certifiedLowerBound_stationary :
    certifiedLowerBound 2 1 1 twoBusCertExample twoBusStationaryMultipliers = 5 / 2 := by
  simp [certifiedLowerBound, objectiveOffset, twoBusStationaryMultipliers, twoBusCertExample,
    Fin.sum_univ_two]
  norm_num

private lemma dualSlack_stationary_entries :
    dualSlack 2 1 1 twoBusCertExample twoBusStationaryMultipliers =
      !![-9 / 16, 3 / 2; 3 / 2, -4] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [dualSlack, objectiveMatrix, activeCoeff, reactiveCoeff, voltageCoeff,
      branchCurrentCoeff, rowSelect, admittance_apply, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.conjTranspose_apply, Matrix.sub_apply] <;>
    simp [twoBusStationaryMultipliers, twoBusCertExample, Fin.sum_univ_two] <;> norm_num

/-- Validation (false stationary optimum): at the AC-feasible voltage `(2, 3/4)` the
Lagrangian with the stationarity multipliers is stationary (its slack matrix annihilates
the voltage) and the would-be bound equals the point's cost `5/2`, yet a multiplier is
negative, the slack has no factorization of any width, and the certified optimum
`(2, 5/4)` costs strictly less. Stationarity alone is not a certificate. -/
lemma twoBus_stationaryPoint_not_certificate :
    acFeasible 2 1 twoBusCertExample twoBusStationaryVoltage ∧
      dualSlack 2 1 1 twoBusCertExample twoBusStationaryMultipliers *ᵥ
        twoBusStationaryVoltage = 0 ∧
      acCost 2 1 twoBusCertExample twoBusStationaryVoltage = 5 / 2 ∧
      certifiedLowerBound 2 1 1 twoBusCertExample twoBusStationaryMultipliers =
        acCost 2 1 twoBusCertExample twoBusStationaryVoltage ∧
      ¬ twoBusStationaryMultipliers.Nonneg ∧
      (∀ (m : ℕ) (F : Matrix (Fin 2) (Fin m) ℂ),
        dualSlack 2 1 1 twoBusCertExample twoBusStationaryMultipliers ≠ F * Fᴴ) ∧
      acCost 2 1 twoBusCertExample twoBusOptimalVoltage <
        certifiedLowerBound 2 1 1 twoBusCertExample twoBusStationaryMultipliers := by
  refine ⟨stationary_feasible, ?_, stationary_cost, ?_, ?_, fun m F hF => ?_, ?_⟩
  · rw [dualSlack_stationary_entries]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, twoBusStationaryVoltage] <;>
      norm_num
  · rw [certifiedLowerBound_stationary, stationary_cost]
  · rintro ⟨h, -⟩
    have := (h 0).2.2.2.2.1
    norm_num [twoBusStationaryMultipliers] at this
  · have h11 := congrFun (congrFun hF 1) 1
    rw [dualSlack_stationary_entries] at h11
    have hre := congrArg Complex.re h11
    simp [Matrix.mul_apply, Complex.re_sum, Complex.mul_conj] at hre
    have hnn : 0 ≤ ∑ j, Complex.normSq (F 1 j) :=
      Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    linarith
  · rw [certifiedLowerBound_stationary, optimal_cost]; norm_num

end PhyslibExt.Circuits.ACVoltageCertificate
