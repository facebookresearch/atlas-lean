/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
Finite binary fingerprinting codes and the tracing game, definitions only.

This module defines finite binary fingerprinting codes and the tracing game
only (no existence or lower-bound theorem is claimed). The syntax
(`FingerprintingCode`, keyed generation and tracing) follows Bun, Ullman and
Vadhan (2018), Definition 3.1, with the shared tracing key of Vadhan (2017),
Definition 7.5.16; `Feasible` is their feasible set, `ErrorRobustFeasible`
their Definition 3.3 written without division, and `MarkingFeasible` the
marking condition of Tardos (2008), Definition 1.1. Coalitions are nonempty
as in Tardos (2008), Definition 1.1; Bun, Ullman and Vadhan allow the empty
coalition, so the security predicates here are formally weaker. Bias
generation (`biasCodebookPMF`, `genFromBiasVectorDist`, `genFromIIDBiasDist`)
and linear accusation (`tardosWeight`, `tardosScore`, `TardosAccuses`) follow
Tardos (2008), Section 2.1, for discrete bias distributions; the bias
generators emit only the bias vector as the tracing key, so a Tardos-style
code carries the codebook in the key as well. Security is recorded as
separate soundness and completeness error probabilities
(`soundnessErrorProb`, `completenessErrorProb`, with the error-robust variant
`errorRobustCompletenessErrorProb`) and predicates `IsFingerprintingSecure`
(Bun, Ullman and Vadhan (2018), Definition 3.1, with separate parameters as
in their Definition 3.12) and `IsErrorRobustFingerprintingSecure` (their
Definition 3.3), together with a combined error probability
(`combinedErrorProb`) and predicate (`IsFingerprintingSecureCombined`)
matching Vadhan (2017), Definition 7.5.17.

Main definitions, by name: `Word`, `Codebook`, `Bias`, `submatrix`, `Pirate`,
`FingerprintingCode`, `Feasible`, `MarkingFeasible`, `ErrorRobustFeasible`,
`AccusesGuilty`, `FalseAccusation`, `NoAccusation`, `TracingFailure`,
`tracingGame`, `completenessFailureEvent`,
`errorRobustCompletenessFailureEvent`, `soundnessFailureEvent`,
`combinedFailureEvent`, `completenessErrorProb`,
`errorRobustCompletenessErrorProb`, `soundnessErrorProb`,
`combinedErrorProb`, `IsFingerprintingSecure`,
`IsErrorRobustFingerprintingSecure`, `IsFingerprintingSecureCombined`,
`bernoulliMass`, `bernoulliPMF`, `biasCodebookMass`, `biasCodebookPMF`,
`pmfIID`, `genFromBiasVectorDist`, `genFromIIDBiasDist`, `tardosWeight`,
`tardosScore`, `TardosAccuses`, `trivialCode`.
-/

@[expose] public section

namespace CSLibExt.Privacy.Fingerprinting

open scoped ENNReal

/-! ### Core types -/

abbrev Word (d : ℕ) : Type := Fin d → Bool

abbrev Codebook (n d : ℕ) : Type := Fin n → Word d

abbrev Bias : Type := Set.Icc (0 : ℝ) 1

def submatrix {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n)) :
    {i : Fin n // i ∈ S} → Word d :=
  fun i => C i.1

@[simp]
theorem submatrix_apply {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n))
    (i : {i : Fin n // i ∈ S}) :
    submatrix C S i = C i.1 :=
  rfl

abbrev Pirate (n d : ℕ) (S : Finset (Fin n)) : Type :=
  ({i : Fin n // i ∈ S} → Word d) → PMF (Word d)

structure FingerprintingCode (n d : ℕ) (Key : Type*) where
  gen : PMF (Codebook n d × Key)
  trace : Key → Word d → PMF (Option (Fin n))

/-! ### Feasibility and marking predicates -/

def Feasible {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) : Prop :=
  ∀ j : Fin d, ∃ i ∈ S, w j = C i j

def MarkingFeasible {n d : ℕ} (C : Codebook n d) (S : Finset (Fin n)) (w : Word d) : Prop :=
  ∀ (j : Fin d) (b : Bool), (∀ i ∈ S, C i j = b) → w j = b

def ErrorRobustFeasible {n d : ℕ} (β : ℝ) (C : Codebook n d) (S : Finset (Fin n))
    (w : Word d) : Prop :=
  (1 - β) * (d : ℝ) ≤
    ((Finset.univ.filter fun j : Fin d => ∃ i ∈ S, w j = C i j).card : ℝ)

/-! ### Colluder accusation predicates -/

def AccusesGuilty {n : ℕ} (S : Finset (Fin n)) (a : Option (Fin n)) : Prop :=
  ∃ i ∈ S, a = some i

def FalseAccusation {n : ℕ} (S : Finset (Fin n)) (a : Option (Fin n)) : Prop :=
  ∃ i : Fin n, i ∉ S ∧ a = some i

def NoAccusation {n : ℕ} (a : Option (Fin n)) : Prop :=
  a = none

def TracingFailure {n : ℕ} (S : Finset (Fin n)) (a : Option (Fin n)) : Prop :=
  ¬ AccusesGuilty S a

/-! ### Tracing game and security predicates -/

noncomputable def tracingGame {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) :
    PMF (Codebook n d × Word d × Option (Fin n)) :=
  FC.gen.bind fun ck =>
    (P (submatrix ck.1 S)).bind fun w =>
      (FC.trace ck.2 w).map fun a => (ck.1, w, a)

theorem tracingGame_def {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) :
    tracingGame FC S P =
      FC.gen.bind fun ck =>
        (P (submatrix ck.1 S)).bind fun w =>
          (FC.trace ck.2 w).map fun a => (ck.1, w, a) :=
  rfl

def completenessFailureEvent {n d : ℕ} (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | Feasible t.1 S t.2.1 ∧ NoAccusation t.2.2}

def errorRobustCompletenessFailureEvent {n d : ℕ} (β : ℝ) (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | ErrorRobustFeasible β t.1 S t.2.1 ∧ NoAccusation t.2.2}

def soundnessFailureEvent {n d : ℕ} (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | FalseAccusation S t.2.2}

def combinedFailureEvent {n d : ℕ} (S : Finset (Fin n)) :
    Set (Codebook n d × Word d × Option (Fin n)) :=
  {t | Feasible t.1 S t.2.1 ∧ TracingFailure S t.2.2}

noncomputable def completenessErrorProb {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (completenessFailureEvent S)).toReal

noncomputable def errorRobustCompletenessErrorProb {n d : ℕ} {Key : Type*}
    (β : ℝ) (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (errorRobustCompletenessFailureEvent β S)).toReal

noncomputable def soundnessErrorProb {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (soundnessFailureEvent S)).toReal

noncomputable def combinedErrorProb {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (S : Finset (Fin n)) (P : Pirate n d S) : ℝ :=
  ((tracingGame FC S P).toOuterMeasure (combinedFailureEvent S)).toReal

def IsFingerprintingSecure {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (c : ℕ) (γ ξ : ℝ) : Prop :=
  0 ≤ γ ∧ 0 ≤ ξ ∧
    ∀ (S : Finset (Fin n)), S.Nonempty → S.card ≤ c → ∀ (P : Pirate n d S),
      completenessErrorProb FC S P ≤ γ ∧ soundnessErrorProb FC S P ≤ ξ

def IsErrorRobustFingerprintingSecure {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (c : ℕ) (β γ ξ : ℝ) : Prop :=
  0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ ξ ∧
    ∀ (S : Finset (Fin n)), S.Nonempty → S.card ≤ c → ∀ (P : Pirate n d S),
      errorRobustCompletenessErrorProb β FC S P ≤ γ ∧ soundnessErrorProb FC S P ≤ ξ

def IsFingerprintingSecureCombined {n d : ℕ} {Key : Type*}
    (FC : FingerprintingCode n d Key) (c : ℕ) (ε : ℝ) : Prop :=
  0 ≤ ε ∧
    ∀ (S : Finset (Fin n)), S.Nonempty → S.card ≤ c → ∀ (P : Pirate n d S),
      combinedErrorProb FC S P ≤ ε

/-! ### Codebook generation from a bias distribution -/

noncomputable def bernoulliMass (p : Bias) (b : Bool) : ℝ≥0∞ :=
  if b then ENNReal.ofReal p.1 else ENNReal.ofReal (1 - p.1)

noncomputable def bernoulliPMF (p : Bias) : PMF Bool :=
  PMF.ofFintype (bernoulliMass p) (by
    rw [Fintype.sum_bool]
    simp only [bernoulliMass, Bool.false_eq_true, ite_true, ite_false]
    rw [← ENNReal.ofReal_add p.2.1 (sub_nonneg.mpr p.2.2), add_sub_cancel, ENNReal.ofReal_one])

@[simp]
theorem bernoulliPMF_apply (p : Bias) (b : Bool) :
    bernoulliPMF p b = bernoulliMass p b :=
  rfl

@[simp]
theorem bernoulliPMF_true (p : Bias) :
    bernoulliPMF p true = ENNReal.ofReal p.1 :=
  rfl

@[simp]
theorem bernoulliPMF_false (p : Bias) :
    bernoulliPMF p false = ENNReal.ofReal (1 - p.1) :=
  rfl

noncomputable def biasCodebookMass {n d : ℕ} (p : Fin d → Bias) (C : Codebook n d) : ℝ≥0∞ :=
  ∏ i : Fin n, ∏ j : Fin d, bernoulliMass (p j) (C i j)

noncomputable def biasCodebookPMF {n d : ℕ} (p : Fin d → Bias) : PMF (Codebook n d) :=
  PMF.ofFintype (biasCodebookMass p) (by
    simp only [biasCodebookMass]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (row : Word d) =>
      ∏ j : Fin d, bernoulliMass (p j) (row j))]
    apply Finset.prod_eq_one
    intro _ _
    rw [← Fintype.prod_sum (fun (j : Fin d) (b : Bool) => bernoulliMass (p j) b)]
    apply Finset.prod_eq_one
    intro j _
    rw [Fintype.sum_bool]
    simp only [bernoulliMass, Bool.false_eq_true, ite_true, ite_false]
    rw [← ENNReal.ofReal_add (p j).2.1 (sub_nonneg.mpr (p j).2.2), add_sub_cancel,
      ENNReal.ofReal_one])

@[simp]
theorem biasCodebookPMF_apply {n d : ℕ} (p : Fin d → Bias) (C : Codebook n d) :
    biasCodebookPMF p C = ∏ i : Fin n, ∏ j : Fin d, bernoulliMass (p j) (C i j) :=
  rfl

noncomputable def pmfIID {α : Type*} (μ : PMF α) : (d : ℕ) → PMF (Fin d → α)
  | 0 => PMF.pure Fin.elim0
  | d + 1 => μ.bind fun x => (pmfIID μ d).map fun f => Fin.cons x f

@[simp]
theorem pmfIID_zero {α : Type*} (μ : PMF α) :
    pmfIID μ 0 = PMF.pure Fin.elim0 :=
  rfl

@[simp]
theorem pmfIID_succ {α : Type*} (μ : PMF α) (d : ℕ) :
    pmfIID μ (d + 1) = μ.bind fun x => (pmfIID μ d).map fun f => Fin.cons x f :=
  rfl

noncomputable def genFromBiasVectorDist {n d : ℕ} (biasDist : PMF (Fin d → Bias)) :
    PMF (Codebook n d × (Fin d → Bias)) :=
  biasDist.bind fun p => (biasCodebookPMF (n := n) p).map fun C => (C, p)

theorem genFromBiasVectorDist_def {n d : ℕ} (biasDist : PMF (Fin d → Bias)) :
    genFromBiasVectorDist (n := n) biasDist =
      biasDist.bind fun p => (biasCodebookPMF (n := n) p).map fun C => (C, p) :=
  rfl

noncomputable def genFromIIDBiasDist {n d : ℕ} (μ : PMF Bias) :
    PMF (Codebook n d × (Fin d → Bias)) :=
  genFromBiasVectorDist (pmfIID μ d)

theorem genFromIIDBiasDist_def {n d : ℕ} (μ : PMF Bias) :
    genFromIIDBiasDist (n := n) (d := d) μ = genFromBiasVectorDist (pmfIID μ d) :=
  rfl

/-! ### Tardos linear accusation score and predicate -/

noncomputable def tardosWeight (p : ℝ) (b : Bool) : ℝ :=
  if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))

@[simp]
theorem tardosWeight_true (p : ℝ) :
    tardosWeight p true = Real.sqrt ((1 - p) / p) :=
  rfl

@[simp]
theorem tardosWeight_false (p : ℝ) :
    tardosWeight p false = -Real.sqrt (p / (1 - p)) :=
  rfl

noncomputable def tardosScore {n d : ℕ} (p : Fin d → ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) : ℝ :=
  ∑ j : Fin d, if w j then tardosWeight (p j) (C i j) else 0

theorem tardosScore_def {n d : ℕ} (p : Fin d → ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) :
    tardosScore p C w i = ∑ j : Fin d, if w j then tardosWeight (p j) (C i j) else 0 :=
  rfl

def TardosAccuses {n d : ℕ} (p : Fin d → ℝ) (Z : ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) : Prop :=
  Z < tardosScore p C w i

theorem tardosAccuses_iff {n d : ℕ} (p : Fin d → ℝ) (Z : ℝ) (C : Codebook n d)
    (w : Word d) (i : Fin n) :
    TardosAccuses p Z C w i ↔ Z < tardosScore p C w i :=
  Iff.rfl

/-! ### Trivial single-user code witness -/

noncomputable def trivialCode : FingerprintingCode 1 1 Unit where
  gen := PMF.pure (fun _ _ => false, ())
  trace := fun _ _ => PMF.pure (some 0)

@[simp]
theorem trivialCode_gen :
    trivialCode.gen = PMF.pure (fun _ _ => false, ()) :=
  rfl

@[simp]
theorem trivialCode_trace (u : Unit) (w : Word 1) :
    trivialCode.trace u w = PMF.pure (some 0) :=
  rfl

end CSLibExt.Privacy.Fingerprinting
