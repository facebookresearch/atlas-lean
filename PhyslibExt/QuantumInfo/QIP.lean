/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.InteractionAttainment
public import PhyslibExt.QuantumInfo.CircuitBridge
public import CSLibExt.Computability.Complexity.QuantumGates.BQPAudit
public import CSLibExt.Computability.Complexity.PairProjection
public import MathlibExt.Computability.TuringMachine.Composition

/-!
# Quantum interactive proofs: acceptance predicates, the QIP class, and BQP subset QIP

## i. Overview

Completeness and soundness predicates for the verifier-first,
even-message quantum interaction model of
`PhyslibExt.QuantumInfo.Interaction`, and their characterization through
the interaction value. In Watrous, Sec. VI.1, a promise problem is in
QIP(m, a, b) when some polynomial-time generated m-message verifier
satisfies completeness on every yes-instance (some prover is accepted
with probability at least `a`) and soundness on every no-instance (every
prover is accepted with probability at most `b`); QIP(m) is
QIP(m, 2/3, 1/3). `QIP.CompleteWith` and `QIP.SoundWith` state these two
conditions at given thresholds for one verifier, as on a single input,
and `QIP.Complete` and `QIP.Sound` are their instances at `2/3` and
`1/3`.

These predicates are also packaged into the complexity class `QIP`:
membership asks for a polynomial-time gate-list generator, with round
indices in unary, producing verifier-first, even-message protocols whose
verifiers meet completeness and soundness on every input. Only total
decision problems are formalized; the prover-first padding is not.

## ii. Key results

* `QIP.completeWith_iff_exists_value` and `QIP.soundWith_iff_forall_value`:
  completeness and soundness at any threshold read off the interaction
  value.
* `QIP.complete_iff_exists_value` and `QIP.sound_iff_forall_value`: the
  same at the thresholds `2/3` and `1/3`.
* `QIP.bqp_subset_qip`: BQP is contained in QIP at zero messages.

## iii. Table of contents

* `QIP.CompleteWith` and `QIP.SoundWith`: the acceptance predicates at a
  threshold.
* `QIP.Complete` and `QIP.Sound`: the acceptance predicates at `2/3` and
  `1/3`.
* `QIP.completeWith_iff_exists_value`, `QIP.soundWith_iff_forall_value`,
  `QIP.complete_iff_exists_value`, `QIP.sound_iff_forall_value`: the
  characterizations through the value.
* `QIP.circuitVerifier`: the gate-list verifier.
* `QIP`: the complexity class.
* `QIP.mem_QIP_iff`: membership unfolds to the generator existential.
* `QIP.acceptProb_circuitVerifier_zero`: the zero-message acceptance
  probability.
* `QIP.bqp_subset_qip`: BQP is contained in QIP.

## iv. References

Source: J. Watrous, "Quantum computational complexity", in Encyclopedia
of Complexity and Systems Science, Springer, 2009 (arXiv:0804.3401),
Sec. VI.1 (QIP(m, a, b): completeness at least `a`, soundness at most
`b`; QIP(m) = QIP(m, 2/3, 1/3)) and Sec. VI.2 (QIP(0) = BQP, for the
inclusion); S. Aaronson, MIT 6.845 Quantum Complexity Theory,
Lecture 17 (course-level definition; strict `> 2/3` there).
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.QIP

open PhyslibExt.QuantumInfo.Interaction

variable {k : ℕ} {dV dM : Type*} [Fintype dV] [DecidableEq dV] [Fintype dM] [DecidableEq dM]

/-- Completeness at threshold `c`: some prover with a finite workspace in `Type` is accepted
with probability at least `c`. The empty workspace has no strategies and never witnesses this;
the memoryless prover uses `Unit`. -/
def CompleteWith (c : ℝ) (V : Verifier k dV dM) : Prop :=
  ∃ (dP : Type) (_ : Fintype dP) (_ : DecidableEq dP) (P : Prover k dM dP),
    c ≤ (Interaction.acceptProb V P : ℝ)

/-- Soundness at threshold `s`: every prover with a finite workspace in `Type` is accepted with
probability at most `s`. -/
def SoundWith (s : ℝ) (V : Verifier k dV dM) : Prop :=
  ∀ (dP : Type) [Fintype dP] [DecidableEq dP] (P : Prover k dM dP),
    (Interaction.acceptProb V P : ℝ) ≤ s

/-- Completeness at a verifier: some prover with a finite workspace in `Type` is accepted
with probability at least `2/3`, the completeness threshold of QIP(m) = QIP(m, 2/3, 1/3). -/
def Complete (V : Verifier k dV dM) : Prop :=
  CompleteWith (2 / 3) V

/-- Soundness at a verifier: every prover with a finite workspace in `Type` is accepted with
probability at most `1/3`, the soundness threshold of QIP(m) = QIP(m, 2/3, 1/3). -/
def Sound (V : Verifier k dV dM) : Prop :=
  SoundWith (1 / 3) V

/-- Completeness at threshold `c` holds exactly when the value at some finite workspace in
`Type` is at least `c`. A witness at the empty workspace, whose value is `0`, forces `c ≤ 0`,
and then every prover with workspace `Unit` meets the threshold. -/
lemma completeWith_iff_exists_value (c : ℝ) (V : Verifier k dV dM) :
    CompleteWith c V ↔ ∃ (dP : Type) (_ : Fintype dP) (_ : DecidableEq dP),
      c ≤ (value V dP : ℝ) := by
  constructor
  · rintro ⟨dP, hF, hD, P, h⟩
    exact ⟨dP, hF, hD, h.trans (Subtype.coe_le_coe.mpr (le_value V P))⟩
  · rintro ⟨dP, hF, hD, h⟩
    rcases isEmpty_or_nonempty dP with hempty | hn
    · rw [value_of_isEmpty V dP, Prob.coe_zero] at h
      let P : Prover k dM Unit := ⟨default, fun _ => CPTPMap.id⟩
      exact ⟨Unit, inferInstance, inferInstance, P, h.trans Prob.zero_le_coe⟩
    · obtain ⟨P, hP⟩ := exists_acceptProb_eq_value (dP := dP) V
      refine ⟨dP, hF, hD, P, ?_⟩
      rw [hP]
      exact h

/-- Soundness at threshold `s` holds exactly when the value at every finite workspace in `Type`
is at most `s`. At the empty workspace, whose value is `0`, the bound `0 ≤ s` comes from any
prover with workspace `Unit`. -/
lemma soundWith_iff_forall_value (s : ℝ) (V : Verifier k dV dM) :
    SoundWith s V ↔ ∀ (dP : Type) [Fintype dP] [DecidableEq dP], (value V dP : ℝ) ≤ s := by
  constructor
  · intro h dP _ _
    rcases isEmpty_or_nonempty dP with hempty | hn
    · rw [value_of_isEmpty V dP, Prob.coe_zero]
      exact Prob.zero_le_coe.trans (h Unit ⟨default, fun _ => CPTPMap.id⟩)
    · obtain ⟨P, hP⟩ := exists_acceptProb_eq_value (dP := dP) V
      rw [← hP]
      exact h dP P
  · intro h dP _ _ P
    exact (Subtype.coe_le_coe.mpr (le_value V P)).trans (h dP)

/-- Completeness at `2/3` holds exactly when the value at some finite workspace in `Type` is at
least `2/3`. -/
lemma complete_iff_exists_value (V : Verifier k dV dM) :
    Complete V ↔ ∃ (dP : Type) (_ : Fintype dP) (_ : DecidableEq dP),
      (2 / 3 : ℝ) ≤ (value V dP : ℝ) :=
  completeWith_iff_exists_value (2 / 3) V

/-- Soundness at `1/3` holds exactly when the value at every finite workspace in `Type` is at
most `1/3`. -/
lemma sound_iff_forall_value (V : Verifier k dV dM) :
    Sound V ↔ ∀ (dP : Type) [Fintype dP] [DecidableEq dP], (value V dP : ℝ) ≤ 1 / 3 :=
  soundWith_iff_forall_value (1 / 3) V

end PhyslibExt.QuantumInfo.QIP

namespace PhyslibExt.QuantumInfo.QIP

open Cslib.Complexity.Classes PhyslibExt.QuantumInfo.Interaction
  PhyslibExt.QuantumInfo.CircuitBridge

/-- Verifier on input `x` of a gate-list generator: private register of `|x| + a` qubits
holding `x` and zeros, message register of `m` zero qubits; `gen (x, [])` prepares the first
message; after the prover's `(i+1)`-st message it applies `gen (x, true^(i+1))`; it accepts
when global qubit `0` measures `1`. -/
noncomputable def circuitVerifier (a m k : ℕ) (gen : List Bool × List Bool → List QGate)
    (x : List Bool) : Verifier k (Fin (2 ^ (x.length + a))) (Fin (2 ^ m)) where
  init := vecState (x.length + a) m
    (applyCircuit (x.length + a + m) (gen (x, [])) (tensorProd (bqpInitState x a) (zeroState m)))
  step i := circuitChannel (x.length + a) m (gen (x, List.replicate (i.val + 1) true))
  accept := outputPOVM (x.length + a) m

end PhyslibExt.QuantumInfo.QIP

namespace PhyslibExt.QuantumInfo

open Cslib.Complexity.Classes MetaMathlibExt.ComplexityTheory

/-- **QIP:** languages decided by a polynomial-time quantum verifier
exchanging quantum messages with an unbounded prover, in the
verifier-first interaction model: polynomials `a`, `m`, `r`, `s`; a
polynomial-time generator of exact 2-local gate lists, the round index
in unary (`[]` for the first circuit, `true ^ (i + 1)` for the circuit
after the (i+1)-st prover message, `i < r n`); at most `s n`
well-formed gates on `n + a n + m n` qubits per circuit; acceptance is
the computational-basis measurement of global qubit `0` after the last
verifier circuit. Protocols have `2 r n` messages with `r n = 0`
allowed (no messages); a prover-first protocol with an odd number of
messages becomes one of these by adding a verifier message the prover
ignores, which is not formalized here. Message registers have fixed
size and prover workspaces range over finite types in `Type`; the empty
workspace has no strategies and cannot witness completeness, and `Unit`
is the memoryless prover. Total decision problems, with the `BQP` gate
set; completeness at least `2 / 3` and soundness at most `1 / 3`. -/
def QIP : DecisionComplexityClass :=
  {L | ∃ a m r s : Polynomial ℕ, ∃ gen : List Bool × List Bool → List QGate,
    IsPolyTime gen ∧
    (∀ x, ∀ i ≤ r.eval x.length, (gen (x, List.replicate i true)).length ≤ s.eval x.length) ∧
    (∀ x, ∀ i ≤ r.eval x.length, ∀ g ∈ gen (x, List.replicate i true),
      QGateWellFormed (x.length + a.eval x.length + m.eval x.length) g) ∧
    ∀ x,
      (L x = true → QIP.Complete
        (QIP.circuitVerifier (a.eval x.length) (m.eval x.length) (r.eval x.length) gen x)) ∧
      (L x = false → QIP.Sound
        (QIP.circuitVerifier (a.eval x.length) (m.eval x.length) (r.eval x.length) gen x))}

namespace QIP

/-- Membership in `QIP` unfolds to the generator existential. -/
lemma mem_QIP_iff {L : List Bool → Bool} :
    L ∈ QIP ↔ ∃ a m r s : Polynomial ℕ, ∃ gen : List Bool × List Bool → List QGate,
      IsPolyTime gen ∧
      (∀ x, ∀ i ≤ r.eval x.length, (gen (x, List.replicate i true)).length ≤ s.eval x.length) ∧
      (∀ x, ∀ i ≤ r.eval x.length, ∀ g ∈ gen (x, List.replicate i true),
        QGateWellFormed (x.length + a.eval x.length + m.eval x.length) g) ∧
      ∀ x,
        (L x = true → Complete
          (circuitVerifier (a.eval x.length) (m.eval x.length) (r.eval x.length) gen x)) ∧
        (L x = false → Sound
          (circuitVerifier (a.eval x.length) (m.eval x.length) (r.eval x.length) gen x)) :=
  Iff.rfl

end QIP
end PhyslibExt.QuantumInfo

namespace PhyslibExt.QuantumInfo.QIP

open Cslib.Complexity.Classes

/-- A zero-message circuit verifier accepts every prover with the circuit acceptance
probability. -/
lemma acceptProb_circuitVerifier_zero {a m : ℕ} {gen : List Bool × List Bool → List QGate}
    {x : List Bool} {dP : Type*} [Fintype dP] [DecidableEq dP]
    (hwf : ∀ g ∈ gen (x, []), QGateWellFormed (x.length + a + m) g)
    (P : Interaction.Prover 0 (Fin (2 ^ m)) dP) :
    (Interaction.acceptProb (circuitVerifier a m 0 gen x) P : ℝ) =
      Cslib.Complexity.Classes.acceptProb
        (applyCircuit (x.length + a + m) (gen (x, []))
          (tensorProd (bqpInitState x a) (zeroState m))) :=
  by
    have hnorm : sqNorm (applyCircuit (x.length + a + m) (gen (x, []))
        (tensorProd (bqpInitState x a) (zeroState m))) = 1 := by
      rw [sqNorm_applyCircuit hwf, sqNorm_tensorProd, sqNorm_bqpInitState,
        sqNorm_zeroState, mul_one]
    rw [PhyslibExt.QuantumInfo.Interaction.acceptProb_zero]
    exact PhyslibExt.QuantumInfo.CircuitBridge.outputPOVM_measure_vecState hnorm

private lemma complete_circuitVerifier_of_eq_zero {a k m : ℕ}
    {gen : List Bool × List Bool → List QGate} {x : List Bool}
    (hk : k = 0) (hm : m = 0)
    (hwf : ∀ g ∈ gen (x, []), QGateWellFormed (x.length + a + m) g)
    (h : (2 / 3 : ℝ) ≤ Cslib.Complexity.Classes.acceptProb
      (applyCircuit (x.length + a) (gen (x, [])) (bqpInitState x a))) :
    Complete (circuitVerifier a m k gen x) := by
  subst hk
  subst hm
  haveI : Nonempty (MState Unit) := inferInstance
  refine ⟨Unit, inferInstance, inferInstance,
    ⟨Classical.choice inferInstance, fun _ => CPTPMap.id⟩, ?_⟩
  rw [acceptProb_circuitVerifier_zero (m := 0) (dP := Unit) hwf _]
  have hbridge : tensorProd (bqpInitState x a) (zeroState 0) =
      bqpInitState x a := by
    funext s
    have hs : s.val < 2 ^ (x.length + a) := s.isLt
    have hmod : s.val % 2 ^ (x.length + a) = s.val := Nat.mod_eq_of_lt hs
    have hdiv : s.val / 2 ^ (x.length + a) = 0 :=
      Nat.div_eq_zero_iff.mpr (Or.inr hs)
    simp only [tensorProd, zeroState, hmod, hdiv, ite_true, mul_one]
    congr 1
  rw [hbridge]
  exact h

private lemma sound_circuitVerifier_of_eq_zero {a k m : ℕ}
    {gen : List Bool × List Bool → List QGate} {x : List Bool}
    (hk : k = 0) (hm : m = 0)
    (hwf : ∀ g ∈ gen (x, []), QGateWellFormed (x.length + a + m) g)
    (h : Cslib.Complexity.Classes.acceptProb
      (applyCircuit (x.length + a) (gen (x, [])) (bqpInitState x a)) ≤
      1 / 3) :
    Sound (circuitVerifier a m k gen x) := by
  subst hk
  subst hm
  intro dP _ _ P
  have hacc := acceptProb_circuitVerifier_zero (m := 0) hwf P
  rw [hacc]
  have hbridge : tensorProd (bqpInitState x a) (zeroState 0) =
      bqpInitState x a := by
    funext s
    have hs : s.val < 2 ^ (x.length + a) := s.isLt
    have hmod : s.val % 2 ^ (x.length + a) = s.val := Nat.mod_eq_of_lt hs
    have hdiv : s.val / 2 ^ (x.length + a) = 0 :=
      Nat.div_eq_zero_iff.mpr (Or.inr hs)
    simp only [tensorProd, zeroState, hmod, hdiv, ite_true, mul_one]
    congr 1
  rw [hbridge]
  exact h

/-- BQP ⊆ QIP with zero messages: the verifier runs the BQP circuit as its first circuit and
measures its output qubit; every prover, the memoryless one included, is accepted with the
circuit's acceptance probability. -/
theorem bqp_subset_qip : Cslib.Complexity.Classes.BQP ⊆ PhyslibExt.QuantumInfo.QIP :=
  by
    intro L hL
    rw [mem_BQP_iff] at hL
    obtain ⟨a, s, gates, hgates, hsize, hwf, hbounds⟩ := hL
    rw [mem_QIP_iff]
    refine ⟨a, 0, 0, s, gates ∘ Prod.fst, ?_, ?_, ?_, ?_⟩
    · exact MetaMathlibExt.ComplexityTheory.IsPolyTime.comp
        Cslib.Complexity.isPolyTime_fst hgates
    · intro x i hi
      rw [Polynomial.eval_zero] at hi
      obtain rfl : i = 0 := by omega
      exact hsize x
    · intro x i hi g hg
      rw [Polynomial.eval_zero] at hi ⊢
      obtain rfl : i = 0 := by omega
      exact hwf x g hg
    · intro x
      constructor
      · intro hx
        refine complete_circuitVerifier_of_eq_zero (hk := Polynomial.eval_zero)
          (hm := Polynomial.eval_zero) ?_ ((hbounds x).1 hx)
        rw [Polynomial.eval_zero]
        exact hwf x
      · intro hx
        refine sound_circuitVerifier_of_eq_zero (hk := Polynomial.eval_zero)
          (hm := Polynomial.eval_zero) ?_ ((hbounds x).2 hx)
        rw [Polynomial.eval_zero]
        exact hwf x

end PhyslibExt.QuantumInfo.QIP
