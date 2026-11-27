/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Channels
public import QuantumInfo.Measurements.POVM
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.IsBotOne

/-!
# Quantum interaction semantics: alternating channels and the value

## i. Overview

A verifier-first quantum interaction with an even number `2k` of
exchanged messages between a verifier (private register `V`, message
register `M`) and a prover (private register `P`). The verifier's
initial state on `V × M` holds the first message. Each of the `k` rounds
is a prover channel on `M × P` (the prover's message) followed by a
verifier channel on `V × M`; in rounds `1` through `k - 1` that verifier
channel produces the next outgoing message, while in the last round it
feeds directly into the final two-outcome POVM on `V × M` and is an
action, not an exchanged message. Counted this way the exchanged
messages are the initial one, `k` prover messages, and `k - 1` further
verifier messages: `2k` in total (for `k = 0` there are none and the
initial state is measured directly). Odd-message schedules in which the
prover moves first are not represented by this API.

The value at a fixed finite prover workspace
`dP` is the supremum of the acceptance probability over all prover
strategies, an element of `Prob` (the unit interval with its complete
linear order), so the supremum is always well-defined; attainment is a
separate compactness statement not proved here. Register index types
are intended as nonempty finite alphabets (the finite-dimensional
spaces of the sources); the empty-index case is recorded only as the
degenerate `value_of_isEmpty` artifact.

## ii. Key results

* `value_zero`: with no prover turns, the value is the verifier's
acceptance of its initial state; `acceptProb_zero` states the same for
each prover.
* `value_le_iff`: the value is the least upper bound of the acceptance
probabilities.
* `run_succ_apply`: the action of `run` on a state is the last round
after the earlier rounds.

## iii. Table of contents

* `Verifier` and `Prover`: the interaction parties.
* `round` and `run`: one round and the channel of `k` rounds.
* `run_succ` and `run_succ_apply`: unfolding one round of `run`.
* `finalState`, `acceptProb`, and `value`: final state, acceptance
probability, and the value.
* `le_value` and `value_le_iff`: the value as least upper bound.
* `acceptProb_zero` and `value_zero`: the zero-message acceptance and
value.
* `value_of_isEmpty`: the empty-index artifact.

## iv. References

Source: J. Watrous, "Quantum computational complexity", in Encyclopedia
of Complexity and Systems Science, Springer, 2009 (arXiv:0804.3401),
Section on quantum interactive proof systems; A. Kitaev and J. Watrous,
"Parallelization, amplification, and exponential time simulation of
quantum interactive proof systems", STOC 2000, Section 2.
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.Interaction

set_option autoImplicit false

variable {dV dM dP : Type*} [Fintype dV] [DecidableEq dV] [Fintype dM]
  [DecidableEq dM] [Fintype dP] [DecidableEq dP]

/-- **Verifier** of a quantum interaction: an initial state on `V × M`,
one channel per round on `V × M` (the prover moves first), and a
two-outcome acceptance measurement. -/
structure Verifier (k : ℕ) (dV dM : Type*) [Fintype dV] [DecidableEq dV]
    [Fintype dM] [DecidableEq dM] where
  /-- Initial joint state of the verifier and message registers. -/
  init : MState (dV × dM)
  /-- The verifier's channel in each round. -/
  step : Fin k → CPTPMap (dV × dM) (dV × dM)
  /-- Acceptance measurement (`true` accepts). -/
  accept : POVM Bool (dV × dM)

/-- **Prover** of a quantum interaction: a private initial state and one
channel per round on the message and private registers. -/
structure Prover (k : ℕ) (dM dP : Type*) [Fintype dM] [DecidableEq dM]
    [Fintype dP] [DecidableEq dP] where
  /-- Initial private state. -/
  init : MState dP
  /-- The prover's channel in each round. -/
  step : Fin k → CPTPMap (dM × dP) (dM × dP)

/-- **One round** on the triple of registers: the prover acts on
`M × P`, then the verifier acts on `V × M`. -/
noncomputable def round (Vi : CPTPMap (dV × dM) (dV × dM))
    (Pi : CPTPMap (dM × dP) (dM × dP)) :
    CPTPMap (dV × dM × dP) (dV × dM × dP) :=
  (CPTPMap.assoc ∘ₘ (Vi ⊗ᶜᵖ CPTPMap.id) ∘ₘ CPTPMap.assoc') ∘ₘ
    (CPTPMap.id ⊗ᶜᵖ Pi)

/-- **The channel of `k` rounds** of alternating verifier and prover
channels. -/
noncomputable def run : (k : ℕ) → (Fin k → CPTPMap (dV × dM) (dV × dM)) →
    (Fin k → CPTPMap (dM × dP) (dM × dP)) →
    CPTPMap (dV × dM × dP) (dV × dM × dP)
  | 0, _, _ => CPTPMap.id
  | k + 1, Vs, Ps => round (Vs (Fin.last k)) (Ps (Fin.last k)) ∘ₘ
      run k (fun i => Vs i.castSucc) (fun i => Ps i.castSucc)

/-- Unfolding one round of `run` (the `CPTPMap` composition interface). -/
lemma run_succ (k : ℕ) (Vs : Fin (k + 1) → CPTPMap (dV × dM) (dV × dM))
    (Ps : Fin (k + 1) → CPTPMap (dM × dP) (dM × dP)) :
    run (k + 1) Vs Ps = round (Vs (Fin.last k)) (Ps (Fin.last k)) ∘ₘ
      run k (fun i => Vs i.castSucc) (fun i => Ps i.castSucc) := by
  rfl

/-- The action of `run` on a state is the last round after the earlier
rounds. -/
lemma run_succ_apply (k : ℕ)
    (Vs : Fin (k + 1) → CPTPMap (dV × dM) (dV × dM))
    (Ps : Fin (k + 1) → CPTPMap (dM × dP) (dM × dP))
    (ρ : MState (dV × dM × dP)) :
    run (k + 1) Vs Ps ρ =
      round (Vs (Fin.last k)) (Ps (Fin.last k))
        (run k (fun i => Vs i.castSucc) (fun i => Ps i.castSucc) ρ) := by
  rw [run_succ, CPTPMap.compose_eq]

/-- **Final state** on `V × M` after the interaction: tensor the initial
states, run the rounds, reassociate, and discard the prover register. -/
noncomputable def finalState {k : ℕ} (V : Verifier k dV dM)
    (P : Prover k dM dP) : MState (dV × dM) :=
  (CPTPMap.traceRight ∘ₘ CPTPMap.assoc' ∘ₘ run k V.step P.step)
    (V.init ⊗ᴹ P.init).assoc

/-- **Acceptance probability** of an interaction. -/
noncomputable def acceptProb {k : ℕ} (V : Verifier k dV dM)
    (P : Prover k dM dP) : Prob :=
  V.accept.measure (finalState V P) true

/-- **Value of a verifier** at prover workspace `dP`: the supremum of the
acceptance probability over all prover strategies. -/
noncomputable def value {k : ℕ} (V : Verifier k dV dM) (dP : Type*)
    [Fintype dP] [DecidableEq dP] : Prob :=
  ⨆ P : Prover k dM dP, acceptProb V P

/-- Every prover's acceptance is at most the value. -/
lemma le_value {k : ℕ} (V : Verifier k dV dM) (P : Prover k dM dP) :
    acceptProb V P ≤ value V dP := by
  unfold value
  exact le_ciSup (OrderTop.bddAbove _) P

/-- The value is the least upper bound of the acceptance probabilities. -/
lemma value_le_iff {k : ℕ} (V : Verifier k dV dM) (p : Prob) :
    value V dP ≤ p ↔ ∀ P : Prover k dM dP, acceptProb V P ≤ p := by
  constructor
  · intro h P
    exact (le_value V P).trans h
  · intro h
    unfold value
    exact ciSup_le' h

/-- With no prover turns, every prover's acceptance is the verifier's acceptance of its
initial state. -/
lemma acceptProb_zero (V : Verifier 0 dV dM) (P : Prover 0 dM dP) :
    acceptProb V P = V.accept.measure V.init true := by
  unfold acceptProb
  have hfinal : finalState V P = V.init := by
    unfold finalState
    have hrun : run 0 V.step P.step = CPTPMap.id := rfl
    simp only [hrun, CPTPMap.compose_eq, CPTPMap.id_MState,
      CPTPMap.assoc'_eq_MState_assoc', MState.assoc'_assoc,
      CPTPMap.traceRight_eq_MState_traceRight, MState.traceRight_prod_eq]
  rw [hfinal]

/-- **Zero-message nonvacuity:** with no prover turns, the value is the
verifier's acceptance of its initial state. -/
lemma value_zero [Nonempty dP] (V : Verifier 0 dV dM) :
    value V dP = V.accept.measure V.init true := by
  haveI hne : Nonempty (Prover 0 dM dP) := by
    haveI : Nonempty (MState dP) := inferInstance
    exact ⟨⟨Classical.choice inferInstance, fun i => i.elim0⟩⟩
  unfold value
  simp only [acceptProb_zero, ciSup_const]

/-- Zero-dimensional artifact: with an empty index type there is no
density operator at all, so there are no prover strategies and the value
is `0`. This is not the memoryless prover: no private workspace is the
one-dimensional register `Unit`, which does have strategies (see the
tests). -/
lemma value_of_isEmpty {k : ℕ} (V : Verifier k dV dM) (dE : Type*)
    [Fintype dE] [DecidableEq dE] [IsEmpty dE] :
    value V dE = 0 := by
  haveI : IsEmpty (MState dE) := ⟨fun ρ => (inferInstance : IsEmpty dE).elim (Classical.choice ρ.nonempty)⟩
  haveI : IsEmpty (Prover k dM dE) := Function.isEmpty (fun P => P.init)
  unfold value
  rw [ciSup_of_empty]
  exact bot_eq_zero

end PhyslibExt.QuantumInfo.Interaction
