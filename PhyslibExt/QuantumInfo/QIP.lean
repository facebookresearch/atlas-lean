/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.InteractionAttainment

/-!
# Quantum interactive proofs: acceptance predicates

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

## ii. Key results

* `QIP.completeWith_iff_exists_value` and `QIP.soundWith_iff_forall_value`:
  completeness and soundness at any threshold read off the interaction
  value.
* `QIP.complete_iff_exists_value` and `QIP.sound_iff_forall_value`: the
  same at the thresholds `2/3` and `1/3`.

## iii. Table of contents

* `QIP.CompleteWith` and `QIP.SoundWith`: the acceptance predicates at a
  threshold.
* `QIP.Complete` and `QIP.Sound`: the acceptance predicates at `2/3` and
  `1/3`.
* `QIP.completeWith_iff_exists_value`, `QIP.soundWith_iff_forall_value`,
  `QIP.complete_iff_exists_value`, `QIP.sound_iff_forall_value`: the
  characterizations through the value.

## iv. References

Source: J. Watrous, "Quantum computational complexity", in Encyclopedia
of Complexity and Systems Science, Springer, 2009 (arXiv:0804.3401),
Sec. VI.1 (QIP(m, a, b): completeness at least `a`, soundness at most
`b`; QIP(m) = QIP(m, 2/3, 1/3)); S. Aaronson, MIT 6.845 Quantum
Complexity Theory, Lecture 17 (course-level definition; strict `> 2/3`
there).
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
