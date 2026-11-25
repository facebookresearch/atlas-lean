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
the interaction value. The complexity class itself, whose verifier
families are uniform quantum circuits, is built on these predicates
separately; classical-message dephasing and the inclusion of classical
interactive proofs are not treated here.

## ii. Key results

* `Interaction.acceptProb_zero`: with no prover turns, acceptance is the
  verifier's acceptance of its initial state, for every prover.
* `QIP.complete_iff_exists_value` and `QIP.sound_iff_forall_value`:
  completeness and soundness read off the interaction value.

## iii. Table of contents

* `Interaction.acceptProb_zero`: zero-round acceptance.
* `QIP.Complete` and `QIP.Sound`: the acceptance predicates.
* `QIP.complete_iff_exists_value`, `QIP.sound_iff_forall_value`.

## iv. References

Source: J. Watrous, "Quantum computational complexity", in Encyclopedia
of Complexity and Systems Science, Springer, 2009 (arXiv:0804.3401),
Sec. VI.1-VI.2 (completeness at least `2/3`, soundness at most `1/3`);
S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 17
(course-level definition; strict `> 2/3` there).
-/

@[expose] public section

namespace PhyslibExt.QuantumInfo.Interaction

/-- With no prover turns, every prover's acceptance is the verifier's acceptance of its
initial state. -/
lemma acceptProb_zero {dV dM dP : Type*} [Fintype dV] [DecidableEq dV] [Fintype dM]
    [DecidableEq dM] [Fintype dP] [DecidableEq dP] (V : Verifier 0 dV dM)
    (P : Prover 0 dM dP) :
    acceptProb V P = V.accept.measure V.init true := by
  unfold acceptProb
  have hfinal : finalState V P = V.init := by
    unfold finalState
    have hrun : run 0 V.step P.step = CPTPMap.id := rfl
    simp only [hrun, CPTPMap.compose_eq, CPTPMap.id_MState,
      CPTPMap.assoc'_eq_MState_assoc', MState.assoc'_assoc,
      CPTPMap.traceRight_eq_MState_traceRight, MState.traceRight_prod_eq]
  rw [hfinal]

end PhyslibExt.QuantumInfo.Interaction

namespace PhyslibExt.QuantumInfo.QIP

open PhyslibExt.QuantumInfo.Interaction

variable {k : ℕ} {dV dM : Type*} [Fintype dV] [DecidableEq dV] [Fintype dM] [DecidableEq dM]

/-- Completeness at a verifier: some prover with a finite workspace in `Type` is accepted
with probability at least `2/3`. The empty workspace has no strategies and never witnesses
this; the memoryless prover uses `Unit`. -/
def Complete (V : Verifier k dV dM) : Prop :=
  ∃ (dP : Type) (_ : Fintype dP) (_ : DecidableEq dP) (P : Prover k dM dP),
    (2 / 3 : ℝ) ≤ (Interaction.acceptProb V P : ℝ)

/-- Soundness at a verifier: every prover with a finite workspace in `Type` is accepted with
probability at most `1/3`. -/
def Sound (V : Verifier k dV dM) : Prop :=
  ∀ (dP : Type) [Fintype dP] [DecidableEq dP] (P : Prover k dM dP),
    (Interaction.acceptProb V P : ℝ) ≤ 1 / 3

lemma complete_iff_exists_value (V : Verifier k dV dM) :
    Complete V ↔ ∃ (dP : Type) (_ : Fintype dP) (_ : DecidableEq dP),
      (2 / 3 : ℝ) ≤ (value V dP : ℝ) := by
  constructor
  · rintro ⟨dP, hF, hD, P, h⟩
    refine ⟨dP, hF, hD, ?_⟩
    have hle : Interaction.acceptProb V P ≤ value V dP := le_value V P
    have hleR : (Interaction.acceptProb V P : ℝ) ≤ (value V dP : ℝ) :=
      Subtype.coe_le_coe.mpr hle
    exact h.trans hleR
  · rintro ⟨dP, hF, hD, h⟩
    rcases isEmpty_or_nonempty dP with hempty | hn
    · have := hempty
      have hv : value V dP = 0 := value_of_isEmpty V dP
      rw [hv] at h
      norm_num at h
    · have := hn
      obtain ⟨P, hP⟩ := exists_acceptProb_eq_value (dP := dP) V
      refine ⟨dP, hF, hD, P, ?_⟩
      rw [hP]
      exact h

lemma sound_iff_forall_value (V : Verifier k dV dM) :
    Sound V ↔ ∀ (dP : Type) [Fintype dP] [DecidableEq dP], (value V dP : ℝ) ≤ 1 / 3 := by
  constructor
  · intro h dP hF hD
    have hle : value V dP ≤ (⟨1 / 3, by norm_num [Set.mem_Icc]⟩ : Prob) :=
      (value_le_iff V _).mpr (fun P => Subtype.coe_le_coe.mp (h dP P))
    exact Subtype.coe_le_coe.mpr hle
  · intro h dP hF hD P
    have hle : Interaction.acceptProb V P ≤ value V dP := le_value V P
    have hleR : (Interaction.acceptProb V P : ℝ) ≤ (value V dP : ℝ) :=
      Subtype.coe_le_coe.mpr hle
    exact hleR.trans (h dP)

end PhyslibExt.QuantumInfo.QIP
