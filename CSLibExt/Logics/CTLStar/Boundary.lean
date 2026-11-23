/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Logics.CTLStar.Basic

/-!
# Deadlock boundary of infinite-run CTL*

CTL* quantifies only over infinite runs. At a terminal state `E π` is
false and `A π` is vacuous, unlike maximal-path CTL's `AU` at deadlock.
These are boundary results for the port, not an expressiveness claim.
-/

@[expose] public section

namespace Cslib.CTLStar

variable {State Label Atom : Type*} {lts : LTS State Label}
  {valuation : State → Atom → Prop} {s : State} {π : PathFormula Atom}

/-- No existential infinite path formula holds at a terminal state. -/
theorem not_stateSat_exists_of_terminal (hdead : lts.IsTerminal s) :
    ¬StateSat lts valuation (.exists π) s := by
  rintro ⟨run, h0, hrun, _⟩
  obtain ⟨label, hstep⟩ := hrun 0
  rw [h0] at hstep
  exact hdead label _ hstep

/-- Universal infinite path quantification is vacuous at a terminal state. -/
theorem stateSat_forall_of_terminal (hdead : lts.IsTerminal s) :
    StateSat lts valuation (.forall π) s := by
  intro run h0 hrun
  obtain ⟨label, hstep⟩ := hrun 0
  rw [h0] at hstep
  exact (hdead label _ hstep).elim

end Cslib.CTLStar
