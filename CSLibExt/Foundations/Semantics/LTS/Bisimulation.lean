/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `85a3956f8d763f4003659b2ea871b54d9d9f711e`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
Adapted to the upstream `Cslib.LTS` simulation and bisimulation API
(`IsSimulation`, `IsBisimulation`, `Bisimilarity` and their homogeneous
forms); only the consequences missing upstream are proved here.
-/

/-
# Strong bisimulation: trace transfer and outgoing labels
-/
module

public import CSLibExt.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# Strong bisimulation: trace transfer and outgoing labels

Simulation, bisimulation and bisimilarity themselves are the upstream
`Cslib.LTS.IsSimulation`, `Cslib.LTS.IsBisimulation` and
`Cslib.LTS.Bisimilarity` (in their homogeneous forms `IsHomSimulation`,
`IsHomBisimulation`, `HomBisimilarity`).  Recorded here are the facts the
process-semantics development uses that upstream does not state: a
multistep transition transfers across homogeneous bisimilarity, and
bisimilar states have the same outgoing labels.
-/

@[expose] public section

namespace Cslib

namespace LTS

variable {State Label : Type*} {lts : LTS State Label}

/-- **Bisimilarity transfers multistep transitions.** Let $s$ and $t$ be bisimilar states of a
labelled transition system, and suppose $s$ reaches a state $s'$ by a multistep transition along
a finite (possibly empty) list of labels $\mu_1, \dots, \mu_n$. Then there is a state $t'$ such
that $t$ reaches $t'$ by a multistep transition along the same list of labels, and $s'$ and $t'$
are bisimilar. -/
theorem HomBisimilarity.mtr {left right left' : State} {labels : List Label}
    (hbisim : HomBisimilarity lts left right) (htr : lts.MTr left labels left') :
    ∃ right', lts.MTr right labels right' ∧ HomBisimilarity lts left' right' := by
  induction htr generalizing right with
  | refl => exact ⟨right, MTr.refl, hbisim⟩
  | stepL head _tail ih =>
      obtain ⟨middle, hright, hnext⟩ := Bisimilarity.follow_fst hbisim head
      obtain ⟨right', htrace, hfinal⟩ := ih hnext
      exact ⟨right', MTr.stepL hright htrace, hfinal⟩

/-- **Bisimilar states enable the same labels.** Let $s$ and $t$ be bisimilar states of a
labelled transition system. Then for every label $\mu$, $s$ has a transition labelled $\mu$ if
and only if $t$ has a transition labelled $\mu$. -/
theorem HomBisimilarity.hasOutLabel_iff {left right : State}
    (hbisim : HomBisimilarity lts left right) (label : Label) :
    lts.HasOutLabel left label ↔ lts.HasOutLabel right label := by
  constructor
  · rintro ⟨left', hstep⟩
    obtain ⟨right', hright, _⟩ := Bisimilarity.follow_fst hbisim hstep
    exact ⟨right', hright⟩
  · rintro ⟨right', hstep⟩
    obtain ⟨left', hleft, _⟩ := Bisimilarity.follow_snd hbisim hstep
    exact ⟨left', hleft⟩

/-- **Bisimilar states have equal sets of outgoing labels.** Let $s$ and $t$ be bisimilar states
of a labelled transition system. Then the set of labels $\mu$ for which $s$ has a transition
labelled $\mu$ equals the set of labels $\mu$ for which $t$ has a transition labelled $\mu$. -/
theorem HomBisimilarity.outgoingLabels_eq {left right : State}
    (hbisim : HomBisimilarity lts left right) :
    lts.outgoingLabels left = lts.outgoingLabels right := by
  ext label
  exact hbisim.hasOutLabel_iff label

end LTS

end Cslib
