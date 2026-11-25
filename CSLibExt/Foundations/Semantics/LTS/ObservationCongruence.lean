/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
Adapted to the upstream weak semantics (`LTS.τSTr`, `LTS.STr`,
`LTS.HomWeakBisimilarity`); the rooted notions are not upstream.
-/

/-
# Rooted observational congruence
-/
module

public import CSLibExt.Foundations.Semantics.LTS.WeakBisimulation

/-!
# Rooted observational congruence for labelled transition systems

Weak bisimilarity may erase an initial silent action, which prevents it from
being a congruence for some process constructors.  This module develops the
standard rooted variant generically for any labelled transition system: an
initial strong transition must be matched by a rooted weak transition, after
which ordinary weak bisimilarity is used.

The construction follows Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib

namespace LTS

variable {State Label : Type*} [HasTau Label] (lts : LTS State Label)

/-- **Rooted weak transition.** In a labelled transition system whose labels include a silent
label $\tau$, there is a rooted weak transition from $s$ to $t$ with label $\mu$ when there are
states $s_1$ and $s_2$ such that $s$ reaches $s_1$ by zero or more $\tau$-transitions,
$s_1 \xrightarrow{\mu} s_2$ is a transition, and $s_2$ reaches $t$ by zero or more
$\tau$-transitions. In particular, a rooted weak transition with label $\tau$ contains at least
one actual $\tau$-transition. -/
def RootedWeakStep (source : State) (label : Label) (target : State) : Prop :=
  ∃ before after,
    lts.τSTr source before ∧
    lts.Tr before label after ∧
    lts.τSTr after target

variable {lts}

/-- **Transitions are rooted weak transitions.** In a labelled transition system with a silent
label $\tau$, every transition $s \xrightarrow{\mu} t$ is a rooted weak transition from $s$ to $t$
with label $\mu$. -/
theorem rootedWeakStep_of_tr {source target : State} {label : Label}
    (hstep : lts.Tr source label target) :
    lts.RootedWeakStep source label target :=
  ⟨source, target, .refl, hstep, .refl⟩

/-- **Rooted weak transitions are weak transitions.** In a labelled transition system with a
silent label $\tau$, every rooted weak transition from $s$ to $t$ with label $\mu$ is a weak
transition from $s$ to $t$ with label $\mu$, where a weak transition with label $\mu$ is either
the trivial step from a state to itself with label $\tau$, or a transition with label $\mu$
preceded and followed by zero or more $\tau$-transitions. -/
theorem RootedWeakStep.toSTr {source target : State} {label : Label}
    (hstep : lts.RootedWeakStep source label target) :
    lts.STr source label target := by
  obtain ⟨before, after, hbefore, hmiddle, hafter⟩ := hstep
  by_cases hlabel : label = HasTau.τ
  · subst label
    exact (sTr_τSTr_iff lts).mpr
      (hbefore.trans ((τSTr.of_tr hmiddle).trans hafter))
  · exact .tr hbefore hmiddle hafter

/-- **Silent steps before a rooted weak transition.** In a labelled transition system with a
silent label $\tau$, if $s$ reaches $m$ by zero or more $\tau$-transitions and there is a rooted
weak transition from $m$ to $t$ with label $\mu$, then there is a rooted weak transition from $s$
to $t$ with label $\mu$. -/
theorem τSTr.rootedWeakStep_trans {source middle target : State}
    {label : Label}
    (hbefore : lts.τSTr source middle)
    (hstep : lts.RootedWeakStep middle label target) :
    lts.RootedWeakStep source label target := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨before, after, hbefore.trans hprefix, hmiddle, hsuffix⟩

/-- **Appending silent steps to a rooted weak transition.** In a labelled transition system with
silent action $\tau$, if there is a rooted weak transition from $s$ to $m$ with label $a$, and $t$
is reachable from $m$ by zero or more $\tau$-transitions, then there is a rooted weak transition
from $s$ to $t$ with label $a$. -/
theorem RootedWeakStep.trans_τSTr {source middle target : State}
    {label : Label}
    (hstep : lts.RootedWeakStep source label middle)
    (hafter : lts.τSTr middle target) :
    lts.RootedWeakStep source label target := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  exact ⟨before, after, hprefix, hmiddle, hsuffix.trans hafter⟩

/-- **A rooted silent step followed by a weak transition is rooted.** In a labelled transition
system with a silent label $\tau$, if there is a rooted weak transition from $s$ to $m$ with
label $\tau$ and a weak transition from $m$ to $t$ with label $\mu$, then there is a rooted weak
transition from $s$ to $t$ with label $\mu$. Here a weak transition with label $\mu$ is either
the trivial step from a state to itself with label $\tau$, or a transition with label $\mu$
preceded and followed by zero or more $\tau$-transitions.

The initial rooted transition supplies the required actual silent step even when the following
weak transition is reflexive. -/
theorem RootedWeakStep.trans_sTr {source middle target : State}
    {label : Label}
    (hrooted : lts.RootedWeakStep source HasTau.τ middle)
    (hweak : lts.STr middle label target) :
    lts.RootedWeakStep source label target := by
  by_cases hlabel : label = HasTau.τ
  · subst label
    exact hrooted.trans_τSTr ((sTr_τSTr_iff lts).mp hweak)
  · obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ :=
      (STr.iff_exists_of_ne hlabel).mp hweak
    have hsource : lts.τSTr source middle :=
      (sTr_τSTr_iff lts).mp hrooted.toSTr
    exact ⟨before, after, hsource.trans hprefix, hmiddle, hsuffix⟩

/-- **Rooted observation congruence.** In a labelled transition system with a silent label
$\tau$, states $p$ and $q$ are rooted weakly bisimilar (observation congruent) when every
transition $p \xrightarrow{\mu} p'$ is matched by a rooted weak transition from $q$ to some $q'$
with label $\mu$ such that $p'$ and $q'$ are weakly bisimilar, and every transition
$q \xrightarrow{\mu} q'$ is matched by a rooted weak transition from $p$ to some $p'$ with label
$\mu$ such that $p'$ and $q'$ are weakly bisimilar. -/
def RootedWeaklyBisimilar (left right : State) : Prop :=
  (∀ ⦃label left'⦄, lts.Tr left label left' →
    ∃ right', lts.RootedWeakStep right label right' ∧
      HomWeakBisimilarity lts left' right') ∧
  (∀ ⦃label right'⦄, lts.Tr right label right' →
    ∃ left', lts.RootedWeakStep left label left' ∧
      HomWeakBisimilarity lts left' right')

@[refl]
theorem observationCongruent_refl (state : State) :
    lts.RootedWeaklyBisimilar state state := by
  constructor <;> intro label next hstep
  · exact ⟨next, rootedWeakStep_of_tr hstep, HomWeakBisimilarity.eqv.refl next⟩
  · exact ⟨next, rootedWeakStep_of_tr hstep, HomWeakBisimilarity.eqv.refl next⟩

theorem RootedWeaklyBisimilar.symm {left right : State}
    (hcongr : lts.RootedWeaklyBisimilar left right) :
    lts.RootedWeaklyBisimilar right left := by
  constructor
  · intro label right' hstep
    obtain ⟨left', hleft', hnext⟩ := hcongr.2 hstep
    exact ⟨left', hleft', HomWeakBisimilarity.eqv.symm hnext⟩
  · intro label left' hstep
    obtain ⟨right', hright', hnext⟩ := hcongr.1 hstep
    exact ⟨right', hright', HomWeakBisimilarity.eqv.symm hnext⟩

/-- **Observation congruence matches rooted weak transitions.** In a labelled transition system
with a silent label $\tau$, if $p$ and $q$ are rooted weakly bisimilar and there is a rooted weak
transition from $p$ to $p'$ with label $\mu$, then there is a state $q'$ with a rooted weak
transition from $q$ to $q'$ with label $\mu$ such that $p'$ and $q'$ are weakly bisimilar. -/
theorem RootedWeaklyBisimilar.match_rootedLeft {left right left' : State}
    {label : Label} (hcongr : lts.RootedWeaklyBisimilar left right)
    (hstep : lts.RootedWeakStep left label left') :
    ∃ right', lts.RootedWeakStep right label right' ∧
      HomWeakBisimilarity lts left' right' := by
  obtain ⟨before, after, hprefix, hmiddle, hsuffix⟩ := hstep
  rcases Relation.ReflTransGen.cases_head hprefix with hEq | ⟨prepared, hhead, htail⟩
  · subst before
    obtain ⟨right', hright', hnext⟩ := hcongr.1 hmiddle
    obtain ⟨right'', hright'', hfinal⟩ :=
      hnext.sTr ((sTr_τSTr_iff lts).mpr hsuffix)
    exact ⟨right'', hright'.trans_τSTr ((sTr_τSTr_iff lts).mp hright''), hfinal⟩
  · have hremainder : lts.RootedWeakStep prepared label left' :=
      τSTr.rootedWeakStep_trans htail
        ⟨before, after, .refl, hmiddle, hsuffix⟩
    obtain ⟨right', hright', hnext⟩ := hcongr.1 hhead
    obtain ⟨right'', hright'', hfinal⟩ :=
      hnext.sTr hremainder.toSTr
    exact ⟨right'', hright'.trans_sTr hright'', hfinal⟩

/-- **Transitivity of rooted observational congruence.** In a labelled transition system with
silent action $\tau$, if $p$ is rooted observationally congruent to $q$ and $q$ is rooted
observationally congruent to $r$, then $p$ is rooted observationally congruent to $r$. -/
@[trans]
theorem RootedWeaklyBisimilar.trans {left middle right : State}
    (hleft : lts.RootedWeaklyBisimilar left middle)
    (hright : lts.RootedWeaklyBisimilar middle right) :
    lts.RootedWeaklyBisimilar left right := by
  constructor
  · intro label left' hstep
    obtain ⟨middle', hmiddle', hleftNext⟩ := hleft.1 hstep
    obtain ⟨right', hright', hrightNext⟩ := hright.match_rootedLeft hmiddle'
    exact ⟨right', hright', HomWeakBisimilarity.eqv.trans hleftNext hrightNext⟩
  · intro label right' hstep
    obtain ⟨middle', hmiddle', hrightNext⟩ := hright.2 hstep
    obtain ⟨left', hleft', hleftNext⟩ := hleft.symm.match_rootedLeft hmiddle'
    exact ⟨left', hleft',
      HomWeakBisimilarity.eqv.trans (HomWeakBisimilarity.eqv.symm hleftNext)
        hrightNext⟩

/-- **Observation congruence is an equivalence relation.** In every labelled transition system
with a silent label $\tau$, rooted weak bisimilarity (observation congruence) is reflexive,
symmetric and transitive. -/
theorem observationCongruent_equivalence :
    Equivalence (lts.RootedWeaklyBisimilar) :=
  ⟨observationCongruent_refl, RootedWeaklyBisimilar.symm,
    RootedWeaklyBisimilar.trans⟩

/-- **Strong bisimilarity implies observation congruence.** In a labelled transition system with
a silent label $\tau$, any two strongly bisimilar states are rooted weakly bisimilar. -/
theorem observationCongruent_of_bisimilar {left right : State}
    (hbisim : HomBisimilarity lts left right) :
    lts.RootedWeaklyBisimilar left right := by
  constructor
  · intro label left' hstep
    obtain ⟨right', hright, hnext⟩ := Bisimilarity.follow_fst hbisim hstep
    exact ⟨right', rootedWeakStep_of_tr hright, HomBisimilarity.to_homWeakBisimilarity hnext⟩
  · intro label right' hstep
    obtain ⟨left', hleft, hnext⟩ := Bisimilarity.follow_snd hbisim hstep
    exact ⟨left', rootedWeakStep_of_tr hleft, HomBisimilarity.to_homWeakBisimilarity hnext⟩

/-- **Observation congruence implies weak bisimilarity.** In a labelled transition system with
a silent label $\tau$, any two rooted weakly bisimilar states are weakly bisimilar. -/
theorem RootedWeaklyBisimilar.to_homWeakBisimilarity {left right : State}
    (hcongr : lts.RootedWeaklyBisimilar left right) :
    HomWeakBisimilarity lts left right := by
  let relation : State → State → Prop := fun p q =>
    lts.RootedWeaklyBisimilar p q ∨ HomWeakBisimilarity lts p q
  have hweak : IsWeakBisimulation lts lts relation := by
    rw [isWeakBisimulation_iff_isSWBisimulation]
    intro p q hpq μ
    constructor
    · intro p' hstep
      rcases hpq with hpq | hpq
      · obtain ⟨q', hq', hnext⟩ := hpq.1 hstep
        exact ⟨q', hq'.toSTr, Or.inr hnext⟩
      · obtain ⟨q', hq', hnext⟩ := hpq.tr hstep
        exact ⟨q', hq', Or.inr hnext⟩
    · intro q' hstep
      rcases hpq with hpq | hpq
      · obtain ⟨p', hp', hnext⟩ := hpq.2 hstep
        exact ⟨p', hp'.toSTr, Or.inr hnext⟩
      · obtain ⟨p', hp', hnext⟩ :=
          (HomWeakBisimilarity.eqv.symm hpq).tr hstep
        exact ⟨p', hp', Or.inr (HomWeakBisimilarity.eqv.symm hnext)⟩
  exact ⟨relation, Or.inl hcongr, hweak⟩

end LTS

end Cslib
