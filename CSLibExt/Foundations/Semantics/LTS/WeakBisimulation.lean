/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
Adapted to the upstream weak semantics (`Cslib.HasTau`, `LTS.τSTr`,
`LTS.STr`, `LTS.saturate`, `LTS.IsWeakBisimulation`,
`LTS.WeakBisimilarity`); only transfer lemmas missing upstream are
proved here.
-/

/-
# Weak bisimulation: transfer lemmas
-/
module

public import CSLibExt.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Semantics.LTS.HasTau

/-!
# Weak transitions and observational equivalence

The weak semantics itself is upstream: silent closure is `LTS.τSTr`,
weak transitions are `LTS.STr` (the transitions of `LTS.saturate`), weak
traces are `LTS.saturate.MTr`, and weak bisimilarity is
`LTS.WeakBisimilarity` / `LTS.HomWeakBisimilarity`.  Recorded here are
the composition and transfer lemmas the process-language developments
use that upstream does not state.

The constructions follow Robin Milner, *Communication and Concurrency*,
Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
-/

@[expose] public section

namespace Cslib

namespace LTS

variable {State Label : Type*} [HasTau Label] {lts : LTS State Label}

/-- **A silent step lies in the silent closure.** In a labelled transition system with a silent
label $\tau$, write $\Rightarrow$ for the silent closure, the reflexive-transitive closure of
the $\tau$-transition relation. If $s \xrightarrow{\tau} t$ is a transition, then
$s \Rightarrow t$. -/
theorem τSTr.of_tr {source target : State}
    (hstep : lts.Tr source HasTau.τ target) : lts.τSTr source target :=
  Relation.ReflTransGen.single hstep

/-- **Prepending a silent step to the silent closure.** In a labelled transition system with a
silent label $\tau$, write $\Rightarrow$ for the silent closure, the reflexive-transitive
closure of the $\tau$-transition relation. If $s \xrightarrow{\tau} m$ is a transition and
$m \Rightarrow t$, then $s \Rightarrow t$. -/
theorem τSTr.cons {source middle target : State}
    (hstep : lts.Tr source HasTau.τ middle) (htail : lts.τSTr middle target) :
    lts.τSTr source target :=
  Relation.ReflTransGen.head hstep htail

/-- **The silent closure is made of runs of silent steps.** In a labelled transition system
with a silent label $\tau$, write $\Rightarrow$ for the silent closure, the
reflexive-transitive closure of the $\tau$-transition relation. Then $s \Rightarrow t$ if and
only if, for some $n \in \mathbb{N}$, there is a multistep transition from $s$ to $t$ whose
list of labels consists of $n$ copies of $\tau$. -/
theorem τSTr_iff_exists_mtr {source target : State} :
    lts.τSTr source target ↔
      ∃ count, lts.MTr source (List.replicate count HasTau.τ) target := by
  constructor
  · intro hclosure
    induction hclosure using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, .refl⟩
    | @head source middle head tail ih =>
        obtain ⟨count, htrace⟩ := ih
        exact ⟨count + 1, by
          simpa [List.replicate_succ] using MTr.stepL head htrace⟩
  · rintro ⟨count, htrace⟩
    induction count generalizing source with
    | zero =>
        simp only [List.replicate_zero, MTr.nil_iff] at htrace
        subst target
        exact .refl
    | succ count ih =>
        rw [List.replicate_succ, MTr.cons_iff] at htrace
        obtain ⟨middle, hstep, htail⟩ := htrace
        exact τSTr.cons hstep (ih htail)

/-- **Weak transitions with a visible label.** In a labelled transition system with a silent
label $\tau$, write $\Rightarrow$ for the reflexive-transitive closure of the
$\tau$-transition relation. A weak transition $s \stackrel{\mu}{\Longrightarrow} t$ is either
the trivial one $s \stackrel{\tau}{\Longrightarrow} s$ or a composite
$s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$. For a label $\mu \ne \tau$,
$s \stackrel{\mu}{\Longrightarrow} t$ holds if and only if there are states $s_1, s_2$ with
$s \Rightarrow s_1$, $s_1 \xrightarrow{\mu} s_2$ and $s_2 \Rightarrow t$. -/
theorem STr.iff_exists_of_ne {source target : State} {label : Label}
    (hne : label ≠ HasTau.τ) :
    lts.STr source label target ↔
      ∃ before after, lts.τSTr source before ∧
        lts.Tr before label after ∧ lts.τSTr after target := by
  constructor
  · intro h
    cases h with
    | refl => exact absurd rfl hne
    | tr hpre hstep hpost => exact ⟨_, _, hpre, hstep, hpost⟩
  · rintro ⟨before, after, hpre, hstep, hpost⟩
    exact .tr hpre hstep hpost

/-- **Silent steps before a weak transition.** Let $L$ be a labelled transition system with a
silent label $\tau$. A weak $\tau$-transition is a sequence of zero or more $\tau$-steps, and for
$\mu \ne \tau$ a weak $\mu$-transition is zero or more $\tau$-steps, one $\mu$-step and zero or
more $\tau$-steps. If a state $s$ reaches a state $m$ by zero or more $\tau$-steps and there is a
weak $\mu$-transition from $m$ to $t$, then there is a weak $\mu$-transition from $s$ to $t$. -/
theorem τSTr.trans_sTr {source middle target : State} {label : Label}
    (hbefore : lts.τSTr source middle) (hstep : lts.STr middle label target) :
    lts.STr source label target := by
  cases hstep with
  | refl => exact (sTr_τSTr_iff lts).mpr hbefore
  | tr hpre hstep hpost => exact .tr (hbefore.trans hpre) hstep hpost

/-- **Silent steps after a weak transition.** Let $L$ be a labelled transition system with a
silent label $\tau$. A weak $\tau$-transition is a sequence of zero or more $\tau$-steps, and for
$\mu \ne \tau$ a weak $\mu$-transition is zero or more $\tau$-steps, one $\mu$-step and zero or
more $\tau$-steps. If there is a weak $\mu$-transition from a state $s$ to a state $m$ and $m$
reaches a state $t$ by zero or more $\tau$-steps, then there is a weak $\mu$-transition from $s$
to $t$. -/
theorem STr.trans_τSTr {source middle target : State} {label : Label}
    (hstep : lts.STr source label middle) (hafter : lts.τSTr middle target) :
    lts.STr source label target := by
  cases hstep with
  | refl => exact (sTr_τSTr_iff lts).mpr hafter
  | tr hpre hstep hpost => exact .tr hpre hstep (hpost.trans hafter)

/-- **Strong traces are weak traces.** Let $L$ be a labelled transition system with a silent
label $\tau$. A weak $\tau$-transition is a sequence of zero or more $\tau$-steps, and for
$\mu \ne \tau$ a weak $\mu$-transition is zero or more $\tau$-steps, one $\mu$-step and zero or
more $\tau$-steps; the saturation of $L$ is the system on the same states whose
$\mu$-transitions are the weak $\mu$-transitions of $L$. If $L$ moves from a state $s$ to a
state $t$ by a sequence of transitions labelled $\mu_1, \dots, \mu_n$, then the saturation of
$L$ moves from $s$ to $t$ by a sequence of transitions with the same labels
$\mu_1, \dots, \mu_n$. -/
theorem MTr.to_saturate {source target : State} {labels : List Label}
    (htrace : lts.MTr source labels target) :
    lts.saturate.MTr source labels target := by
  induction htrace with
  | refl => exact .refl
  | stepL head tail ih => exact .stepL (STr.single head) ih

/-- **Weak bisimilarity is bisimilarity of the saturated system.** In a labelled transition
system with a silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
Thus two states are weakly bisimilar if and only if they are bisimilar in the saturated
system; this holds by definition. -/
theorem HomWeakBisimilarity.iff_homBisimilarity_saturate {left right : State} :
    HomWeakBisimilarity lts left right ↔ HomBisimilarity lts.saturate left right :=
  Iff.rfl

/-- **Weak bisimilarity answers a strong step with a weak step.** Let $L$ be a labelled
transition system with a silent label $\tau$. A weak $\tau$-transition is a sequence of zero or
more $\tau$-steps, and for $\mu \ne \tau$ a weak $\mu$-transition is zero or more $\tau$-steps,
one $\mu$-step and zero or more $\tau$-steps. Two states are weakly bisimilar when some
bisimulation of the system whose $\mu$-transitions are the weak $\mu$-transitions of $L$ relates
them. If $p$ and $q$ are weakly bisimilar and $L$ has a transition from $p$ to $p'$ labelled
$\mu$, then there is a state $q'$ with a weak $\mu$-transition from $q$ to $q'$ such that $p'$
and $q'$ are weakly bisimilar. -/
theorem HomWeakBisimilarity.tr {left right left' : State} {label : Label}
    (hbisim : HomWeakBisimilarity lts left right) (hstep : lts.Tr left label left') :
    ∃ right', lts.STr right label right' ∧ HomWeakBisimilarity lts left' right' := by
  obtain ⟨relation, hrel, hrelation⟩ := hbisim
  have hswb : IsSWBisimulation lts lts relation :=
    isWeakBisimulation_iff_isSWBisimulation.mp hrelation
  obtain ⟨right', hright, hnext⟩ := (hswb hrel label).1 left' hstep
  exact ⟨right', hright, relation, hnext, hrelation⟩

/-- **Weak bisimilarity transfers weak transitions.** In a labelled transition system with a
silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
If $s$ and $t$ are weakly bisimilar and $s \stackrel{\mu}{\Longrightarrow} s'$, then there is a
state $t'$ with $t \stackrel{\mu}{\Longrightarrow} t'$ such that $s'$ and $t'$ are weakly
bisimilar. -/
theorem HomWeakBisimilarity.sTr {left right left' : State} {label : Label}
    (hbisim : HomWeakBisimilarity lts left right)
    (hstep : lts.STr left label left') :
    ∃ right', lts.STr right label right' ∧ HomWeakBisimilarity lts left' right' := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  obtain ⟨right', hright, hnext⟩ := Bisimilarity.follow_fst hsat hstep
  exact ⟨right', hright, hnext⟩

/-- **Weak bisimilarity transfers weak traces.** In a labelled transition system with a
silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
Suppose $s$ and $t$ are weakly bisimilar and $s$ reaches $s'$ by a multistep transition of
the saturated system with label list $\mu_1, \dots, \mu_n$, that is, by weak transitions
$s \stackrel{\mu_1}{\Longrightarrow} \cdots \stackrel{\mu_n}{\Longrightarrow} s'$. Then $t$
reaches some $t'$ by a multistep transition of the saturated system with the same label list,
and $s'$ and $t'$ are weakly bisimilar. -/
theorem HomWeakBisimilarity.saturate_mtr {left right left' : State}
    {labels : List Label}
    (hbisim : HomWeakBisimilarity lts left right)
    (htrace : lts.saturate.MTr left labels left') :
    ∃ right', lts.saturate.MTr right labels right' ∧
      HomWeakBisimilarity lts left' right' := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  obtain ⟨right', hright, hnext⟩ := hsat.mtr htrace
  exact ⟨right', hright, hnext⟩

/-- **Strong bisimilarity implies weak bisimilarity.** In a labelled transition system with a
silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
If two states are bisimilar in the original system, then they are weakly bisimilar. -/
theorem HomBisimilarity.to_homWeakBisimilarity {left right : State}
    (h : HomBisimilarity lts left right) : HomWeakBisimilarity lts left right := by
  obtain ⟨relation, hrel, hbisim⟩ := h
  refine ⟨relation, hrel, ?_⟩
  rw [isWeakBisimulation_iff_isSWBisimulation]
  intro s₁ s₂ hs μ
  constructor
  · intro s₁' hstep
    obtain ⟨s₂', hright, hnext⟩ := (hbisim hs μ).1 s₁' hstep
    exact ⟨s₂', STr.single hright, hnext⟩
  · intro s₂' hstep
    obtain ⟨s₁', hleft, hnext⟩ := (hbisim hs μ).2 s₂' hstep
    exact ⟨s₁', STr.single hleft, hnext⟩

/-- **Weakly bisimilar states enable the same weak labels.** In a labelled transition system
with a silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
If $s$ and $t$ are weakly bisimilar, then for every label $\mu$, there is a weak transition
$s \stackrel{\mu}{\Longrightarrow} s'$ for some $s'$ if and only if there is a weak transition
$t \stackrel{\mu}{\Longrightarrow} t'$ for some $t'$. -/
theorem HomWeakBisimilarity.hasOutLabel_saturate_iff {left right : State}
    (hbisim : HomWeakBisimilarity lts left right) (label : Label) :
    lts.saturate.HasOutLabel left label ↔ lts.saturate.HasOutLabel right label := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  exact hsat.hasOutLabel_iff label

/-- **Weakly bisimilar states have the same set of weak labels.** In a labelled transition
system with a silent label $\tau$, write $\Rightarrow$ for the reflexive-transitive
closure of the $\tau$-transition relation. The weak transitions
$s \stackrel{\mu}{\Longrightarrow} t$ are the trivial ones $s \stackrel{\tau}{\Longrightarrow} s$
and the composites $s \Rightarrow s_1 \xrightarrow{\mu} s_2 \Rightarrow t$; the saturated
system has the same states and has the weak transitions as its transitions. Two states are
weakly bisimilar if some bisimulation of the saturated system relates them.
If $s$ and $t$ are weakly bisimilar, then the set of labels $\mu$ with
$s \stackrel{\mu}{\Longrightarrow} s'$ for some $s'$ equals the set of labels $\mu$ with
$t \stackrel{\mu}{\Longrightarrow} t'$ for some $t'$. -/
theorem HomWeakBisimilarity.outgoingLabels_saturate_eq {left right : State}
    (hbisim : HomWeakBisimilarity lts left right) :
    lts.saturate.outgoingLabels left = lts.saturate.outgoingLabels right := by
  have hsat : HomBisimilarity lts.saturate left right := hbisim
  exact hsat.outgoingLabels_eq

end LTS

end Cslib
