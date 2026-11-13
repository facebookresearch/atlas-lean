/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Classes

/-!
# Running two single-tape machines one after the other

CSLib's `SingleTapeTM.compComputer tm1 tm2` runs `tm1` and, when it halts, starts `tm2` on the
tape `tm1` left. Upstream proves its correctness only inside `TimeComputable.comp`, for total
functions with time bounds, through private lemmas. This file states the facts for single runs,
which is what a composition with a possibly non-halting second machine needs:

* `Outputs.compComputer`, `OutputsWithinTime.compComputer`: outputs compose (time bounds add).
* `haltsOn_compComputer_iff`: if `tm1` outputs `b` on `a`, the composite halts on `a` iff `tm2`
  halts on `b`.

The proofs embed the two machines' configurations into the composite (`compCfgLeft`,
`compCfgRight`, public versions of upstream's private `toCompCfg_left` / `toCompCfg_right`) and
use that machines are deterministic (`rightUnique_transitionRelation`).

## Main results

- `Cslib.Turing.SingleTapeTM.Outputs.compComputer`,
  `Cslib.Turing.SingleTapeTM.OutputsWithinTime.compComputer`,
  `Cslib.Turing.SingleTapeTM.haltsOn_compComputer_iff`.
-/

@[expose] public section

set_option autoImplicit false

open Relation

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm1 tm2 : SingleTapeTM Symbol)

/-- **Embedding the first machine's configurations into a composite.** Let $M_1$ and $M_2$ be
single-tape Turing machines over the same alphabet, and let $M$ be their composite, whose states
are the disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and
runs $M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs
$M_2$ and halts where $M_2$ halts. A configuration of $M_1$ with tape $t$ is sent to the
configuration of $M$ with the same tape $t$ whose state is the copy of $q$ if $M_1$ is in state
$q$, and the start state of $M_2$ if $M_1$ has halted.

Source: public version of upstream CSLib's private `toCompCfg_left`. -/
def compCfgLeft (c : tm1.Cfg) : (compComputer tm1 tm2).Cfg :=
  ⟨some (c.state.elim (.inr tm2.q₀) .inl), c.BiTape⟩

/-- **Embedding the second machine's configurations into a composite.** Let $M_1$ and $M_2$ be
single-tape Turing machines over the same alphabet, and let $M$ be their composite, whose states
are the disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and
runs $M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs
$M_2$ and halts where $M_2$ halts. A configuration of $M_2$ with tape $t$ is sent to the
configuration of $M$ with the same tape $t$ whose state is the copy of $q$ if $M_2$ is in state
$q$, and which is halted if $M_2$ has halted.

Source: public version of upstream CSLib's private `toCompCfg_right`. -/
def compCfgRight (c : tm2.Cfg) : (compComputer tm1 tm2).Cfg :=
  ⟨c.state.map .inr, c.BiTape⟩

variable {tm1 tm2}

/-- **The composite simulates steps of the first machine.** Let $M_1$ and $M_2$ be single-tape
Turing machines over the same alphabet, and let $M$ be their composite, whose states are the
disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and runs
$M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs $M_2$
and halts where $M_2$ halts. Let $\iota_1$ send a configuration of $M_1$ to the configuration of
$M$ with the same tape whose state is the copy of the state of $M_1$, or the start state of $M_2$
if $M_1$ has halted. If $M_1$ moves from a configuration $c$ to a configuration $c'$ in one step,
then $M$ moves from $\iota_1(c)$ to $\iota_1(c')$ in one step.

Source: upstream CSLib's private `map_toCompCfg_left_step`, stated as a relation. -/
theorem transitionRelation_compCfgLeft {c c' : tm1.Cfg} (h : tm1.TransitionRelation c c') :
    (compComputer tm1 tm2).TransitionRelation (compCfgLeft tm1 tm2 c) (compCfgLeft tm1 tm2 c') := by
  obtain ⟨s, t⟩ := c
  cases s with
  | none => simp [TransitionRelation, step] at h
  | some q =>
    simp only [TransitionRelation, step] at h
    generalize hM : tm1.tr q t.head = r at h
    obtain ⟨⟨wr, dir⟩, q'⟩ := r
    obtain rfl := Option.some_injective _ h
    simp only [TransitionRelation, step, compCfgLeft, Option.elim_some, compComputer, hM]
    cases q' <;> rfl

/-- **Step function of a composite on configurations of the second machine.** Let $M_1$ and $M_2$
be single-tape Turing machines over the same alphabet, and let $M$ be their composite, whose
states are the disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of
$M_1$ and runs $M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it
then runs $M_2$ and halts where $M_2$ halts. Let $\iota_2$ send a configuration of $M_2$ to the
configuration of $M$ with the same tape whose state is the copy of the state of $M_2$, halted if
$M_2$ has halted. For every configuration $c$ of $M_2$: if $M_2$ moves from $c$ to $c'$ in one
step, then $M$ moves from $\iota_2(c)$ to $\iota_2(c')$ in one step, and if $c$ has no successor
in $M_2$, then $\iota_2(c)$ has no successor in $M$.

Source: upstream CSLib's private `map_toCompCfg_right_step`. -/
theorem step_compCfgRight (c : tm2.Cfg) :
    (compComputer tm1 tm2).step (compCfgRight tm1 tm2 c) =
      (tm2.step c).map (compCfgRight tm1 tm2) := by
  obtain ⟨s, t⟩ := c
  cases s with
  | none => rfl
  | some q =>
    rcases hM : tm2.tr q t.head with ⟨stmt, q'⟩
    have e : compCfgRight tm1 tm2 ⟨some q, t⟩ = ⟨some (.inr q), t⟩ := rfl
    rw [e]
    cases q' <;> simp only [step, compComputer, hM, Option.map_some] <;> rfl

/-- **The composite simulates steps of the second machine.** Let $M_1$ and $M_2$ be single-tape
Turing machines over the same alphabet, and let $M$ be their composite, whose states are the
disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and runs
$M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs $M_2$
and halts where $M_2$ halts. Let $\iota_2$ send a configuration of $M_2$ to the configuration of
$M$ with the same tape whose state is the copy of the state of $M_2$, halted if $M_2$ has halted.
If $M_2$ moves from a configuration $c$ to a configuration $c'$ in one step, then $M$ moves from
$\iota_2(c)$ to $\iota_2(c')$ in one step. -/
theorem transitionRelation_compCfgRight {c c' : tm2.Cfg} (h : tm2.TransitionRelation c c') :
    (compComputer tm1 tm2).TransitionRelation (compCfgRight tm1 tm2 c)
      (compCfgRight tm1 tm2 c') := by
  simp only [TransitionRelation, step_compCfgRight] at h ⊢
  rw [h, Option.map_some]

/-- **Runs of a composite from configurations of the second machine.** Let $M_1$ and $M_2$ be
single-tape Turing machines over the same alphabet, and let $M$ be their composite, whose states
are the disjoint union of those of $M_1$ and of $M_2$: $M$ starts in the start state of $M_1$ and
runs $M_1$, where $M_1$ would halt it enters the start state of $M_2$ instead, and it then runs
$M_2$ and halts where $M_2$ halts. Let $\iota_2$ send a configuration of $M_2$ to the
configuration of $M$ with the same tape whose state is the copy of the state of $M_2$, halted if
$M_2$ has halted. If $c$ is a configuration of $M_2$ and $M$ moves from $\iota_2(c)$ to a
configuration $d$ in finitely many (possibly zero) steps, then there is a configuration $c'$ of
$M_2$ such that $M_2$ moves from $c$ to $c'$ in finitely many (possibly zero) steps and
$d = \iota_2(c')$. -/
theorem exists_of_reflTransGen_compCfgRight {c : tm2.Cfg} {d : (compComputer tm1 tm2).Cfg}
    (h : ReflTransGen (compComputer tm1 tm2).TransitionRelation (compCfgRight tm1 tm2 c) d) :
    ∃ c', ReflTransGen tm2.TransitionRelation c c' ∧ d = compCfgRight tm1 tm2 c' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨c', hc', rfl⟩ := ih
    simp only [TransitionRelation, step_compCfgRight] at hstep
    obtain ⟨c'', hc'', rfl⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨c'', hc'.tail hc'', rfl⟩

/-- **Outputs compose.** Let $M_1$ and $M_2$ be single-tape Turing machines over the same
alphabet, and let $M$ be their composite, whose states are the disjoint union of those of $M_1$
and of $M_2$: $M$ starts in the start state of $M_1$ and runs $M_1$, where $M_1$ would halt it
enters the start state of $M_2$ instead, and it then runs $M_2$ and halts where $M_2$ halts. Say
that a machine outputs a word $w$ on a word $v$ when, started in its start state on a tape
holding $v$, it reaches the halted configuration whose tape holds exactly $w$, with the head at
the start of $w$. For all words $a$, $b$, $c$: if $M_1$ outputs $b$ on $a$ and $M_2$ outputs $c$
on $b$, then $M$ outputs $c$ on $a$. -/
theorem Outputs.compComputer {a b c : List Symbol} (h₁ : tm1.Outputs a b)
    (h₂ : tm2.Outputs b c) : (compComputer tm1 tm2).Outputs a c :=
  (h₁.lift (compCfgLeft tm1 tm2) fun _ _ ↦ transitionRelation_compCfgLeft).trans
    (h₂.lift (compCfgRight tm1 tm2) fun _ _ ↦ transitionRelation_compCfgRight)

/-- **Timed outputs compose.** Let $M_1$ and $M_2$ be single-tape Turing machines over the same
alphabet, and let $M$ be their composite, whose states are the disjoint union of those of $M_1$
and of $M_2$: $M$ starts in the start state of $M_1$ and runs $M_1$, where $M_1$ would halt it
enters the start state of $M_2$ instead, and it then runs $M_2$ and halts where $M_2$ halts. Say
that a machine outputs a word $w$ on a word $v$ within $t$ steps when, started in its start state
on a tape holding $v$, it reaches in at most $t$ steps the halted configuration whose tape holds
exactly $w$, with the head at the start of $w$. For all words $a$, $b$, $c$ and all natural
numbers $t_1$, $t_2$: if $M_1$ outputs $b$ on $a$ within $t_1$ steps and $M_2$ outputs $c$ on $b$
within $t_2$ steps, then $M$ outputs $c$ on $a$ within $t_1 + t_2$ steps. -/
theorem OutputsWithinTime.compComputer {a b c : List Symbol} {t₁ t₂ : ℕ}
    (h₁ : tm1.OutputsWithinTime a b t₁) (h₂ : tm2.OutputsWithinTime b c t₂) :
    (compComputer tm1 tm2).OutputsWithinTime a c (t₁ + t₂) :=
  (h₁.map (compCfgLeft tm1 tm2) fun _ _ ↦ transitionRelation_compCfgLeft).trans
    (h₂.map (compCfgRight tm1 tm2) fun _ _ ↦ transitionRelation_compCfgRight)

/-- **Halting of a composite.** Let $M_1$ and $M_2$ be single-tape Turing machines over the same
alphabet, and let $M$ be their composite, whose states are the disjoint union of those of $M_1$
and of $M_2$: $M$ starts in the start state of $M_1$ and runs $M_1$, where $M_1$ would halt it
enters the start state of $M_2$ instead, and it then runs $M_2$ and halts where $M_2$ halts. Say
that a machine outputs a word $w$ on a word $v$ when, started in its start state on a tape
holding $v$, it reaches the halted configuration whose tape holds exactly $w$, with the head at
the start of $w$. For all words $a$ and $b$ such that $M_1$ outputs $b$ on $a$: $M$, started in
its start state on a tape holding $a$, halts if and only if $M_2$, started in its start state on
a tape holding $b$, halts. -/
theorem haltsOn_compComputer_iff {a b : List Symbol} (h₁ : tm1.Outputs a b) :
    (compComputer tm1 tm2).HaltsOn a ↔ tm2.HaltsOn b := by
  have hmid : ReflTransGen (compComputer tm1 tm2).TransitionRelation
      ((compComputer tm1 tm2).initCfg a) (compCfgRight tm1 tm2 (tm2.initCfg b)) :=
    h₁.lift (compCfgLeft tm1 tm2) fun _ _ ↦ transitionRelation_compCfgLeft
  constructor
  · rintro ⟨d, hd, hstate⟩
    rcases hmid.total_of_right_unique (rightUnique_transitionRelation _) hd with h | h
    · obtain ⟨c', hc', rfl⟩ := exists_of_reflTransGen_compCfgRight h
      refine ⟨c', hc', ?_⟩
      exact Option.map_eq_none_iff.mp hstate
    · -- a halted configuration has no successor, so it is the middle one, which is running
      rcases h.cases_head with h | ⟨e, he, -⟩
      · rw [h] at hstate
        have e : (compCfgRight tm1 tm2 (tm2.initCfg b)).state = some (.inr tm2.q₀) := rfl
        rw [e] at hstate
        cases hstate
      · obtain ⟨s, t⟩ := d
        simp only at hstate
        subst hstate
        simp [TransitionRelation, step] at he
  · rintro ⟨c', hc', hstate⟩
    refine ⟨compCfgRight tm1 tm2 c', hmid.trans (hc'.lift (compCfgRight tm1 tm2) fun _ _ ↦
      transitionRelation_compCfgRight), ?_⟩
    change Option.map _ c'.state = none
    rw [hstate]
    rfl

end Cslib.Turing.SingleTapeTM
