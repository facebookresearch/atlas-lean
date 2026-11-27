/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Computability.Automata.DA.Basic
public import Mathlib.Order.Setoid.Basic

/-!
# The unwinding theorem for noninterference

Goguen and Meseguer's noninterference, in Rushby's formulation. A machine whose actions belong to
security domains is *secure* for a relation `policy` on domains (written $\rightsquigarrow$) if the
output of every action $a$ after an action sequence $\alpha$, run from the initial state, is the
same as after $\alpha$ purged of the actions whose domain may not interfere with that of $a$. The
unwinding theorem reduces this property of action sequences to three conditions on single steps,
stated with an equivalence relation $\sim_u$ on states for each domain $u$.

## Main definitions

* `Cslib.Security.DomainMachine`: a deterministic automaton (`Cslib.Automata.DA`) whose actions
  have outputs and security domains.
* `Cslib.Security.DomainMachine.purge`: deletes from an action sequence the actions whose domain
  may not interfere with a given domain.
* `Cslib.Security.DomainMachine.Secure`: security for a policy.
* `Cslib.Security.DomainMachine.OutputConsistent`, `Cslib.Security.DomainMachine.StepConsistent`
  and `Cslib.Security.DomainMachine.LocallyRespects`: the unwinding conditions.

## Main results

* `Cslib.Security.DomainMachine.view_mtr_purge`: under step consistency and local respect, runs of
  $\alpha$ and of $\alpha$ purged for $u$ from $\sim_u$-equivalent states end in
  $\sim_u$-equivalent states.
* `Cslib.Security.DomainMachine.secure_of_view_mtr_purge`: security follows from output consistency
  when runs from the initial state agree in this sense.
* `Cslib.Security.DomainMachine.unwinding`: the unwinding theorem.

## Implementation notes

A policy is any relation on domains. Rushby takes policies to be reflexive, which none of the
results here needs. Since `purge` keeps the actions whose domain interferes with the given domain,
it needs the policy to be decidable. Runs are CSLib's `Cslib.FLTS.mtr`, which consumes an action
sequence from the left, as Rushby's $\mathrm{run}$ does.

Purge-based security is meant for transitive policies; intransitive (channel-control) policies
need an intransitive purge and another unwinding theorem (Rushby, Chapter 4).

## References

* J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical
  Report CSL-92-02, SRI International, 1992, Chapter 2.
-/

@[expose] public section

namespace Cslib.Security

/-- **Machine with security domains.** A system in the sense of Goguen–Meseguer noninterference:
a deterministic automaton with states $S$, an initial state $s_0$ (`start`) and a transition
function $\mathrm{step} : S \times A \to S$ (`tr`) on actions $A$, together with an output function
$\mathrm{output} : S \times A \to O$ and a security domain $\mathrm{dom}(a) \in D$ of each action
$a$. The state reached from $s$ by an action sequence $\alpha$ is $\mathrm{run}(s, \alpha)$
(`mtr`), with $\mathrm{run}(s, \Lambda) = s$ and
$\mathrm{run}(s, a \circ \alpha) = \mathrm{run}(\mathrm{step}(s, a), \alpha)$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Definition 1. -/
structure DomainMachine (S A O D : Type*) extends Cslib.Automata.DA S A where
  /-- The output of an action performed in a state. -/
  output : S → A → O
  /-- The security domain of an action. -/
  dom : A → D

namespace DomainMachine

variable {S A O D : Type*} (M : DomainMachine S A O D)

/-- **Purge of an action sequence.** For a relation $\rightsquigarrow$ on domains (`policy`), an
action sequence $\alpha$ and a domain $u$, $\mathrm{purge}(\alpha, u)$ is the subsequence of
$\alpha$ formed by deleting every action $a$ with $\mathrm{dom}(a) \not\rightsquigarrow u$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Definition 2. -/
def purge (policy : D → D → Prop) [DecidableRel policy] (α : List A) (u : D) : List A :=
  α.filter fun a => policy (M.dom a) u

section Purge

variable {policy : D → D → Prop} [DecidableRel policy]

@[simp]
theorem purge_nil (u : D) : M.purge policy [] u = [] :=
  rfl

theorem purge_cons_of_pos {a : A} {u : D} (h : policy (M.dom a) u) (α : List A) :
    M.purge policy (a :: α) u = a :: M.purge policy α u :=
  List.filter_cons_of_pos (decide_eq_true h)

theorem purge_cons_of_neg {a : A} {u : D} (h : ¬policy (M.dom a) u) (α : List A) :
    M.purge policy (a :: α) u = M.purge policy α u :=
  List.filter_cons_of_neg (by simpa using h)

end Purge

/-- **Security for a policy.** A machine is secure for a relation $\rightsquigarrow$ on domains
(`policy`) if, for every action sequence $\alpha$ and action $a$, the output of $a$ after running
$\alpha$ from the initial state $s_0$ equals its output after running
$\mathrm{purge}(\alpha, \mathrm{dom}(a))$ from $s_0$:
$\mathrm{output}(\mathrm{run}(s_0, \alpha), a) =
\mathrm{output}(\mathrm{run}(s_0, \mathrm{purge}(\alpha, \mathrm{dom}(a))), a)$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Definition 2. -/
def Secure (policy : D → D → Prop) [DecidableRel policy] : Prop :=
  ∀ (α : List A) (a : A),
    M.output (M.mtr M.start α) a = M.output (M.mtr M.start (M.purge policy α (M.dom a))) a

/-- **Output consistency.** A family of equivalence relations $\sim_u$ on states, one for each
domain $u$ (`view u`), is output consistent if $s \sim_{\mathrm{dom}(a)} t$ implies
$\mathrm{output}(s, a) = \mathrm{output}(t, a)$ for all states $s$, $t$ and actions $a$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Definition 3. -/
def OutputConsistent (view : D → Setoid S) : Prop :=
  ∀ (a : A) (s t : S), view (M.dom a) s t → M.output s a = M.output t a

/-- **Step consistency.** A family of equivalence relations $\sim_u$ on states, one for each
domain $u$ (`view u`), is step consistent if $s \sim_u t$ implies
$\mathrm{step}(s, a) \sim_u \mathrm{step}(t, a)$ for all domains $u$, states $s$, $t$ and
actions $a$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Definition 4. -/
def StepConsistent (view : D → Setoid S) : Prop :=
  ∀ (u : D) (a : A) (s t : S), view u s t → view u (M.tr s a) (M.tr t a)

/-- **Local respect of a policy.** A family of equivalence relations $\sim_u$ on states, one for
each domain $u$ (`view u`), locally respects a relation $\rightsquigarrow$ on domains (`policy`)
if $\mathrm{dom}(a) \not\rightsquigarrow u$ implies $s \sim_u \mathrm{step}(s, a)$ for all
domains $u$, actions $a$ and states $s$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Definition 4. -/
def LocallyRespects (policy : D → D → Prop) (view : D → Setoid S) : Prop :=
  ∀ (u : D) (a : A) (s : S), ¬policy (M.dom a) u → view u s (M.tr s a)

variable {M} {policy : D → D → Prop} [DecidableRel policy] {view : D → Setoid S}

/-- **Runs and purged runs from equivalent states.** Let $\sim_u$ be equivalence relations on the
states of a machine, one for each domain $u$, that are step consistent and locally respect a
relation $\rightsquigarrow$ on domains. If $s \sim_u t$, then
$\mathrm{run}(s, \alpha) \sim_u \mathrm{run}(t, \mathrm{purge}(\alpha, u))$ for every action
sequence $\alpha$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, proof of Theorem 1, equation (2.1). -/
theorem view_mtr_purge (hstep : M.StepConsistent view) (hloc : M.LocallyRespects policy view)
    {u : D} {s t : S} (hst : view u s t) (α : List A) :
    view u (M.mtr s α) (M.mtr t (M.purge policy α u)) := by
  induction α generalizing s t with
  | nil => exact hst
  | cons a α ih =>
    by_cases h : policy (M.dom a) u
    · rw [M.purge_cons_of_pos h]
      exact ih (hstep u a s t hst)
    · rw [M.purge_cons_of_neg h]
      exact ih (Setoid.trans' _ (Setoid.symm' _ (hloc u a s h)) hst)

/-- **Security from views of purged runs.** Let $\rightsquigarrow$ be a relation on the domains of a
machine and $\sim_u$ output consistent equivalence relations on its states, one for each domain $u$.
If $\mathrm{run}(s_0, \alpha) \sim_u \mathrm{run}(s_0, \mathrm{purge}(\alpha, u))$ for every action
sequence $\alpha$ and domain $u$, where $s_0$ is the initial state, then the machine is secure for
$\rightsquigarrow$.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Lemma 1. -/
theorem secure_of_view_mtr_purge (hout : M.OutputConsistent view)
    (h : ∀ (α : List A) (u : D), view u (M.mtr M.start α) (M.mtr M.start (M.purge policy α u))) :
    M.Secure policy :=
  fun α a => hout a _ _ (h α (M.dom a))

/-- **Unwinding theorem.** Let $\rightsquigarrow$ be a relation on the domains of a machine and
$\sim_u$ equivalence relations on its states, one for each domain $u$. If they are output
consistent, step consistent and locally respect $\rightsquigarrow$, then the machine is secure for
$\rightsquigarrow$: for every action sequence $\alpha$ and action $a$,
$\mathrm{output}(\mathrm{run}(s_0, \alpha), a) =
\mathrm{output}(\mathrm{run}(s_0, \mathrm{purge}(\alpha, \mathrm{dom}(a))), a)$, where $s_0$ is
the initial state.

Source: J. Rushby, *Noninterference, transitivity, and channel-control security policies*,
Technical Report CSL-92-02, SRI International, 1992, Theorem 1. -/
theorem unwinding (hout : M.OutputConsistent view) (hstep : M.StepConsistent view)
    (hloc : M.LocallyRespects policy view) : M.Secure policy :=
  secure_of_view_mtr_purge hout fun α _ => view_mtr_purge hstep hloc (Setoid.refl' _ _) α

end DomainMachine

end Cslib.Security
