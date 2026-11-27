/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-state CCS agents and weak-bisimulation certificates
-/
module

public import CSLibExt.Languages.CCS.Recursion
public import CSLibExt.Foundations.Semantics.LTS.ObservationCongruence

/-!
# Finite-state CCS agents

Tools for verifying concrete protocols written in the recursive CCS of
`CSLibExt/Languages/CCS/Recursion.lean` (Milner, *Communication and
Concurrency*, Prentice Hall, 1989, Chapters 2-5).

A family of processes `realize : α → Process` indexed by codes `α` *realizes*
a code-level transition function `steps : α → List (Label × α)` when the
processes' transitions are exactly the listed ones (`Realizes`). Realization is
preserved by the operators used to assemble protocols:

* `Realizes.constant`: process constants whose bodies are choices of prefixes
  (`sumOf`), the usual presentation of a finite-state agent;
* `Realizes.parallel`: parallel composition, with the code-level product
  `parSteps` (interleaving plus synchronization of complementary labels);
* `Realizes.restriction`: restriction, filtering the listed labels
  (`restrictSteps`).

`weaklyBisimilar_of_certCheck` turns a finite relation, given as a list of
code pairs, into a weak bisimulation (observation equivalence, Milner,
Chapter 5) once the Boolean check `certCheck` succeeds. Every implementation
step must be matched by staying put (a silent step) or by exactly one
specification step, which suits specifications such as buffers that never
need silent moves to keep up. Every specification step must be matched
directly, or after a silent implementation step to a pair earlier in the list,
so the list order is a ranking that guarantees the silent detours terminate.
`rootedWeaklyBisimilar_of_certCheck` adds a sufficient check of the root
condition (`rootCheck`) and concludes rooted observation congruence.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS

open Cslib.CCS (Label StaticProcess)
open Cslib.CCS.Recursive Cslib.LTS

variable {Name Constant : Type*} [DecidableEq Name]

/-- **Sum of prefixes.** For a list $l$ of pairs $(a, q)$ of a label and a process, the process
that chooses among the prefixes $a.q$ listed in $l$: the empty list gives the inactive process
$\mathbf{0}$, and the list with head $(a, q)$ and tail $r$ gives the choice $a.q + P$ between the
prefix $a.q$ and the process $P$ built in the same way from $r$. -/
def sumOf : List (Label Name × Process Name Constant) → Process Name Constant
  | [] => .nil
  | (a, q) :: rest => .choice (.prefix a q) (sumOf rest)

/-- **Transitions of a sum of prefixes.** For every recursive specification, every list $l$ of
pairs of a label and a process, every label $a$ and every process $q$, the sum of the prefixes
listed in $l$ has a transition labelled $a$ to $q$ exactly when $(a, q)$ belongs to $l$. -/
theorem step_sumOf_iff {spec : Specification Name Constant}
    (l : List (Label Name × Process Name Constant)) (a : Label Name)
    (q : Process Name Constant) :
    Process.Step spec (sumOf l) a q ↔ (a, q) ∈ l := by
  induction l with
  | nil => simpa [sumOf] using Process.nil_no_step
  | cons head rest ih =>
      obtain ⟨b, r⟩ := head
      rw [sumOf, Process.choice_step_iff, Process.prefix_step_iff, ih]
      simp

/-- **Realization of a code-level transition system.** Fix a recursive specification. A family
of processes $P_x$ indexed by codes $x$ realizes a function $s$ that lists, for each code $x$,
labelled transitions $(a, y)$ with $a$ a label and $y$ a code, when for every code $x$, every
label $a$ and every process $q$, the process $P_x$ has a transition with label $a$ to $q$
exactly when $s(x)$ contains an entry $(a, y)$ with $P_y = q$. -/
def Realizes (spec : Specification Name Constant) {α : Type*}
    (realize : α → Process Name Constant) (steps : α → List (Label Name × α)) : Prop :=
  ∀ x a q, Process.Step spec (realize x) a q ↔ ∃ y, (a, y) ∈ steps x ∧ realize y = q

variable {spec : Specification Name Constant}

/-- **Constants listing their transitions realize them.** Fix a recursive specification, a map
$\iota$ from codes to process constants and a function $s$ listing labelled transitions for
each code. Suppose that for every code $x$, writing $(a_1, y_1), \dots, (a_n, y_n)$ for the
entries of $s(x)$ in order, the body of the constant $\iota(x)$ is
$a_1.\iota(y_1) + (a_2.\iota(y_2) + \dots + (a_n.\iota(y_n) + 0))$, which is $0$ when $n = 0$.
Then the processes $\iota(x)$, indexed by codes $x$, realize $s$. -/
theorem Realizes.constant {α : Type*} (inj : α → Constant)
    (steps : α → List (Label Name × α))
    (hspec : ∀ x, spec (inj x) =
      sumOf ((steps x).map fun y => (y.1, Process.constant (inj y.2)))) :
    Realizes spec (fun x => Process.constant (inj x)) steps := by
  intro x a q
  rw [Process.constant_step_iff, hspec, step_sumOf_iff]
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨b, y⟩, hmem, rfl, rfl⟩
    exact ⟨y, hmem, rfl⟩
  · rintro ⟨y, hmem, rfl⟩
    exact ⟨(a, y), hmem, rfl, rfl⟩

/-- **Code-level parallel composition.** Given functions $s$ and $t$ listing the labelled
transitions of codes $x$ and $y$, the transitions of the pair $(x, y)$ are listed in three
blocks: $(a, (x', y))$ for each entry $(a, x')$ of $s(x)$; then $(a, (x, y'))$ for each entry
$(a, y')$ of $t(y)$; then $(\tau, (x', y'))$ for each entry $(a, x')$ of $s(x)$ and each entry
$(b, y')$ of $t(y)$ whose labels are complementary, that is, one is the input and the other the
output on the same name. -/
def parSteps {α β : Type*} (s : α → List (Label Name × α)) (t : β → List (Label Name × β))
    (z : α × β) : List (Label Name × (α × β)) :=
  (s z.1).map (fun y => (y.1, (y.2, z.2))) ++ (t z.2).map (fun w => (w.1, (z.1, w.2))) ++
    (s z.1).flatMap fun y =>
      (t z.2).filterMap fun w => (Label.synchronize y.1 w.1).map fun c => (c, (y.2, w.2))

/-- **Parallel composition preserves realization.** Fix a recursive specification. If the
processes $P_x$ realize $s$ and the processes $Q_y$ realize $t$, then the parallel compositions
$P_x \mid Q_y$, indexed by pairs $(x, y)$, realize the code-level parallel composition of $s$
and $t$. -/
theorem Realizes.parallel {α β : Type*} {f : α → Process Name Constant}
    {g : β → Process Name Constant} {s : α → List (Label Name × α)}
    {t : β → List (Label Name × β)} (hf : Realizes spec f s) (hg : Realizes spec g t) :
    Realizes spec (fun z => .parallel (f z.1) (g z.2)) (parSteps s t) := by
  rintro ⟨x, y⟩ a q
  rw [Process.parallel_step_iff]
  simp only [hf _, hg _, parSteps, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, Option.map_eq_some_iff, Label.synchronize_eq_some_iff,
    Prod.mk.injEq, Prod.exists]
  constructor
  · rintro (⟨_, ⟨x', hx', rfl⟩, rfl⟩ | ⟨_, ⟨y', hy', rfl⟩, rfl⟩ |
      ⟨rfl, b, c, _, _, ⟨x', hx', rfl⟩, ⟨y', hy', rfl⟩, hbc, rfl⟩)
    · exact ⟨x', y, Or.inl (Or.inl ⟨a, x', hx', rfl, rfl, rfl⟩), rfl⟩
    · exact ⟨x, y', Or.inl (Or.inr ⟨a, y', hy', rfl, rfl, rfl⟩), rfl⟩
    · exact ⟨x', y', Or.inr ⟨b, x', hx', c, y', hy', .tau, ⟨rfl, hbc⟩, rfl, rfl, rfl⟩, rfl⟩
  · rintro ⟨x', y', (⟨_, x'', hx'', rfl, rfl, rfl⟩ | ⟨_, y'', hy'', rfl, rfl, rfl⟩) |
      ⟨b, x'', hx'', c, y'', hy'', _, ⟨rfl, hbc⟩, rfl, rfl, rfl⟩, rfl⟩
    · exact Or.inl ⟨_, ⟨x'', hx'', rfl⟩, rfl⟩
    · exact Or.inr (Or.inl ⟨_, ⟨y'', hy'', rfl⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, b, c, _, _, ⟨x'', hx'', rfl⟩, ⟨y'', hy'', rfl⟩, hbc, rfl⟩)

/-- **Boolean restriction test.** For a list $L$ of blocked names, the test returns true on a
label exactly when the label is the silent action $\tau$, or an input or an output on a name
that does not occur in $L$. It is the Boolean form of the condition that restriction by $L$
allows the label. -/
def allowedB (blocked : List Name) : Label Name → Bool
  | .tau => true
  | .input n => !blocked.contains n
  | .output n => !blocked.contains n

theorem allowedB_iff (blocked : List Name) (a : Label Name) :
    allowedB blocked a = true ↔ StaticProcess.Allowed blocked a := by
  cases a <;> simp [allowedB, StaticProcess.Allowed]

/-- **Code-level restriction.** For a list $L$ of blocked names and a function $s$ listing the
labelled transitions of each code, the restricted transitions of a code $x$ are the entries
$(a, y)$ of $s(x)$, in order, whose label $a$ is the silent action $\tau$ or an input or an
output on a name that does not occur in $L$. -/
def restrictSteps {α : Type*} (blocked : List Name) (s : α → List (Label Name × α)) (x : α) :
    List (Label Name × α) :=
  (s x).filter fun y => allowedB blocked y.1

/-- **Restriction preserves realization.** Fix a recursive specification and a list $L$ of
blocked names. If the processes $P_x$ realize $s$, then the restricted processes
$P_x \setminus L$ realize the code-level restriction of $s$ by $L$. -/
theorem Realizes.restriction {α : Type*} {f : α → Process Name Constant}
    {s : α → List (Label Name × α)} (blocked : List Name) (hf : Realizes spec f s) :
    Realizes spec (fun x => .restriction blocked (f x)) (restrictSteps blocked s) := by
  intro x a q
  rw [Process.restriction_step_iff]
  simp only [hf x, restrictSteps, List.mem_filter, allowedB_iff]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hallowed, rfl⟩
    exact ⟨y, ⟨hy, hallowed⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hallowed⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, hallowed, rfl⟩

/-! ## Weak-bisimulation certificates -/

section Certificate

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Forward certificate check.** Let $s$ list the labelled transitions $(a, x')$ of each
implementation code $x$, let $t$ list those of each specification code $y$, and let $R$ be a
finite list of code pairs. The forward check succeeds when for every pair $(x, y)$ in $R$ and
every entry $(a, x')$ of $s(x)$, either $a = \tau$ and $(x', y)$ is in $R$, or some entry
$(a, y')$ of $t(y)$ with the same label has $(x', y')$ in $R$. -/
def forwardCheck (s : α → List (Label Name × α)) (t : β → List (Label Name × β))
    (rel : List (α × β)) : Bool :=
  rel.all fun p => (s p.1).all fun step =>
    (step.1 == .tau && rel.contains (step.2, p.2)) ||
      (t p.2).any fun spec => spec.1 == step.1 && rel.contains (step.2, spec.2)

/-- **Backward certificate check.** Let $s$ list the labelled transitions $(a, x')$ of each
implementation code $x$, let $t$ list those of each specification code $y$, and let $R$ be a
finite list of code pairs. The backward check succeeds when for every pair $(x, y)$ in $R$ and
every entry $(a, y')$ of $t(y)$, at least one of the following holds: $a = \tau$ and
$(x, y')$ is in $R$; some entry $(a, x')$ of $s(x)$ with the same label has $(x', y')$ in $R$;
or some entry $(\tau, x'')$ of $s(x)$ has $(x'', y)$ in $R$, and the first occurrence of
$(x'', y)$ in $R$ comes strictly before the first occurrence of $(x, y)$. -/
def backwardCheck (s : α → List (Label Name × α)) (t : β → List (Label Name × β))
    (rel : List (α × β)) : Bool :=
  rel.all fun p => (t p.2).all fun spec =>
    (spec.1 == .tau && rel.contains (p.1, spec.2)) ||
      ((s p.1).any fun step => step.1 == spec.1 && rel.contains (step.2, spec.2)) ||
      (s p.1).any fun step =>
        step.1 == .tau && rel.contains (step.2, p.2) && rel.idxOf (step.2, p.2) < rel.idxOf p

/-- **Weak-bisimulation certificate check.** For transition lists $s$ of implementation codes
and $t$ of specification codes and a finite list $R$ of code pairs, the certificate check
succeeds when both the forward check and the backward check succeed on $s$, $t$ and $R$. -/
def certCheck (s : α → List (Label Name × α)) (t : β → List (Label Name × β))
    (rel : List (α × β)) : Bool :=
  forwardCheck s t rel && backwardCheck s t rel

variable {f : α → Process Name Constant} {g : β → Process Name Constant}
  {s : α → List (Label Name × α)} {t : β → List (Label Name × β)} {rel : List (α × β)}

private theorem backward_match (hf : Realizes spec f s) (hb : backwardCheck s t rel = true) :
    ∀ (n : Nat) (x : α) (y : β), rel.idxOf (x, y) = n → (x, y) ∈ rel →
      ∀ a y', (a, y') ∈ t y →
        ∃ x', (Process.lts spec).STr (f x) a (f x') ∧ (x', y') ∈ rel := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hxy a y' hy'
    simp only [backwardCheck, List.all_eq_true] at hb
    have h := hb (x, y) hxy (a, y') hy'
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
      List.any_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨rfl, hmem⟩ | ⟨⟨b, x'⟩, hx', rfl, hmem⟩) | ⟨⟨b, x''⟩, hx'', ⟨rfl, hmem⟩, hlt⟩
    · exact ⟨x, STr.refl, hmem⟩
    · have hstep : (Process.lts spec).Tr (f x) b (f x') := (hf x b (f x')).2 ⟨x', hx', rfl⟩
      exact ⟨x', STr.single hstep, hmem⟩
    · have hstep : (Process.lts spec).Tr (f x) .tau (f x'') :=
        (hf x .tau (f x'')).2 ⟨x'', hx'', rfl⟩
      obtain ⟨x', hweak, hmem'⟩ := ih _ (hn ▸ hlt) x'' y rfl hmem a y' hy'
      exact ⟨x', τSTr.trans_sTr (τSTr.of_tr hstep) hweak, hmem'⟩

/-- **Certificate checks give weak bisimilarity.** Let $f$ realize the code-level transition
function $s$ and $g$ realize $t$ for a recursive specification, and let $R$ be a list of code
pairs on which the certificate check of $s$, $t$ and $R$ succeeds. Then for every pair $(x, y)$
in $R$, the processes $f(x)$ and $g(y)$ are weakly bisimilar in the labelled transition system
of the specification. -/
theorem weaklyBisimilar_of_certCheck (hf : Realizes spec f s) (hg : Realizes spec g t)
    (hcheck : certCheck s t rel = true) {x : α} {y : β} (hxy : (x, y) ∈ rel) :
    (Process.lts spec).HomWeakBisimilarity (f x) (g y) := by
  simp only [certCheck, Bool.and_eq_true] at hcheck
  obtain ⟨hfwd, hbwd⟩ := hcheck
  refine ⟨fun P Q => ∃ x y, (x, y) ∈ rel ∧ P = f x ∧ Q = g y, ⟨x, y, hxy, rfl, rfl⟩, ?_⟩
  refine IsSWBisimulation.isWeakBisimulation ?_
  rintro P Q ⟨x, y, hxy, rfl, rfl⟩ a
  constructor
  · intro P' hstep
    obtain ⟨x', hx', rfl⟩ := (hf x a P').1 hstep
    simp only [forwardCheck, List.all_eq_true] at hfwd
    have h := hfwd (x, y) hxy (a, x') hx'
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem,
      List.any_eq_true] at h
    rcases h with ⟨rfl, hmem⟩ | ⟨⟨b, y'⟩, hy', rfl, hmem⟩
    · exact ⟨g y, STr.refl, x', y, hmem, rfl, rfl⟩
    · have hstep' : (Process.lts spec).Tr (g y) b (g y') := (hg y b (g y')).2 ⟨y', hy', rfl⟩
      exact ⟨g y', STr.single hstep', x', y', hmem, rfl, rfl⟩
  · intro Q' hstep
    obtain ⟨y', hy', rfl⟩ := (hg y a Q').1 hstep
    obtain ⟨x', hweak, hmem⟩ := backward_match hf hbwd _ x y rfl hxy a y' hy'
    exact ⟨f x', hweak, x', y', hmem, rfl, rfl⟩

/-- **Direct check of the root condition.** Given code-level transition functions $s$ on codes
$\alpha$ and $t$ on codes $\beta$, each listing labelled steps to codes, a relation $R$ given as
a list of code pairs, and codes $x$ and $y$, the root check succeeds exactly when every listed
step $(a, x')$ of $s(x)$ is matched by some listed step $(a, y')$ of $t(y)$ with the same label
and $(x', y') \in R$, and every listed step $(a, y')$ of $t(y)$ is matched by some listed step
$(a, x')$ of $s(x)$ with the same label and $(x', y') \in R$.

This is a sufficient check of the root condition of observation congruence at $(x, y)$. Rooted
weak bisimilarity also allows silent steps around the matching step, so the check is incomplete. -/
def rootCheck (s : α → List (Label Name × α)) (t : β → List (Label Name × β))
    (rel : List (α × β)) (x : α) (y : β) : Bool :=
  ((s x).all fun step => (t y).any fun spec =>
      spec.1 == step.1 && rel.contains (step.2, spec.2)) &&
    (t y).all fun spec => (s x).any fun step =>
      step.1 == spec.1 && rel.contains (step.2, spec.2)

/-- **Certificate checks give rooted observation congruence.** Let $f$ realize the code-level
transition function $s$ and $g$ realize $t$ for a recursive specification, and let $R$ be a list
of code pairs on which the certificate check of $s$, $t$ and $R$ succeeds. If the root check of
$s$, $t$ and $R$ succeeds at codes $x$ and $y$, then the processes $f(x)$ and $g(y)$ are rooted
weakly bisimilar (observation congruent) in the labelled transition system of the specification
(Milner, Chapter 7). -/
theorem rootedWeaklyBisimilar_of_certCheck (hf : Realizes spec f s) (hg : Realizes spec g t)
    (hcheck : certCheck s t rel = true) {x : α} {y : β} (hroot : rootCheck s t rel x y = true) :
    (Process.lts spec).RootedWeaklyBisimilar (f x) (g y) := by
  simp only [rootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    List.contains_iff_mem] at hroot
  obtain ⟨hleft, hright⟩ := hroot
  constructor
  · intro a P' hstep
    obtain ⟨x', hx', rfl⟩ := (hf x a P').1 hstep
    obtain ⟨⟨b, y'⟩, hy', rfl, hmem⟩ := hleft (a, x') hx'
    exact ⟨g y', LTS.rootedWeakStep_of_tr ((hg y _ _).2 ⟨y', hy', rfl⟩),
      weaklyBisimilar_of_certCheck hf hg hcheck hmem⟩
  · intro a Q' hstep
    obtain ⟨y', hy', rfl⟩ := (hg y a Q').1 hstep
    obtain ⟨⟨b, x'⟩, hx', rfl, hmem⟩ := hright (a, y') hy'
    exact ⟨f x', LTS.rootedWeakStep_of_tr ((hf x _ _).2 ⟨x', hx', rfl⟩),
      weaklyBisimilar_of_certCheck hf hg hcheck hmem⟩

end Certificate

end Cslib.Algorithms.CCS
