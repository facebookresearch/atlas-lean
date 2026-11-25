/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.Language

/-!
# Pushdown automata

A pushdown automaton with acceptance by empty stack. Transitions are
finitely branching, always pop the top stack symbol, and push a (possibly
empty) list of symbols in its place; the head of the pushed list becomes the
new stack top. A transition either consumes one input letter or is an
`ε`-transition consuming none.

## Main definitions

* `Cslib.Automata.PDA`: the automaton, with `step`, `start`, and an initial
  stack symbol `startStack`.
* `Cslib.Automata.PDA.Config`, `PDA.Step`, `PDA.Derives`: configurations
  and one/many-step computation.
* `PDA.accepts`: the language accepted by empty stack from the initial
  configuration.
* `PDA.restrict`: restriction of the stack alphabet to a finite
  `PDA.ClosedUnder` set, without changing the accepted language.

## Main results

* `Cslib.Automata.PDA.Derives.append_input_stack`: computations are
  independent of the input suffix and the bottom of the stack below the
  part being rewritten.
* `Cslib.Automata.PDA.accepts_restrict`: restricting the stack alphabet
  to a finite closed set does not change the accepted language.
-/

@[expose] public section

namespace Cslib.Automata

/-- **Pushdown automaton.** A pushdown automaton over an input alphabet $T$, with
states in $\sigma$ and stack alphabet $\Gamma$, consists of a transition function, a start
state in $\sigma$ and an initial stack symbol in $\Gamma$. The transition function assigns
to each state $q$, each input option (a letter of $T$, or none for an
$\varepsilon$-transition) and each popped stack symbol $\gamma$ a finite set of pairs
$(q', u)$ of a next state $q'$ and a list $u$ of stack symbols to push.

This is the generalized model: the state and stack types themselves are unrestricted,
and only each transition is finitely branching. A standard (textbook) pushdown
automaton is additionally finitely supported; without that, the language it accepts can
be an arbitrary language, so the conversion from pushdown automata back to context-free
grammars needs finiteness hypotheses. -/
structure PDA (T : Type*) (σ : Type*) (Γ : Type*) where
  /-- The finitely branching transition function. -/
  step : σ → Option T → Γ → Finset (σ × List Γ)
  /-- The initial state. -/
  start : σ
  /-- The sole initial stack symbol. -/
  startStack : Γ

namespace PDA

variable {T : Type*} {σ : Type*} {Γ : Type*} {M : PDA T σ Γ}

/-- **Pushdown automaton configuration.** A configuration of a pushdown automaton with input
alphabet $T$, states in $\sigma$ and stack alphabet $\Gamma$ consists of a current state in
$\sigma$, the remaining unread input (a word over $T$), and the stack contents (a list over
$\Gamma$ whose first element is the top of the stack). -/
structure Config (T : Type*) (σ : Type*) (Γ : Type*) where
  /-- The current state. -/
  state : σ
  /-- The still-unread input. -/
  input : List T
  /-- The stack, head first. -/
  stack : List Γ
deriving DecidableEq

/-- **One step of a pushdown automaton.** Write a configuration of a pushdown automaton
$M$ as $(q, w, s)$: state $q$, remaining input $w$, and stack $s$ listed from the top.
A configuration $(q, w, \gamma s)$ steps to $(q', w, u s)$ whenever $(q', u)$ is an
$\varepsilon$-transition of $M$ from $q$ with top symbol $\gamma$, and a configuration
$(q, a w, \gamma s)$ steps to $(q', w, u s)$ whenever $(q', u)$ is a transition of $M$
from $q$ on the input letter $a$ with top symbol $\gamma$. There are no other steps: a
step pops the top symbol, consumes at most one input letter, and pushes the list $u$
with its head as the new top. -/
inductive Step (M : PDA T σ Γ) : Config T σ Γ → Config T σ Γ → Prop
  | epsilon {q q' : σ} {w : List T} {γ : Γ} {s pushed : List Γ}
      (h : (q', pushed) ∈ M.step q none γ) :
      Step M ⟨q, w, γ :: s⟩ ⟨q', w, pushed ++ s⟩
  | consume {q q' : σ} {a : T} {w : List T} {γ : Γ} {s pushed : List Γ}
      (h : (q', pushed) ∈ M.step q (some a) γ) :
      Step M ⟨q, a :: w, γ :: s⟩ ⟨q', w, pushed ++ s⟩

/-- **Multi-step computation of a pushdown automaton.** For a pushdown automaton $M$, a
configuration $c$ derives a configuration $c'$ when $M$ can reach $c'$ from $c$ in zero or more
computation steps; that is, derivation is the reflexive transitive closure of the one-step
computation relation of $M$. -/
abbrev Derives (M : PDA T σ Γ) (c c' : Config T σ Γ) : Prop :=
  Relation.ReflTransGen (Step M) c c'

/-- **Computations extend by unread input and stack bottom.** Let $M$ be a pushdown automaton.
If $M$ can compute from a configuration with state $q$, remaining input $w$ and stack $s$ to a
configuration with state $q'$, remaining input $w'$ and stack $s'$, then for every word $v$ and
every list $t$ of stack symbols, $M$ can compute from the configuration with state $q$,
remaining input $wv$ and stack $st$ to the configuration with state $q'$, remaining input $w'v$
and stack $s't$. Here $st$ is the stack $s$ with $t$ placed below it. -/
theorem Derives.append_input_stack {c c' : Config T σ Γ} (h : Derives M c c')
    (v : List T) (t : List Γ) :
    Derives M ⟨c.state, c.input ++ v, c.stack ++ t⟩
      ⟨c'.state, c'.input ++ v, c'.stack ++ t⟩ := by
  induction h with
  | refl => rfl
  | tail _ last ih =>
    refine ih.tail ?_
    cases last with
    | epsilon hstep =>
      simpa [List.append_assoc] using Step.epsilon (M := M) hstep
    | consume hstep =>
      simpa [List.append_assoc] using Step.consume (M := M) hstep

/-- **Finitely supported pushdown automata.** A pushdown automaton $M$ is finitely supported when
there are finite sets $\sigma_0$ of states, $\Gamma_0$ of stack symbols and $T_0$ of input letters
such that the start state lies in $\sigma_0$, the initial stack symbol lies in $\Gamma_0$, every
transition from a state in $\sigma_0$ that pops a symbol in $\Gamma_0$ (on any input letter or on
$\varepsilon$) moves to a state in $\sigma_0$ and pushes only symbols in $\Gamma_0$, and there is
no transition from a state in $\sigma_0$ popping a symbol in $\Gamma_0$ that consumes an input
letter outside $T_0$.

This is the finiteness condition of a standard pushdown automaton; computations from the initial
configuration then only ever visit finitely many states, push finitely many stack symbols, and
respond to finitely many input letters. -/
def FinitelySupported (M : PDA T σ Γ) : Prop :=
  ∃ (σ₀ : Finset σ) (Γ₀ : Finset Γ) (T₀ : Finset T),
    M.start ∈ σ₀ ∧ M.startStack ∈ Γ₀ ∧
    (∀ q ∈ σ₀, ∀ (opt : Option T) {γ : Γ}, γ ∈ Γ₀ →
      ∀ y ∈ M.step q opt γ, y.1 ∈ σ₀ ∧ ∀ γ' ∈ y.2, γ' ∈ Γ₀) ∧
    ∀ q ∈ σ₀, ∀ {a : T}, a ∉ T₀ → ∀ {γ : Γ}, γ ∈ Γ₀ →
      M.step q (some a) γ = ∅

/-- **Initial configuration of a pushdown automaton.** The initial configuration of a pushdown
automaton $M$ on an input word $w$ has the start state of $M$ as its state, all of $w$ as its
remaining input, and the stack consisting of the initial stack symbol of $M$ alone. -/
def initConfig (M : PDA T σ Γ) (w : List T) : Config T σ Γ :=
  ⟨M.start, w, [M.startStack]⟩

/-- **Language accepted by a pushdown automaton.** The language accepted by a pushdown
automaton $M$, by empty stack, consists of the words $w$ for which some computation of $M$
leads from the initial configuration on input $w$ to a configuration, in some state, with no
remaining input and an empty stack. -/
def accepts (M : PDA T σ Γ) : Language T :=
  { w : List T | ∃ q : σ, Derives M (initConfig M w) ⟨q, [], []⟩ }

theorem mem_accepts {w : List T} :
    w ∈ M.accepts ↔ ∃ q : σ, Derives M (initConfig M w) ⟨q, [], []⟩ :=
  Iff.rfl

/-- **Closed sets of stack symbols.** A finite set $\Gamma_0$ of stack symbols is closed for a
pushdown automaton $M$ when every transition of $M$ that pops a symbol in $\Gamma_0$, from any
state and on any input letter or on $\varepsilon$, pushes only symbols in $\Gamma_0$.
Computations starting with a stack inside a closed set keep their stack inside it. -/
def ClosedUnder (M : PDA T σ Γ) (Γ₀ : Finset Γ) : Prop :=
  ∀ (q : σ) (opt : Option T) {γ : Γ}, γ ∈ Γ₀ →
    ∀ y ∈ M.step q opt γ, ∀ γ' ∈ y.2, γ' ∈ Γ₀

/-- **Lifting a stack to a set of stack symbols.** Given a finite set $\Gamma_0$ of
stack symbols and a stack $s = \gamma_1 \cdots \gamma_n$ all of whose symbols lie in
$\Gamma_0$, the lifted stack is the same list $\gamma_1 \cdots \gamma_n$, in the same
order, regarded as a stack over the alphabet $\Gamma_0$. -/
def liftStack (Γ₀ : Finset Γ) : (s : List Γ) → (∀ γ ∈ s, γ ∈ Γ₀) →
    List {γ // γ ∈ Γ₀}
  | [], _ => []
  | γ :: s, h =>
    ⟨γ, h γ (List.mem_cons.mpr (Or.inl rfl))⟩ ::
      liftStack Γ₀ s (fun γ' hγ' => h γ' (List.mem_cons_of_mem γ hγ'))

theorem liftStack_cons {Γ₀ : Finset Γ} {γ : Γ} {s : List Γ}
    (h : ∀ γ' ∈ γ :: s, γ' ∈ Γ₀) :
    liftStack Γ₀ (γ :: s) h =
      ⟨γ, h γ (List.mem_cons.mpr (Or.inl rfl))⟩ ::
        liftStack Γ₀ s (fun γ' hγ' => h γ' (List.mem_cons_of_mem γ hγ')) := by
  rw [liftStack]

theorem map_val_liftStack {Γ₀ : Finset Γ} :
    ∀ (s : List Γ) (h : ∀ γ ∈ s, γ ∈ Γ₀),
      (liftStack Γ₀ s h).map Subtype.val = s
  | [], _ => rfl
  | γ :: s, h => by
    rw [liftStack_cons, List.map_cons, map_val_liftStack s]

theorem liftStack_append {Γ₀ : Finset Γ} (s t : List Γ)
    (h : ∀ γ ∈ s ++ t, γ ∈ Γ₀) :
    liftStack Γ₀ (s ++ t) h =
      liftStack Γ₀ s (fun γ hγ => h γ (List.mem_append_left t hγ)) ++
        liftStack Γ₀ t (fun γ hγ => h γ (List.mem_append_right s hγ)) :=
  (List.map_injective_iff.mpr Subtype.val_injective) (by
    rw [map_val_liftStack, List.map_append, map_val_liftStack,
      map_val_liftStack])

attribute [local instance] Classical.propDecidable

/-- **Restricting the stack alphabet of a pushdown automaton.** Let $M$ be a pushdown
automaton with stack alphabet $\Gamma$, and let $\Gamma_0 \subseteq \Gamma$ be a finite set
of stack symbols that contains the initial stack symbol of $M$ and is closed for $M$.
The restriction of $M$ to $\Gamma_0$ is the pushdown automaton with the same input
alphabet, states and start state as $M$, stack alphabet $\Gamma_0$, and the initial stack
symbol of $M$ as its initial stack symbol. Its transitions from a state $q$ on an input
option $o$ with top symbol $\gamma \in \Gamma_0$ are the transitions $(q', u)$ of $M$ from
$q$ on $o$ with top symbol $\gamma$, with the pushed list $u$ read as a list over
$\Gamma_0$; closedness guarantees that every symbol of $u$ lies in $\Gamma_0$.

The restricted automaton has a finite stack alphabet and accepts the same language as
$M$. -/
noncomputable def restrict (M : PDA T σ Γ) (Γ₀ : Finset Γ)
    (hstart : M.startStack ∈ Γ₀) (hclosed : M.ClosedUnder Γ₀) :
    PDA T σ {γ // γ ∈ Γ₀} where
  step q opt γ :=
    (M.step q opt γ.1).attach.image fun y =>
      (y.1.1, liftStack Γ₀ y.1.2 (fun γ' hγ' => hclosed q opt γ.2 y.1 y.2 γ' hγ'))
  start := M.start
  startStack := ⟨M.startStack, hstart⟩

theorem restrict_step {Γ₀ : Finset Γ} {hstart : M.startStack ∈ Γ₀}
    {hclosed : M.ClosedUnder Γ₀} {q : σ} {opt : Option T} {γ : {γ // γ ∈ Γ₀}} :
    (M.restrict Γ₀ hstart hclosed).step q opt γ =
      (M.step q opt γ.1).attach.image fun y =>
        (y.1.1, liftStack Γ₀ y.1.2 (fun γ' hγ' => hclosed q opt γ.2 y.1 y.2 γ' hγ')) :=
  rfl

/-- **Transitions of the restricted pushdown automaton.** Let $M$ be a pushdown
automaton with stack alphabet $\Gamma$, and let $M|_{\Gamma_0}$ be its restriction to a
finite set $\Gamma_0 \subseteq \Gamma$ of stack symbols that contains the initial stack
symbol and is closed for $M$. Let $q, q'$ be states, $o$ an input option (an input
letter, or none for an $\varepsilon$-transition), $\gamma \in \Gamma_0$ and $s$ a list of
symbols of $\Gamma_0$. Then $(q', s)$ is a transition of $M|_{\Gamma_0}$ from $q$ on $o$
with top symbol $\gamma$ if and only if $(q', s)$, with $s$ read as a list of symbols
of $\Gamma$, is a transition of $M$ from $q$ on $o$ with top symbol $\gamma$. -/
theorem mem_restrict_step {Γ₀ : Finset Γ} {hstart : M.startStack ∈ Γ₀}
    {hclosed : M.ClosedUnder Γ₀} {q q' : σ} {opt : Option T}
    {γ : {γ // γ ∈ Γ₀}} {s : List {γ // γ ∈ Γ₀}} :
    (q', s) ∈ (M.restrict Γ₀ hstart hclosed).step q opt γ ↔
      ∃ pushed : List Γ, (q', pushed) ∈ M.step q opt γ.1 ∧
        s.map Subtype.val = pushed := by
  rw [restrict_step]
  constructor
  · intro h
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h
    obtain ⟨h1, h2⟩ := (Prod.mk.injEq ..).mp hy
    exact ⟨y.1.2, h1 ▸ y.2, by rw [← h2, map_val_liftStack]⟩
  · rintro ⟨pushed, hmem, hs⟩
    refine Finset.mem_image.mpr ⟨⟨(q', pushed), hmem⟩, Finset.mem_attach _ _, ?_⟩
    congr 1
    exact (List.map_injective_iff.mpr Subtype.val_injective)
      (by rw [map_val_liftStack, hs])

/-- **Computations of the restriction are computations of the automaton.** Let $M$ be a pushdown
automaton and let $\Gamma_0$ be a finite set of stack symbols that contains the initial stack
symbol of $M$ and is closed for $M$. If the restriction of $M$ to $\Gamma_0$ can compute from a
configuration with state $q$, remaining input $w$ and stack $s$ to a configuration with state
$q'$, remaining input $w'$ and stack $s'$, then $M$ can compute from the configuration
$(q, w, s)$ to the configuration $(q', w', s')$, where the stacks $s$ and $s'$ over $\Gamma_0$ are
read as stacks over the full stack alphabet of $M$. -/
theorem derives_val_of_derives_restrict {Γ₀ : Finset Γ}
    {hstart : M.startStack ∈ Γ₀} {hclosed : M.ClosedUnder Γ₀}
    {c c' : Config T σ {γ // γ ∈ Γ₀}}
    (h : (M.restrict Γ₀ hstart hclosed).Derives c c') :
    M.Derives ⟨c.state, c.input, c.stack.map Subtype.val⟩
      ⟨c'.state, c'.input, c'.stack.map Subtype.val⟩ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    refine ih.tail ?_
    cases hstep with
    | epsilon hmem =>
      obtain ⟨pushed, hmem', hs⟩ := mem_restrict_step.mp hmem
      simpa [hs] using Step.epsilon (M := M) hmem'
    | consume hmem =>
      obtain ⟨pushed, hmem', hs⟩ := mem_restrict_step.mp hmem
      simpa [hs] using Step.consume (M := M) hmem'

/-- **Computations stay inside a closed set of stack symbols.** Let $M$ be a pushdown
automaton and $\Gamma_0$ a finite set of stack symbols that is closed for $M$. If a
configuration $c$ derives a configuration $c'$ in zero or more steps of $M$, and every
symbol on the stack of $c$ lies in $\Gamma_0$, then every symbol on the stack of $c'$ lies
in $\Gamma_0$. -/
theorem stack_subset_of_derives {Γ₀ : Finset Γ} (hclosed : M.ClosedUnder Γ₀)
    {c c' : Config T σ Γ} (h : M.Derives c c') (hc : ∀ γ ∈ c.stack, γ ∈ Γ₀) :
    ∀ γ ∈ c'.stack, γ ∈ Γ₀ := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih =>
    intro γ' hγ'
    cases hstep with
    | epsilon hmem =>
      cases List.mem_append.mp hγ' with
      | inl hγ' => exact hclosed _ _ (ih _ (List.mem_cons_self ..)) _ hmem _ hγ'
      | inr hγ' => exact ih _ (List.mem_cons_of_mem _ hγ')
    | consume hmem =>
      cases List.mem_append.mp hγ' with
      | inl hγ' => exact hclosed _ _ (ih _ (List.mem_cons_self ..)) _ hmem _ hγ'
      | inr hγ' => exact ih _ (List.mem_cons_of_mem _ hγ')

/-- **Computations inside a closed set lift to the restriction.** Let $M$ be a pushdown automaton
and let $\Gamma_0$ be a finite set of stack symbols that contains the initial stack symbol of $M$
and is closed for $M$. Suppose $M$ can compute from a configuration with state $q$, remaining
input $w$ and stack $s$ to a configuration with state $q'$, remaining input $w'$ and stack $s'$,
and every symbol of $s$ lies in $\Gamma_0$. Then the symbols of $s'$ also lie in $\Gamma_0$, and
the restriction of $M$ to $\Gamma_0$ can compute from the configuration $(q, w, s)$ to the
configuration $(q', w', s')$, with $s$ and $s'$ read as stacks over $\Gamma_0$. -/
theorem derives_restrict_of_derives {Γ₀ : Finset Γ}
    {hstart : M.startStack ∈ Γ₀} {hclosed : M.ClosedUnder Γ₀}
    {c c' : Config T σ Γ} (h : M.Derives c c') (hc : ∀ γ ∈ c.stack, γ ∈ Γ₀) :
    (M.restrict Γ₀ hstart hclosed).Derives
      ⟨c.state, c.input, liftStack Γ₀ c.stack hc⟩
      ⟨c'.state, c'.input,
        liftStack Γ₀ c'.stack (stack_subset_of_derives hclosed h hc)⟩ := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    refine ih.tail ?_
    cases hstep with
    | epsilon hmem =>
      rw [liftStack_cons, liftStack_append]
      exact Step.epsilon (mem_restrict_step.mpr ⟨_, hmem, map_val_liftStack _ _⟩)
    | consume hmem =>
      rw [liftStack_cons, liftStack_append]
      exact Step.consume (mem_restrict_step.mpr ⟨_, hmem, map_val_liftStack _ _⟩)

/-- **Restricting the stack alphabet preserves the accepted language.** Let $M$ be a pushdown
automaton and let $\Gamma_0$ be a finite set of stack symbols of $M$ that contains the initial
stack symbol of $M$ and is closed for $M$. Then the restriction of $M$ to the stack alphabet
$\Gamma_0$ accepts, by empty stack, exactly the same language as $M$. -/
theorem accepts_restrict {Γ₀ : Finset Γ} {hstart : M.startStack ∈ Γ₀}
    {hclosed : M.ClosedUnder Γ₀} :
    (M.restrict Γ₀ hstart hclosed).accepts = M.accepts := by
  ext w
  constructor
  · rintro ⟨q, h⟩
    exact ⟨q, derives_val_of_derives_restrict h⟩
  · rintro ⟨q, h⟩
    refine ⟨q, ?_⟩
    have h' := derives_restrict_of_derives (hstart := hstart)
      (hclosed := hclosed) h
      (c := initConfig M w) (fun γ hγ => by
        have : γ = M.startStack := List.mem_singleton.mp hγ
        rwa [this])
    simpa [initConfig, restrict, liftStack] using h'

end PDA

end Cslib.Automata
