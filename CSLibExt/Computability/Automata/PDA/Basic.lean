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

/-- A pushdown automaton over input alphabet `T`, with states in `σ` and
stack alphabet `Γ`. From state `q`, on optional input (`none` is an
`ε`-transition) and popped stack symbol `γ`, a transition chooses finitely
many pairs of a next state and a list of symbols to push.

This is the generalized model: the state and stack types themselves are
unrestricted, and only each transition is finitely branching. A standard
(textbook) pushdown automaton additionally has finite support in the sense
of `PDA.FinitelySupported`; without it, `PDA.accepts` can be an arbitrary
language, so the reverse PDA-to-CFG direction needs finiteness hypotheses. -/
structure PDA (T : Type*) (σ : Type*) (Γ : Type*) where
  /-- The finitely branching transition function. -/
  step : σ → Option T → Γ → Finset (σ × List Γ)
  /-- The initial state. -/
  start : σ
  /-- The sole initial stack symbol. -/
  startStack : Γ

namespace PDA

variable {T : Type*} {σ : Type*} {Γ : Type*} {M : PDA T σ Γ}

/-- A configuration: current state, remaining input, and stack contents
with the head as the top. -/
structure Config (T : Type*) (σ : Type*) (Γ : Type*) where
  /-- The current state. -/
  state : σ
  /-- The still-unread input. -/
  input : List T
  /-- The stack, head first. -/
  stack : List Γ
deriving DecidableEq

/-- One computation step: pop the top stack symbol, optionally consume one
input letter, move to the chosen state, and push the chosen list. -/
inductive Step (M : PDA T σ Γ) : Config T σ Γ → Config T σ Γ → Prop
  | epsilon {q q' : σ} {w : List T} {γ : Γ} {s pushed : List Γ}
      (h : (q', pushed) ∈ M.step q none γ) :
      Step M ⟨q, w, γ :: s⟩ ⟨q', w, pushed ++ s⟩
  | consume {q q' : σ} {a : T} {w : List T} {γ : Γ} {s pushed : List Γ}
      (h : (q', pushed) ∈ M.step q (some a) γ) :
      Step M ⟨q, a :: w, γ :: s⟩ ⟨q', w, pushed ++ s⟩

/-- Many-step computation, the reflexive transitive closure of `Step`. -/
abbrev Derives (M : PDA T σ Γ) (c c' : Config T σ Γ) : Prop :=
  Relation.ReflTransGen (Step M) c c'

/-- Adding unread input at the end and extra symbols at the bottom of the
stack does not affect a computation. -/
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

/-- Finite support: some finite sets of states, stack symbols, and input
labels such that the start state and the initial stack symbol are
supported, transitions between supported states and stack symbols stay
within the support, and no transition from a supported configuration
consumes an unsupported input label. This is the finiteness condition of
a standard pushdown automaton; computations from the initial
configuration then only ever visit finitely many states, push finitely
many stack symbols, and respond to finitely many input letters. -/
def FinitelySupported (M : PDA T σ Γ) : Prop :=
  ∃ (σ₀ : Finset σ) (Γ₀ : Finset Γ) (T₀ : Finset T),
    M.start ∈ σ₀ ∧ M.startStack ∈ Γ₀ ∧
    (∀ q ∈ σ₀, ∀ (opt : Option T) {γ : Γ}, γ ∈ Γ₀ →
      ∀ y ∈ M.step q opt γ, y.1 ∈ σ₀ ∧ ∀ γ' ∈ y.2, γ' ∈ Γ₀) ∧
    ∀ q ∈ σ₀, ∀ {a : T}, a ∉ T₀ → ∀ {γ : Γ}, γ ∈ Γ₀ →
      M.step q (some a) γ = ∅

/-- The initial configuration for input `w`. -/
def initConfig (M : PDA T σ Γ) (w : List T) : Config T σ Γ :=
  ⟨M.start, w, [M.startStack]⟩

/-- The language accepted by empty stack: some computation from the initial
configuration consumes the whole input and empties the stack. -/
def accepts (M : PDA T σ Γ) : Language T :=
  { w : List T | ∃ q : σ, Derives M (initConfig M w) ⟨q, [], []⟩ }

theorem mem_accepts {w : List T} :
    w ∈ M.accepts ↔ ∃ q : σ, Derives M (initConfig M w) ⟨q, [], []⟩ :=
  Iff.rfl

/-- A set of stack symbols is closed for `M` when pushing from a symbol in
the set only ever pushes symbols in the set. Computations starting inside
a closed set stay inside it. -/
def ClosedUnder (M : PDA T σ Γ) (Γ₀ : Finset Γ) : Prop :=
  ∀ (q : σ) (opt : Option T) {γ : Γ}, γ ∈ Γ₀ →
    ∀ y ∈ M.step q opt γ, ∀ γ' ∈ y.2, γ' ∈ Γ₀

/-- Lift a stack whose symbols all lie in `Γ₀` to a stack over the
subtype. -/
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

/-- Restrict the stack alphabet to a finite closed set `Γ₀` containing the
initial stack symbol. The restricted PDA is over the subtype, hence has a
`Fintype` stack alphabet, and accepts the same language
(`PDA.accepts_restrict`). -/
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

/-- A transition of the restricted PDA is a transition of `M` whose pushed
stack lifts. -/
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

/-- Computations of the restricted PDA map to computations of `M`. -/
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

/-- Stacks of computations starting in a closed set stay in it. -/
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

/-- Computations of `M` starting in a closed set lift to the restricted
PDA. -/
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

/-- Restricting the stack alphabet to a finite closed set does not change
the accepted language. -/
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
