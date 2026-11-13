/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Comp.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Comp.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`MetaMathlibExt` namespaces, Mathlib-pin proof repairs, removal of the source repository's
`Millennium` hypothesis wrapper, the `IsPolyTime` corollaries at the end of this file, and
`iter_none` taken from `MetaMathlibExt.TM2Program`.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.TuringMachine.Program

/-!
# Composition of polynomial-time two-stack Turing machines

`TM2ComputableInPolyTime` is closed under composition: from machines computing `f : α → β`
and `g : β → γ` in polynomial time we build one machine computing `g ∘ f` in polynomial time.
Mathlib PR #44441 (`TM2ComputableInPolyTime.comp`, stacked on #44440) proves the same result
upstream; once it reaches the pinned Mathlib, prefer it and retire this file.

The composite machine has stacks `K₁ ⊕ K₂ ⊕ Unit`. It runs `M₁`, pops `M₁`'s output onto a
scratch stack and from there onto `M₂`'s input stack (the two reversals cancel), then runs `M₂`.
Each copy loop takes `2m + 1` steps for an intermediate string of length `m`, and
`m ≤ n + c · p₁(n)` where `c` bounds the pushes per step of `M₁` (`pushBound`), so the
composite runs within `p₁ + 4 (X + c p₁) + 2 + p₂ ∘ (X + c p₁)` steps (`compTime`).

## Main declarations

* `MetaMathlibExt.TM2Composition.compComputable`: the composite machine with its time bound.
* `MetaMathlibExt.tm2ComputableInPolyTime_comp`: closure under composition, as `Nonempty`.
* `MetaMathlibExt.ComplexityTheory.IsPolyTime.comp`: closure of `IsPolyTime` under composition.
* `MetaMathlibExt.ComplexityTheory.comp_mem_P`: `P` is closed under polynomial-time preimages.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Composition

open Turing StateTransition Function

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (M₁ M₂ : FinTM2)

/-- **Stack indices of the composite machine.** For finite multi-stack Turing machines $M_1$ and
$M_2$ with stack index sets $K_1$ and $K_2$, the stacks of their composite machine are indexed by
the disjoint union $K_1 \sqcup K_2 \sqcup \{\ast\}$: the stacks of $M_1$, the stacks of $M_2$, and
one scratch stack $\ast$. -/
abbrev CK := M₁.K ⊕ M₂.K ⊕ Unit

/-- **Intermediate alphabet of the composite machine.** For a multi-stack Turing machine (a TM2
machine) $M_2$ with input stack $k_0$, this is the alphabet of the symbols on stack $k_0$ of $M_2$.

When a machine $M_1$ is composed with $M_2$, the composite machine uses this alphabet for its
scratch stack and for the symbol held in its control state. -/
abbrev X := M₂.Γ M₂.k₀

/-- **Stack alphabets of the composite machine.** Let $M_1$ and $M_2$ be finite multi-stack Turing
machines and let $X$ be the alphabet of the input stack of $M_2$. The stacks of their composite
machine are the stacks of $M_1$, the stacks of $M_2$ and one scratch stack. Each stack of $M_1$
keeps its alphabet from $M_1$, each stack of $M_2$ keeps its alphabet from $M_2$, and the scratch
stack has alphabet $X$. -/
@[reducible] def CΓ : CK M₁ M₂ → Type
  | .inl k => M₁.Γ k
  | .inr (.inl k) => M₂.Γ k
  | .inr (.inr _) => X M₂

/-- **Labels of the composite machine.** Let $M_1$ and $M_2$ be finite multi-stack Turing
machines with label sets $\Lambda_1$ and $\Lambda_2$, and let $X$ be the alphabet of the input
stack of $M_2$. The label set of their composite machine is the disjoint union of $\Lambda_1$,
$\Lambda_2$ and two copies of $X \sqcup \{\bot\}$, one for each copy loop: in each copy, $\bot$
labels the step that pops and $x \in X$ labels the step that pushes $x$. -/
abbrev CΛ := M₁.Λ ⊕ M₂.Λ ⊕ (Option (X M₂) ⊕ Option (X M₂))

/-- **States of the composite machine.** Let $M_1$ and $M_2$ be finite multi-stack Turing machines
with internal state sets $\sigma_1$ and $\sigma_2$, and let $X$ be the alphabet of the input stack
of $M_2$. The internal states of their composite machine are the triples in
$\sigma_1 \times \sigma_2 \times (X \sqcup \{\bot\})$: a state of $M_1$, a state of $M_2$, and
either the symbol just popped by a copy loop or $\bot$ when there is none. -/
abbrev Cσ := M₁.σ × M₂.σ × Option (X M₂)

/-- **Pop label of the first copy loop.** In the composite machine of $M_1$ and $M_2$, this is
the label $\mathrm{none}$ in the first copy-loop part of the label set; the composite program
uses it to pop a symbol from $M_1$'s output stack. -/
abbrev pop1 : CΛ M₁ M₂ := .inr (.inr (.inl none))
/-- **Push labels of the first copy loop.** In the composite machine of $M_1$ and $M_2$, for a
symbol $x$ of $M_2$'s input alphabet, this is the label $\mathrm{some}\ x$ in the first copy-loop
part of the label set; the composite program uses it to push $x$ on the scratch stack. -/
abbrev push1 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inl (some x)))
/-- **Pop label of the second copy loop.** In the composite machine of $M_1$ and $M_2$, this is
the label $\mathrm{none}$ in the second copy-loop part of the label set; the composite program
uses it to pop a symbol from the scratch stack. -/
abbrev pop2 : CΛ M₁ M₂ := .inr (.inr (.inr none))
/-- **Push labels of the second copy loop.** In the composite machine of $M_1$ and $M_2$, for a
symbol $x$ of $M_2$'s input alphabet, this is the label $\mathrm{some}\ x$ in the second
copy-loop part of the label set; the composite program uses it to push $x$ on $M_2$'s input
stack. -/
abbrev push2 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inr (some x)))

/-- **Scratch stack of the composite machine.** For multi-stack Turing machines (TM2 machines)
$M_1$ and $M_2$ with stack index types $K_1$ and $K_2$, the composite machine has stack indices
$K_1 \oplus K_2 \oplus \mathrm{Unit}$; its scratch stack is the index given by the unique element
of the $\mathrm{Unit}$ summand. -/
abbrev tmp : CK M₁ M₂ := .inr (.inr ())

/-- **Lifting a statement of the first machine.** Given finite multi-stack Turing machines
$M_1$ and $M_2$, a statement of $M_1$ is translated into a statement of their composite
machine, whose state is a triple $(v_1, v_2, o)$, by recursion on the statement: an operation
on a stack $k$ of $M_1$ acts on the copy of $k$ among the composite stacks, every read or update
of $M_1$'s state reads or updates the component $v_1$ and leaves $v_2$ and $o$ unchanged, a
branch tests $v_1$, a jump to a label $l$ of $M_1$ becomes a jump to the copy of $l$, and
halting becomes a jump to the pop label of the first copy loop, which moves $M_1$'s output. -/
def lift₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inl k) (fun s => f s.1) (lift₁ q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .load a q => .load (fun s => (a s.1, s.2)) (lift₁ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (lift₁ q₁) (lift₁ q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => pop1 M₁ M₂)

/-- **Lifting a statement of the second machine.** Given finite multi-stack Turing machines
$M_1$ and $M_2$, a statement of $M_2$ is translated into a statement of their composite
machine, whose state is a triple $(v_1, v_2, o)$, by recursion on the statement: an operation
on a stack $k$ of $M_2$ acts on the copy of $k$ among the composite stacks, every read or update
of $M_2$'s state reads or updates the component $v_2$ and leaves $v_1$ and $o$ unchanged, a
branch tests $v_2$, a jump to a label $l$ of $M_2$ becomes a jump to the copy of $l$, and
halting stays halting. -/
def lift₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inr (.inl k)) (fun s => f s.2.1) (lift₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (lift₂ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (lift₂ q₁) (lift₂ q₂)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (φ : M₁.Γ M₁.k₁ → X M₂)

/-- **The program of the composite machine.** Let $M_1$ and $M_2$ be finite multi-stack Turing
machines and $\varphi$ a map from $M_1$'s output alphabet to $M_2$'s input alphabet. At a label
of $M_1$ or of $M_2$ the composite program runs the lifted statement of that machine at that
label. At the pop label of the first copy loop it pops $M_1$'s output stack, stores the image
under $\varphi$ of the popped symbol (or nothing) in the third state component, and jumps to the
push label of the first loop for that image, or to the pop label of the second loop if the
stack was empty. At the push label of the first loop for $x$ it pushes $x$ on the scratch stack
and jumps to the first pop label. At the pop label of the second loop it pops the scratch
stack, stores the popped symbol (or nothing) in the third state component, and jumps to the
push label of the second loop for that symbol, or to the copy of $M_2$'s main label if the
scratch stack was empty. At the push label of the second loop for $x$ it pushes $x$ on $M_2$'s
input stack and jumps to the second pop label. -/
def prog : CΛ M₁ M₂ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .inl l => lift₁ M₁ M₂ (M₁.m l)
  | .inr (.inl l) => lift₂ M₁ M₂ (M₂.m l)
  | .inr (.inr (.inl none)) =>
      .pop (.inl M₁.k₁) (fun s o => (s.1, s.2.1, o.map φ))
        (.goto fun s => match s.2.2 with
          | some x => push1 M₁ M₂ x
          | none => pop2 M₁ M₂)
  | .inr (.inr (.inl (some x))) =>
      .push (tmp M₁ M₂) (fun _ => x) (.goto fun _ => pop1 M₁ M₂)
  | .inr (.inr (.inr none)) =>
      .pop (tmp M₁ M₂) (fun s o => (s.1, s.2.1, o))
        (.goto fun s => match s.2.2 with
          | some x => push2 M₁ M₂ x
          | none => .inr (.inl M₂.main))
  | .inr (.inr (.inr (some x))) =>
      .push (.inr (.inl M₂.k₀)) (fun _ => x) (.goto fun _ => pop2 M₁ M₂)

/-- **The composite machine.** Let $M_1$ and $M_2$ be finite multi-stack Turing machines, let $X$ be
the alphabet of the input stack of $M_2$, and let $\varphi$ map the output alphabet of $M_1$ to $X$.
The composite machine has the stacks of $M_1$, the stacks of $M_2$ and one scratch stack with
alphabet $X$; its input stack is that of $M_1$ and its output stack is that of $M_2$. It starts
at the main label of $M_1$, in the state made of the initial states of $M_1$ and $M_2$ and no held
symbol. It runs $M_1$; when $M_1$ halts, it pops the output stack of $M_1$ onto the scratch stack,
translating each symbol by $\varphi$, then pops the scratch stack onto the input stack of $M_2$,
then runs $M_2$ from its main label, and it halts when $M_2$ halts. -/
noncomputable def compTM : FinTM2 where
  K := CK M₁ M₂
  k₀ := .inl M₁.k₀
  k₁ := .inr (.inl M₂.k₁)
  Γ := CΓ M₁ M₂
  Λ := CΛ M₁ M₂
  main := .inl M₁.main
  σ := Cσ M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  m := prog M₁ M₂ φ

/-! ### Stacks of the composite machine -/

/-- **Assembling the stacks of the composite machine.** Given finite multi-stack Turing machines
$M_1$ and $M_2$, contents $S_1$ for the stacks of $M_1$, contents $S_2$ for the stacks of $M_2$,
and a list $t$ of symbols of $M_2$'s input alphabet, the stack contents of their composite
machine put $S_1(k)$ on the copy of each stack $k$ of $M_1$, $S_2(k)$ on the copy of each stack
$k$ of $M_2$, and $t$ on the scratch stack. -/
def mkStk (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    ∀ k : CK M₁ M₂, List (CΓ M₁ M₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => t

variable {M₁ M₂}

theorem update_mkStk_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₁.K) (x : List (M₁.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inl k) x = mkStk M₁ M₂ (update S₁ k x) S₂ t := by
  funext k'
  rcases k' with k' | k' | u
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_inr (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₂.K) (x : List (M₂.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inr (.inl k)) x = mkStk M₁ M₂ S₁ (update S₂ k x) t := by
  funext k'
  rcases k' with k' | k' | u
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_tmp (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (x : List (X M₂)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (tmp M₁ M₂) x = mkStk M₁ M₂ S₁ S₂ x := by
  funext k'
  rcases k' with k' | k' | ⟨⟩
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl
  · simp [mkStk]

/-! ### Simulating one statement of `M₁` or `M₂` -/

/-- **Composite label of an $M_1$ label.** A label $l$ of $M_1$ is sent to $l$ viewed as a label of
the $M_1$ part of the composite of $M_1$ and $M_2$, and the halted label is sent to the label that
pops $M_1$'s output stack, which starts the first copy loop. -/
def lab₁ : Option M₁.Λ → CΛ M₁ M₂
  | some l => .inl l
  | none => pop1 M₁ M₂

theorem stepAux_lift₁ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k))
    (v₂ : M₂.σ) (o : Option (X M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₁ M₁ M₂ q) (v, v₂, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨some (lab₁ (TM2.stepAux q v S₁).l), ((TM2.stepAux q v S₁).var, v₂, o),
        mkStk M₁ M₂ (TM2.stepAux q v S₁).stk S₂ t⟩ := by
  induction q generalizing v S₁ with
  | push k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | peek k f q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | load a q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₁, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₁, TM2.stepAux, lab₁]
  | halt => simp [lift₁, TM2.stepAux, lab₁]

theorem stepAux_lift₂ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k))
    (v₁ : M₁.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₂ M₁ M₂ q) (v₁, v, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨(TM2.stepAux q v S₂).l.map (fun l => .inr (.inl l)), (v₁, (TM2.stepAux q v S₂).var, o),
        mkStk M₁ M₂ S₁ (TM2.stepAux q v S₂).stk t⟩ := by
  induction q generalizing v S₂ with
  | push k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | peek k f q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | load a q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₂, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₂, TM2.stepAux]
  | halt => simp [lift₂, TM2.stepAux]

/-! ### Phase embeddings and one-step simulation -/

/-- **Embedding of $M_1$'s configurations into the composite machine.** A configuration $c$ of $M_1$
is sent to the configuration of the composite of $M_1$ and $M_2$ whose label is the label of $c$
viewed as a label of the $M_1$ part, or the label that pops $M_1$'s output stack (the start of the
first copy loop) if $c$ is halted, whose state is $(v, q_2, \mathrm{none})$ with $v$ the state of
$c$ and $q_2$ the initial state of $M_2$, and whose stacks are the stacks of $c$ on $M_1$'s stacks,
with $M_2$'s stacks and the scratch stack empty. -/
def emb₁ (c : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂) :=
  ⟨some (lab₁ c.l), (c.var, M₂.initialState, none), mkStk M₁ M₂ c.stk (fun _ => []) []⟩

/-- **Embedding of $M_2$'s configurations into the composite machine.** A configuration $c$ of $M_2$
is sent to the configuration of the composite of $M_1$ and $M_2$ whose label is the label of $c$
viewed as a label of the $M_2$ part (halted if $c$ is halted), whose state is
$(q_1, v, \mathrm{none})$ with $q_1$ the initial state of $M_1$ and $v$ the state of $c$, and whose
stacks are the stacks of $c$ on $M_2$'s stacks, with $M_1$'s stacks and the scratch stack
empty. -/
def emb₂ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂) :=
  ⟨c.l.map (fun l => .inr (.inl l)), (M₁.initialState, c.var, none),
    mkStk M₁ M₂ (fun _ => []) c.stk []⟩

theorem step_emb₁ {c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ} (h : TM2.step M₁.m c = some c') :
    TM2.step (prog M₁ M₂ φ) (emb₁ c) = some (emb₁ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb₁, lab₁, TM2.step, prog]
    rw [stepAux_lift₁]
    rfl

theorem step_emb₂ {c c' : TM2.Cfg M₂.Γ M₂.Λ M₂.σ} (h : TM2.step M₂.m c = some c') :
    TM2.step (prog M₁ M₂ φ) (emb₂ c) = some (emb₂ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb₂, Option.map_some, TM2.step, prog]
    rw [stepAux_lift₂]

theorem iter_step {σ : Type} {f : σ → Option σ} {c c' : σ} (h : f c = some c') (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some c') := by
  rw [iterate_succ_apply]
  change (flip bind f)^[n] (f c) = _
  rw [h]

/-- **Simulation transports runs.** Let $f : \alpha \to \mathrm{Option}\,\alpha$ and
$g : \beta \to \mathrm{Option}\,\beta$ be partial step functions (a value $\mathrm{none}$ means
halting) and $e : \alpha \to \beta$ a map such that $f(c) = c'$ implies $g(e(c)) = e(c')$ for all
$c, c'$. Then for every $n$ and all $c, d \in \alpha$, if $n$ steps of $f$ starting from $c$ end
at $d$, then $n$ steps of $g$ starting from $e(c)$ end at $e(d)$.

Halted configurations are absorbing, so every intermediate configuration of such a run is live. -/
theorem iter_sim {α β : Type} {f : α → Option α} {g : β → Option β} (e : α → β)
    (H : ∀ c c', f c = some c' → g (e c) = some (e c')) :
    ∀ (n : ℕ) (c d : α), (flip bind f)^[n] (some c) = some d →
      (flip bind g)^[n] (some (e c)) = some (e d) := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h ⊢
      rw [h]
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind f)^[n] (f c) = some d at h
      cases hc : f c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          rw [iter_step (H c c' hc)]
          exact ih c' d h

/-! ### The copy loops -/

section copy

variable (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k))
  (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))

theorem step_pop1_cons (y : M₁.Γ M₁.k₁) (ys : List (M₁.Γ M₁.k₁)) (hy : S₁ M₁.k₁ = y :: ys) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (push1 M₁ M₂ (φ y)), (v₁, v₂, some (φ y)),
        mkStk M₁ M₂ (update S₁ M₁.k₁ ys) S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, hy, update_mkStk_inl]

theorem step_pop1_nil (hy : S₁ M₁.k₁ = []) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none), mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, hy, update_mkStk_inl]

theorem step_push1 (x : X M₂) (s : Cσ M₁ M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (push1 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop1 M₁ M₂), s, mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_pop2_cons (x : X M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ =
      some ⟨some (push2 M₁ M₂ x), (v₁, v₂, some x), mkStk M₁ M₂ S₁ S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_pop2_nil :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ []⟩ =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none), mkStk M₁ M₂ S₁ S₂ []⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_push2 (x : X M₂) (s : Cσ M₁ M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (push2 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), s, mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (x :: S₂ M₂.k₀)) t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_inr]

end copy

/-- **First copy loop of the composite machine.** Consider the composite program of machines $M_1$
and $M_2$ with symbol translation $\varphi$. Suppose it is at the label that pops $M_1$'s output
stack, with state $(v_1, v_2, o)$, with $M_1$'s stacks holding $S_1$, $M_2$'s stacks holding $S_2$,
the scratch stack holding $t$, and $M_1$'s output stack holding the list $y$. Then after exactly
$2|y| + 1$ steps it is at the label that pops the scratch stack, with state
$(v_1, v_2, \mathrm{none})$, $M_1$'s output stack empty and its other stacks unchanged, $M_2$'s
stacks still $S_2$, and the scratch stack holding the reverse of the list obtained by applying
$\varphi$ to each symbol of $y$, followed by $t$. -/
theorem copy₁ (ys : List (M₁.Γ M₁.k₁)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (hy : S₁ M₁.k₁ = ys) :
    (flip bind (TM2.step (prog M₁ M₂ φ)))^[2 * ys.length + 1]
        (some ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none),
        mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ ((ys.map φ).reverse ++ t)⟩ := by
  induction ys generalizing o S₁ t with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop1_nil φ v₁ v₂ o S₁ S₂ t hy)]
      simp
  | cons y ys ih =>
      rw [show 2 * (y :: ys).length + 1 = (2 * ys.length + 1) + 1 + 1 by
          simp only [List.length_cons]; omega,
        iter_step (step_pop1_cons φ v₁ v₂ o S₁ S₂ t y ys hy), iter_step (step_push1 φ _ _ _ _ _),
        ih _ _ _ (update_self _ _ _)]
      simp [update_idem]

/-- **Second copy loop of the composite machine.** Consider the composite program of machines
$M_1$ and $M_2$ with symbol translation $\varphi$. Suppose it is at the label that pops the
scratch stack, with state $(v_1, v_2, o)$, with $M_1$'s stacks holding $S_1$, $M_2$'s stacks
holding $S_2$, and the scratch stack holding the list $t$. Then after exactly $2|t| + 1$ steps it
is at the start label of $M_2$, with state $(v_1, v_2, \mathrm{none})$, $M_1$'s stacks still
$S_1$, $M_2$'s input stack holding the reverse of $t$ followed by its previous contents, $M_2$'s
other stacks unchanged, and the scratch stack empty. -/
theorem copy₂ (t : List (X M₂)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) :
    (flip bind (TM2.step (prog M₁ M₂ φ)))^[2 * t.length + 1]
        (some ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none),
        mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (t.reverse ++ S₂ M₂.k₀)) []⟩ := by
  induction t generalizing o S₂ with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop2_nil φ v₁ v₂ o S₁ S₂)]
      simp
  | cons x t ih =>
      rw [show 2 * (x :: t).length + 1 = (2 * t.length + 1) + 1 + 1 by
          simp only [List.length_cons]; omega,
        iter_step (step_pop2_cons φ v₁ v₂ o S₁ S₂ t x), iter_step (step_push2 φ _ _ _ _ _), ih]
      simp [update_idem]

/-! ### Output length is bounded by input length plus pushes -/

section length

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- **Number of push instructions in a TM2 statement.** For a statement $q$ of a multi-stack
Turing machine (Mathlib's TM2 model), this is the number of push nodes in $q$: a push node counts
$1$ plus the count of its continuation; peek, pop and load nodes count as their continuation; a
branch counts the sum of its two branches; goto and halt count $0$.

It is an upper bound on the number of symbols pushed in one step. -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

theorem length_stepAux (k : K) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
      simp only [TM2.stepAux, pushes]
      refine (ih _ _).trans ?_
      by_cases h : k = k'
      · subst h; simp; omega
      · simp [update_of_ne h]
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
      simp only [TM2.stepAux, pushes]
      refine (ih _ _).trans ?_
      by_cases h : k = k'
      · subst h; simp
      · simp [update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, pushes]
      cases f v
      · exact (ih₂ v S).trans (by omega)
      · exact (ih₁ v S).trans (by omega)
  | goto f => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end length

/-- **Push bound of a finite multi-stack Turing machine.** For a finite multi-stack Turing
machine $M$ (Mathlib's TM2 model with finitely many labels), the push bound of $M$ is the sum,
over all labels $l$ of $M$, of the number of push instructions in the statement that $M$
assigns to $l$.

No stack of $M$ grows by more than the push bound in a single step. -/
noncomputable def pushBound (M : FinTM2) : ℕ := ∑ l, pushes (M.m l)

theorem length_step (M : FinTM2) (k : M.K) {c c' : M.Cfg} (h : M.step c = some c') :
    (c'.stk k).length ≤ (c.stk k).length + pushBound M := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    rw [← Option.some.inj h]
    have hl : pushes (M.m l) ≤ pushBound M :=
      Finset.single_le_sum (f := fun l => pushes (M.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    exact (length_stepAux k _ v S).trans (Nat.add_le_add_left hl _)

theorem length_iter (M : FinTM2) (k : M.K) :
    ∀ (n : ℕ) (c d : M.Cfg), (flip bind M.step)^[n] (some c) = some d →
      (d.stk k).length ≤ (c.stk k).length + pushBound M * n := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h
      subst h; simp
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind M.step)^[n] (M.step c) = some d at h
      cases hc : M.step c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          have h₁ := ih c' d h
          have h₂ := length_step M k hc
          rw [Nat.mul_succ]
          omega

/-! ### Monotonicity of `Polynomial ℕ` evaluation -/

/-- **Evaluation of a natural-number polynomial is monotone.** For every polynomial $p$ with
coefficients in $\mathbb{N}$ and all natural numbers $a \le b$, we have $p(a) \le p(b)$. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-! ### Initial and halting configurations -/

/-- **Stacks of the initial configuration are no longer than the input.** Let $M$ be a finite
multi-stack Turing machine (Mathlib's TM2 model with finitely many stacks, function labels and
internal states, and a finite input alphabet) with input stack $k_0$, and let $l$ be a list of
symbols from the alphabet of stack $k_0$. Then for every stack $k$ of $M$, the stack $k$ in the
initial configuration of $M$ on input $l$ has length at most the length of $l$.

The initial configuration holds $l$ on stack $k_0$ and leaves every other stack empty. -/
theorem initList_stk_length_le (M : FinTM2) (l : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M l).stk k).length ≤ l.length := by
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_stk_self (M : FinTM2) (l : List (M.Γ M.k₁)) : (haltList M l).stk M.k₁ = l := by
  simp [haltList]

theorem update_haltList_stk (M : FinTM2) (l : List (M.Γ M.k₁)) :
    update (haltList M l).stk M.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [haltList, h]

theorem update_nil_eq_initList (M : FinTM2) (l : List (M.Γ M.k₀)) :
    update (fun _ => []) M.k₀ l = (initList M l).stk := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem initList_compTM (l : List (M₁.Γ M₁.k₀)) :
    initList (compTM M₁ M₂ φ) l = emb₁ (initList M₁ l) := by
  simp only [initList, emb₁, lab₁]
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases h : k = M₁.k₀
    · subst h; simp [mkStk, compTM]; try rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]
  · simp [mkStk, compTM]

theorem haltList_compTM (l : List (M₂.Γ M₂.k₁)) :
    haltList (compTM M₁ M₂ φ) l = emb₂ (haltList M₂ l) := by
  simp only [haltList, emb₂, Option.map_none]
  congr 1
  funext k
  rcases k with k | k | u
  · simp [mkStk, compTM]
  · by_cases h : k = M₂.k₁
    · subst h; simp [mkStk, compTM]; try rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]

/-! ### The composition theorem -/

section main

variable {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
  {f : α → β} {g : β → γ}

/-- **Symbol translation between composed machines.** Let $h_1$ be a polynomial-time TM2
computation of $f : \alpha \to \beta$ and $h_2$ one of $g : \beta \to \gamma$, where $\beta$ is
encoded by lists over an alphabet $\Gamma_\beta$. A symbol $y$ of the output-stack alphabet of
$h_1$'s machine is sent to the symbol of the input-stack alphabet of $h_2$'s machine that
corresponds, under $h_2$'s input alphabet bijection with $\Gamma_\beta$, to the letter that $y$
corresponds to under $h_1$'s output alphabet bijection with $\Gamma_\beta$. -/
def glue (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    h₁.tm.Γ h₁.tm.k₁ → X h₂.tm :=
  fun y => h₂.inputAlphabet.symm (h₁.outputAlphabet y)

/-- **Intermediate length bound of the composite machine.** Let $h_1$ be a polynomial-time TM2
computation of $f : \alpha \to \beta$ with polynomial time bound $p_1 \in \mathbb{N}[X]$, and let
$c$ be the push bound of the machine of $h_1$. This is the polynomial
$X + c\,p_1 \in \mathbb{N}[X]$.

Evaluated at the length $n$ of an input, its value $n + c\,p_1(n)$ bounds the length of the
intermediate string that the machine of $h_1$ writes for the composite machine. -/
noncomputable def midPoly (h₁ : TM2ComputableInPolyTime eα eβ f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (pushBound h₁.tm) * h₁.time

/-- **Time bound of the composite machine.** Let $p_1, p_2 \in \mathbb{N}[X]$ be the polynomial time
bounds of a machine $M_1$ computing $f$ and a machine $M_2$ computing $g$, and let $c$ be the sum,
over the labels of $M_1$, of the number of push instructions in the statement at that label. The
composite time bound is the polynomial $p_1 + 4(X + c\,p_1) + 2 + p_2 \circ (X + c\,p_1)$.

The two copy loops take $2m + 1$ steps each on an intermediate string of length
$m \le n + c\,p_1(n)$, where $n$ is the input length. -/
noncomputable def compTime (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : Polynomial ℕ :=
  h₁.time + Polynomial.C 4 * midPoly h₁ + Polynomial.C 2 + h₂.time.comp (midPoly h₁)

/-- **The composite machine computes the composite function in time.** Let $M_1$ compute
$f : \alpha \to \beta$ in polynomial time from the encoding $e_\alpha$ to $e_\beta$, and let $M_2$
compute $g : \beta \to \gamma$ in polynomial time from $e_\beta$ to $e_\gamma$. For every
$a \in \alpha$, let $n$ be the length of $e_\alpha(a)$ and $T$ the composite time bound. Started on
$e_\alpha(a)$, written in the input alphabet of $M_1$, the composite machine of $M_1$ and $M_2$
(with the glue map from output symbols of $M_1$ to input symbols of $M_2$) reaches within
$T(n)$ steps the halted configuration whose output stack holds $e_\gamma(g(f(a)))$, written in the
output alphabet of $M_2$, whose other stacks are empty and whose internal state is the initial
one. -/
noncomputable def compOutputs (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (a : α) :
    TM2OutputsInTime (compTM h₁.tm h₂.tm (glue h₁ h₂))
      (List.map h₁.inputAlphabet.invFun (eα a))
      (some (List.map h₂.outputAlphabet.invFun (eγ (g (f a)))))
      ((compTime h₁ h₂).eval (eα a).length) := by
  let φ := glue h₁ h₂
  let inp := List.map h₁.inputAlphabet.invFun (eα a)
  let L := List.map h₁.outputAlphabet.invFun (eβ (f a))
  let inp₂ := List.map h₂.inputAlphabet.invFun (eβ (f a))
  let out := List.map h₂.outputAlphabet.invFun (eγ (g (f a)))
  obtain ⟨⟨s₁, e₁⟩, hs₁⟩ := h₁.outputsFun a
  obtain ⟨⟨s₂, e₂⟩, hs₂⟩ := h₂.outputsFun (f a)
  change (flip bind h₁.tm.step)^[s₁] (some (initList h₁.tm inp)) =
      some (haltList h₁.tm L) at e₁
  change (flip bind h₂.tm.step)^[s₂] (some (initList h₂.tm inp₂)) =
      some (haltList h₂.tm out) at e₂
  -- Phase 1: run `M₁`.
  have P₁ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[s₁]
      (some (emb₁ (M₂ := h₂.tm) (initList h₁.tm inp))) =
      some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L)) :=
    iter_sim (emb₁ (M₂ := h₂.tm)) (fun _ _ h => step_emb₁ φ h) _ _ _ e₁
  -- Copy loop 1.
  have P₂ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[2 * L.length + 1]
      (some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L))) =
      some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩ :=
    copy₁ φ L _ _ _ _ _ _ (haltList_stk_self _ _)
  -- Copy loop 2, ending in `M₂`'s initial configuration.
  have hT : ((L.map φ).reverse ++ []).reverse ++ [] = inp₂ := by
    simp [L, inp₂, φ, glue, List.map_map, Function.comp_def]
  have P₃ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[2 * ((L.map φ).reverse ++ []).length + 1]
      (some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩) =
      some (emb₂ (M₁ := h₁.tm) (initList h₂.tm inp₂)) := by
    rw [copy₂, update_haltList_stk]
    rw [hT, update_nil_eq_initList]
    rfl
  -- Phase 2: run `M₂`.
  have P₄ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[s₂]
      (some (emb₂ (M₁ := h₁.tm) (initList h₂.tm inp₂))) =
      some (emb₂ (M₁ := h₁.tm) (haltList h₂.tm out)) :=
    iter_sim (emb₂ (M₁ := h₁.tm)) (fun _ _ h => step_emb₂ φ h) _ _ _ e₂
  refine ⟨⟨s₂ + (2 * ((L.map φ).reverse ++ []).length + 1) + (2 * L.length + 1) +
    s₁, ?_⟩, ?_⟩
  · change (flip bind (compTM h₁.tm h₂.tm φ).step)^[_]
        (some (initList (compTM h₁.tm h₂.tm φ) inp)) =
      Option.map (haltList (compTM h₁.tm h₂.tm φ)) (some out)
    rw [initList_compTM]; simp only [Option.map]; rw [haltList_compTM]
    change (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[_] _ = _
    erw [iterate_add_apply, iterate_add_apply, iterate_add_apply]
    erw [P₁, P₂, P₃, P₄]
    rfl
  · -- Time bound.
    change s₁ ≤ h₁.time.eval (eα a).length at hs₁
    change s₂ ≤ h₂.time.eval (eβ (f a)).length at hs₂
    have hlen := length_iter h₁.tm h₁.tm.k₁ _ _ _ e₁
    rw [haltList_stk_self] at hlen
    have hinit := initList_stk_length_le h₁.tm inp h₁.tm.k₁
    have hL : L.length = (eβ (f a)).length := by simp [L]
    have hinp : inp.length = (eα a).length := by simp [inp]
    have hm : (eβ (f a)).length ≤
        (eα a).length + pushBound h₁.tm * h₁.time.eval (eα a).length := by
      have := Nat.mul_le_mul_left (pushBound h₁.tm) hs₁
      omega
    have hp₂ := eval_mono h₂.time hm
    have hmid : (midPoly h₁).eval (eα a).length =
        (eα a).length + pushBound h₁.tm * h₁.time.eval (eα a).length := by
      simp [midPoly]
    simp only [compTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, hmid]
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
      Nat.add_zero, hL]
    omega

/-- **The composite polynomial-time TM2 computation.** Let $h_1$ be a polynomial-time TM2
computation of $f : \alpha \to \beta$ with respect to encodings $e_\alpha$ and $e_\beta$, and
let $h_2$ be one of $g : \beta \to \gamma$ with respect to $e_\beta$ and $e_\gamma$. This is the
polynomial-time TM2 computation of $g \circ f$ with respect to $e_\alpha$ and $e_\gamma$ whose
machine is the composite machine of the machines of $h_1$ and $h_2$ with the glue map between
them, whose input alphabet bijection is that of $h_1$, whose output alphabet bijection is that of
$h_2$, and whose time bound is the composite time bound of $h_1$ and $h_2$.

It witnesses that polynomial-time TM2 computability is closed under composition. -/
noncomputable def compComputable (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : TM2ComputableInPolyTime eα eγ (g ∘ f) where
  tm := compTM h₁.tm h₂.tm (glue h₁ h₂)
  inputAlphabet := h₁.inputAlphabet
  outputAlphabet := h₂.outputAlphabet
  time := compTime h₁ h₂
  outputsFun := compOutputs h₁ h₂

end main

end MetaMathlibExt.TM2Composition

namespace MetaMathlibExt

open Turing

/-- **Polynomial-time TM2-computable functions are closed under composition.** Let $\alpha$,
$\beta$, $\gamma$ be types encoded as lists over alphabets by $e_\alpha$, $e_\beta$, $e_\gamma$.
If $f : \alpha \to \beta$ is computable in polynomial time by a multi-stack Turing machine (a
TM2 machine) with respect to $e_\alpha$ and $e_\beta$, and $g : \beta \to \gamma$ is computable
in polynomial time by a TM2 machine with respect to $e_\beta$ and $e_\gamma$, then there is a TM2
machine computing $g \circ f$ in polynomial time with respect to $e_\alpha$ and $e_\gamma$.

Source: Mathlib PR #44441 states the same result as `TM2ComputableInPolyTime.comp`. -/
theorem tm2ComputableInPolyTime_comp {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) :=
  ⟨TM2Composition.compComputable h₁ h₂⟩

namespace ComplexityTheory

open Computability

/-- **Composition of polynomial-time functions under encodings.** Let $e_\alpha$, $e_\beta$,
$e_\gamma$ be encodings of types $\alpha$, $\beta$, $\gamma$ as lists over alphabets
$\Gamma_\alpha$, $\Gamma_\beta$, $\Gamma_\gamma$. If $f : \alpha \to \beta$ is polynomial-time
computable with respect to $e_\alpha$ and $e_\beta$, and $g : \beta \to \gamma$ is polynomial-time
computable with respect to $e_\beta$ and $e_\gamma$, then $g \circ f$ is polynomial-time
computable with respect to $e_\alpha$ and $e_\gamma$. -/
theorem IsPolyTimeWithEncoding.comp {α β γ Γα Γβ Γγ : Type} {ea : Encoding α Γα}
    {eb : Encoding β Γβ} {ec : Encoding γ Γγ} {f : α → β} {g : β → γ}
    (hf : IsPolyTimeWithEncoding ea eb f) (hg : IsPolyTimeWithEncoding eb ec g) :
    IsPolyTimeWithEncoding ea ec (g ∘ f) :=
  let ⟨h₁⟩ := hf
  let ⟨h₂⟩ := hg
  tm2ComputableInPolyTime_comp h₁ h₂

/-- **Polynomial-time functions are closed under composition.** Let $\alpha$, $\beta$, $\gamma$ be
types with canonical bitstring encodings. If $f : \alpha \to \beta$ and $g : \beta \to \gamma$ are
polynomial-time computable, then so is $g \circ f$. -/
theorem IsPolyTime.comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β} {g : β → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) :=
  IsPolyTimeWithEncoding.comp hf hg

/-- **P is closed under polynomial-time preimages.** Let $L$ be a decision problem on bitstrings and
let $f$ be a polynomial-time computable function from bitstrings to bitstrings. If $L$ is in P,
then $L \circ f$ is in P. In particular P is closed under polynomial-time many-one reductions. -/
theorem comp_mem_P {L : DecisionProblem} {f : List Bool → List Bool} (hL : L ∈ P)
    (hf : IsPolyTime f) : L ∘ f ∈ P :=
  IsPolyTime.comp hf hL

end ComplexityTheory

end MetaMathlibExt
