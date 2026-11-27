/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Semantics.LTS.HasTau
public import Mathlib.Data.Set.Basic

/-!
# Input-output conformance of labelled transition systems

Following Tretmans, *Model Based Testing with Labelled Transition Systems*, LNCS 4949 (2008),
Definitions 7–9 and 11–12, observe quiescence as a self-loop and compare possible outputs
on the specification's suspension traces. The definitions are meaningful on arbitrary
transition systems; the source restricts its testing theory to image-finite and strongly
converging systems. No test-generation or decidability result is claimed here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Testing.Ioco

/-- Inputs, outputs and the silent action have disjoint tags. -/
inductive Action (Input Output : Type*) where
  | input (label : Input)
  | output (label : Output)
  | tau

instance {Input Output : Type*} : HasTau (Action Input Output) where
  τ := .tau

/-- A visible suspension label is an input or an output; the extra output `none` is δ.
The silent action cannot occur in an observable word. -/
abbrev Observable (Input Output : Type*) := Input ⊕ Option Output

variable {State Impl Spec Input Output : Type*}

/-- A state is quiescent if it has no immediate output or silent step. Inputs are allowed. -/
def Quiescent (lts : LTS State (Action Input Output)) (s : State) : Prop :=
  (¬ ∃ o t, lts.Tr s (.output o) t) ∧ ¬ ∃ t, lts.Tr s .tau t

/-- The suspension system preserves the old steps and adds exactly a δ self-loop at each
quiescent state. Ordinary outputs are tagged with `some`. -/
def suspension (lts : LTS State (Action Input Output)) :
    LTS State (Action Input (Option Output)) where
  Tr s label t := match label with
    | .input i => lts.Tr s (.input i) t
    | .output (some o) => lts.Tr s (.output o) t
    | .output none => s = t ∧ Quiescent lts s
    | .tau => lts.Tr s .tau t

/-- **Residual states after a suspension trace.** Execute the visible word weakly from `s` in the
suspension system, allowing silent moves before, between and after its observations. -/
def after (lts : LTS State (Action Input Output)) (s : State)
    (word : List (Observable Input Output)) : Set State :=
  { t | (suspension lts).SMTr s (word.map (Sum.elim Action.input Action.output)) t }

/-- The empty observation permits any finite sequence of silent steps of the original system. -/
@[simp]
theorem mem_after_nil {lts : LTS State (Action Input Output)} {s t : State} :
    t ∈ after lts s [] ↔ lts.τSTr s t :=
  (LTS.sMTr_τSTr_iff (lts := suspension lts)).symm

/-- A suspension trace is a visible word with a nonempty residual set. -/
def suspensionTraces (lts : LTS State (Action Input Output)) (s : State) :
    Set (List (Observable Input Output)) :=
  { word | (after lts s word).Nonempty }

/-- The output set is the union of immediate outputs of the residual states, including δ
when at least one residual state is quiescent. Neither inputs nor silent actions are outputs. -/
def out (lts : LTS State (Action Input Output)) (states : Set State) : Set (Option Output) :=
  { o | ∃ s ∈ states, match o with
    | some a => ∃ t, lts.Tr s (.output a) t
    | none => Quiescent lts s }

/-- An implementation weakly accepts every input at every state reachable from its start.
Unreachable states do not affect input-enabledness. -/
def InputEnabled (lts : LTS State (Action Input Output)) (start : State) : Prop :=
  ∀ s, lts.CanReach start s → ∀ i, ∃ t, lts.STr s (.input i) t

/-- **Input-output conformance (ioco).** An input-enabled implementation conforms if on each
suspension trace of the specification its possible outputs are allowed by the specification.
Traces absent from the specification impose no condition; the specification need not accept
every input. -/
def Conforms (impl : LTS Impl (Action Input Output)) (implStart : Impl)
    (spec : LTS Spec (Action Input Output)) (specStart : Spec) : Prop :=
  InputEnabled impl implStart ∧
    ∀ word ∈ suspensionTraces spec specStart,
      out impl (after impl implStart word) ⊆ out spec (after spec specStart word)

end Cslib.Testing.Ioco
