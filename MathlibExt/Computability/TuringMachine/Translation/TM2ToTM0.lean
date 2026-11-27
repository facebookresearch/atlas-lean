/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# From multi-stack machines to single-tape machines, preserving halting
-/
module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# From multi-stack machines to single-tape machines, preserving halting

Mathlib translates multi-stack machines (`TM2`) to single-tape machines with a store (`TM1`,
`Turing.TM2to1.tr`) and those to plain single-tape machines (`TM0`, `Turing.TM1to0.tr`). This file
composes the two translations and records the facts needed to use the composite as a reduction:

* `tr_eval_dom` : the composite halts on the encoded input iff the multi-stack machine halts.
  Mathlib's `TM2to1.tr_eval` relates only outputs; halting comes from `TM2to1.tr_eval_dom`, and
  `TM1to0.tr_eval` is an equality of evaluations.
* `tr_supports` : the composite only visits a finite set of states, built from the finite
  supports `TM2to1.trSupp` and `TM1to0.trStmts`.
* `supports_univ`, `initList_eq_init` : bridges for bundled machines (`FinTM2`). A machine with
  finitely many labels is supported by all of them, and the run of a `FinTM2` from `initList`
  is the run of `TM2.eval` with the main label as default (a scoped instance).

## Main results

- `tr`, `tr_eval_dom`, `tr_supports`.
- `supportsStmt_univ`, `supports_univ`, `initList_eq_init`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM2ToTM0

open Turing

section Translation

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*} [Inhabited Λ] [Inhabited σ]
  (M : Λ → TM2.Stmt Γ Λ σ)

/-- **Two-step single-tape translation of a multi-stack machine.** For a multi-stack Turing
machine $M$ with stacks indexed by $K$ and stack alphabets $\Gamma_k$, this is the single-tape
machine obtained by translating $M$ first into a single-tape machine with a store and then into a
plain single-tape machine. Its tape alphabet consists of a bottom-of-stack flag together with one
optional symbol of $\Gamma_k$ for each stack $k$. Its states are pairs of an optional statement of
the intermediate machine and a value of the internal state of $M$. -/
abbrev tr : TM0.Machine (TM2to1.Γ' K Γ) (TM1to0.Λ' (TM2to1.tr M)) :=
  TM1to0.tr (TM2to1.tr M)

/-- **The emulation halts iff the multi-stack machine halts.** Let $M$ be a multi-stack Turing
machine with stacks indexed by $K$, let $k \in K$, and let $L$ be a list over the alphabet of stack
$k$. The single-tape emulation of $M$, started on the tape encoding of the stacks with $L$ on stack
$k$ and all other stacks empty, halts if and only if $M$, started with $L$ on stack $k$ and all
other stacks empty, halts. -/
theorem tr_eval_dom (k : K) (L : List (Γ k)) :
    (TM0.eval (tr M) (TM2to1.trInit k L)).Dom ↔ (TM2.eval M k L).Dom := by
  rw [TM1to0.tr_eval]
  exact TM2to1.tr_eval_dom M k L

/-- **The emulation visits finitely many states.** Let $M$ be a multi-stack Turing machine whose
internal state type is finite, and let $S$ be a finite set of labels that supports $M$. Then the
single-tape emulation of $M$ is supported by an explicit finite set of states built from $S$ through
the two translations: this set contains the initial state and is closed under the transitions of the
emulation. -/
theorem tr_supports [Fintype σ] {S : Finset Λ} (ss : TM2.Supports M S) :
    TM0.Supports (tr M) ↑(TM1to0.trStmts (TM2to1.tr M) (TM2to1.trSupp M S)) :=
  TM1to0.tr_supports _ (TM2to1.tr_supports M ss)

omit [DecidableEq K] [Inhabited Λ] [Inhabited σ] in
/-- **Every statement is supported by all labels.** If the label type $\Lambda$ is finite, then
every statement of a multi-stack Turing machine with labels $\Lambda$ is supported by the finite set
of all labels: every label it can jump to lies in this set. -/
theorem supportsStmt_univ [Fintype Λ] : ∀ q : TM2.Stmt Γ Λ σ, TM2.SupportsStmt Finset.univ q
  | .push _ _ q => supportsStmt_univ q
  | .peek _ _ q => supportsStmt_univ q
  | .pop _ _ q => supportsStmt_univ q
  | .load _ q => supportsStmt_univ q
  | .branch _ q₁ q₂ => ⟨supportsStmt_univ q₁, supportsStmt_univ q₂⟩
  | .goto _ => fun _ ↦ Finset.mem_univ _
  | .halt => trivial

omit [DecidableEq K] [Inhabited σ] in
/-- **A multi-stack machine is supported by all its labels.** A multi-stack Turing machine with
finitely many labels is supported by the set of all its labels: this set contains the default label,
and every statement of the machine is supported by it. -/
theorem supports_univ [Fintype Λ] : TM2.Supports M Finset.univ :=
  ⟨Finset.mem_univ _, fun q _ ↦ supportsStmt_univ (M q)⟩

end Translation

/-! ### Bundled machines -/

/-- The main label of a bundled machine, as its default label (scoped). -/
scoped instance inhabitedMainLabel (tm : FinTM2) : Inhabited tm.Λ := ⟨tm.main⟩

/-- **The initial configuration of a bundled multi-stack machine.** For a bundled multi-stack Turing
machine and every list $l$ over the alphabet of its input stack, the initial configuration of the
bundled machine on $l$ equals the generic multi-stack initial configuration with $l$ on the input
stack, when the main label is taken as the default label. -/
theorem initList_eq_init (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    initList tm l = TM2.init tm.k₀ l := by
  simp only [initList, TM2.init]
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h
    simp
  · simp [h]

end MetaMathlibExt.TM2ToTM0
