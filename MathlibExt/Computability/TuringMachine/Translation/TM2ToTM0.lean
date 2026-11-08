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

/-- The single-tape (`TM0`) emulation of a multi-stack machine, through `TM1`. Its tape alphabet
is `TM2to1.Γ' K Γ`: a bottom-of-stack flag and one optional symbol per stack. -/
abbrev tr : TM0.Machine (TM2to1.Γ' K Γ) (TM1to0.Λ' (TM2to1.tr M)) :=
  TM1to0.tr (TM2to1.tr M)

/-- **The emulation halts iff the multi-stack machine halts.** -/
theorem tr_eval_dom (k : K) (L : List (Γ k)) :
    (TM0.eval (tr M) (TM2to1.trInit k L)).Dom ↔ (TM2.eval M k L).Dom := by
  rw [TM1to0.tr_eval]
  exact TM2to1.tr_eval_dom M k L

/-- **The emulation visits finitely many states**, given a finite support of the multi-stack
machine. -/
theorem tr_supports [Fintype σ] {S : Finset Λ} (ss : TM2.Supports M S) :
    TM0.Supports (tr M) ↑(TM1to0.trStmts (TM2to1.tr M) (TM2to1.trSupp M S)) :=
  TM1to0.tr_supports _ (TM2to1.tr_supports M ss)

omit [DecidableEq K] [Inhabited Λ] [Inhabited σ] in
/-- Every statement is supported by the set of all labels. -/
theorem supportsStmt_univ [Fintype Λ] : ∀ q : TM2.Stmt Γ Λ σ, TM2.SupportsStmt Finset.univ q
  | .push _ _ q => supportsStmt_univ q
  | .peek _ _ q => supportsStmt_univ q
  | .pop _ _ q => supportsStmt_univ q
  | .load _ q => supportsStmt_univ q
  | .branch _ q₁ q₂ => ⟨supportsStmt_univ q₁, supportsStmt_univ q₂⟩
  | .goto _ => fun _ ↦ Finset.mem_univ _
  | .halt => trivial

omit [DecidableEq K] [Inhabited σ] in
/-- A machine with finitely many labels is supported by all of them. -/
theorem supports_univ [Fintype Λ] : TM2.Supports M Finset.univ :=
  ⟨Finset.mem_univ _, fun q _ ↦ supportsStmt_univ (M q)⟩

end Translation

/-! ### Bundled machines -/

/-- The main label of a bundled machine, as its default label (scoped). -/
scoped instance inhabitedMainLabel (tm : FinTM2) : Inhabited tm.Λ := ⟨tm.main⟩

/-- The initial configuration of a bundled machine is `TM2.init` with the main label as default. -/
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
