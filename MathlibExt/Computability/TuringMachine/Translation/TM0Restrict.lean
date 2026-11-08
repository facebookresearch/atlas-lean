/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Restricting a single-tape machine to a supporting set of states
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Restricting a single-tape machine to a supporting set of states

Mathlib's single-tape machines (`Turing.TM0`) may have an infinite state type, with finiteness
recorded by `TM0.Supports M S`: the run from the default state stays in `S`. `restrict hS` is the
same machine with states the subtype `S`, and it evaluates exactly like `M` when its default
state is `M`'s (`eval_restrict`). For a finite set `S` the restricted machine has a finite state
type.

## Main results

- `restrict`, `eval_restrict`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM0Restrict

open Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] {M : TM0.Machine Γ Λ} {S : Set Λ} [Inhabited S]

/-- The machine `M` with its states restricted to a supporting set `S`. -/
def restrict (hS : TM0.Supports M S) : TM0.Machine Γ S := fun q a ↦
  (M q a).pbind fun p hp ↦ some (⟨p.1, hS.2 hp q.2⟩, p.2)

/-- A configuration of the restricted machine, as one of `M`. -/
def cfgVal (c : TM0.Cfg Γ S) : TM0.Cfg Γ Λ := ⟨c.q.1, c.Tape⟩

theorem step_cfgVal (hS : TM0.Supports M S) (c : TM0.Cfg Γ S) :
    TM0.step M (cfgVal c) = (TM0.step (restrict hS) c).map cfgVal := by
  obtain ⟨q, T⟩ := c
  simp only [TM0.step, cfgVal]
  cases h : M q.1 T.head with
  | none => simp [restrict, h]
  | some p =>
    obtain ⟨q', s⟩ := p
    simp only [restrict, h, Option.map_some, Option.pbind_some]
    cases s <;> rfl

/-- The restricted machine is simulated step for step by `M`. -/
theorem respects (hS : TM0.Supports M S) :
    StateTransition.Respects (TM0.step (restrict hS)) (TM0.step M) fun a b ↦ cfgVal a = b := by
  rintro a₁ _ rfl
  have e := step_cfgVal hS a₁
  cases h : TM0.step (restrict hS) a₁ with
  | none => rw [e, h]; rfl
  | some b₁ => exact ⟨_, rfl, Relation.TransGen.single (by rw [e, h]; rfl)⟩

/-- **The restricted machine evaluates like `M`**, when its default state is that of `M` (as for
the instance `⟨⟨default, hS.1⟩⟩`). -/
theorem eval_restrict (hS : TM0.Supports M S) (hdef : (default : S).1 = default) (l : List Γ) :
    TM0.eval (restrict hS) l = TM0.eval M l := by
  have h := StateTransition.tr_eval' (TM0.step (restrict hS)) (TM0.step M) cfgVal
    (respects hS) (TM0.init l)
  have hinit : cfgVal (TM0.init l : TM0.Cfg Γ S) = TM0.init l := by
    simp only [cfgVal, TM0.init, hdef]
  rw [hinit] at h
  simp only [TM0.eval, h]
  rfl

end MetaMathlibExt.TM0Restrict
