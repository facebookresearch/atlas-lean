/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.Syntax

@[expose] public section

namespace CSLibExt.Languages.MiniImp

/-!
# MiniImp big-step semantics (Weeks 3-4 core, 90-day plan #3 LOGICS)

Expression evaluation plus a big-step (natural) semantics for statements.
Partial correctness: a looping program has no `BigStep` derivation, so
Hoare triples in `Hoare.lean` say nothing about divergence.

`beval` returns a `Prop`, not `Bool`, so branch conditions stay in the
logic and the Hoare rules need no boolean coercion. `State.update` is
defined here (not `Function.update`) so this file needs no Mathlib import.
-/

/-- Evaluate an arithmetic expression in a state. -/
def evalA : AExp → State → Nat
  | .lit n, _ => n
  | .var x, s => s x
  | .add e₁ e₂, s => evalA e₁ s + evalA e₂ s

/-- Truth of a boolean expression in a state, as a `Prop`. -/
def beval : BExp → State → Prop
  | .tru, _ => True
  | .le e₁ e₂, s => evalA e₁ s ≤ evalA e₂ s
  | .and b₁ b₂, s => beval b₁ s ∧ beval b₂ s
  | .not b, s => ¬ beval b s

/-- Update state `s` at `x` to `v`, leaving other variables unchanged. -/
def State.update (s : State) (x : String) (v : Nat) : State :=
  fun y => if y = x then v else s y

/-- Big-step semantics: `BigStep c s s'` means `c` run from `s` ends in `s'`. -/
inductive BigStep : Stmt → State → State → Prop where
  | skip {s : State} : BigStep .skip s s
  | assign {x : String} {e : AExp} {s : State} :
      BigStep (.assign x e) s (State.update s x (evalA e s))
  | seq {c₁ c₂ : Stmt} {s s' s'' : State} :
      BigStep c₁ s s' → BigStep c₂ s' s'' → BigStep (.seq c₁ c₂) s s''
  | ifTrue {b : BExp} {c₁ c₂ : Stmt} {s s' : State} :
      beval b s → BigStep c₁ s s' → BigStep (.if_ b c₁ c₂) s s'
  | ifFalse {b : BExp} {c₁ c₂ : Stmt} {s s' : State} :
      ¬ beval b s → BigStep c₂ s s' → BigStep (.if_ b c₁ c₂) s s'
  | whileTrue {b : BExp} {c : Stmt} {s s' s'' : State} :
      beval b s → BigStep c s s' → BigStep (.while b c) s' s'' →
        BigStep (.while b c) s s''
  | whileFalse {b : BExp} {c : Stmt} {s : State} :
      ¬ beval b s → BigStep (.while b c) s s

/-- Skip leaves the state unchanged. -/
example {s : State} : BigStep .skip s s := BigStep.skip

/-- Assignment updates exactly the assigned variable's value. -/
example {s : State} :
    BigStep (Stmt.assign "x" (AExp.lit 3)) s (State.update s "x" 3) :=
  BigStep.assign

end CSLibExt.Languages.MiniImp
