/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.Hoare

@[expose] public section

namespace CSLibExt.Languages.MiniImp

/-!
# Weakest preconditions for MiniImp (Weeks 5-8, 90-day plan #3 LOGICS)

VC generation as weakest-precondition computation: `wp c Q s` is the
condition on the entry state `s` that guarantees `Q` on every
terminating run of `c`. `wp_sound` says `wp` is sound for partial
correctness: `wp c Q s` and `BigStep c s s'` give `Q s'`.

While uses the loop's annotated invariant `I` (`Stmt.while b I c`):
`wp` requires `I` at entry, `I ∧ ¬ b → Q` at exit, and
`I ∧ b → wp c I` for the body. Binary search is the demo.
-/

/-- Weakest precondition: `wp c Q s` guarantees `Q` on every
terminating run of `c` from `s`. -/
def wp : Stmt → (State → Prop) → (State → Prop)
  | .skip, Q => Q
  | .assign x e, Q => fun s => Q (State.update s x (evalA e s))
  | .seq c₁ c₂, Q => wp c₁ (wp c₂ Q)
  | .if_ b c₁ c₂, Q =>
      fun s => (beval b s → wp c₁ Q s) ∧ (¬ beval b s → wp c₂ Q s)
  | .while b I c, Q =>
      fun s => I s ∧ (∀ s', I s' ∧ ¬ beval b s' → Q s') ∧
        (∀ s', I s' ∧ beval b s' → wp c I s')

/-- Soundness of `wp` for partial correctness. -/
theorem wp_sound {c : Stmt} {s s' : State} {Q : State → Prop}
    (hwp : wp c Q s) (h : BigStep c s s') : Q s' := by
  induction h generalizing Q with
  | skip => exact hwp
  | assign => exact hwp
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hwp)
  | ifTrue hb _ ih => exact ih (hwp.1 hb)
  | ifFalse hb _ ih => exact ih (hwp.2 hb)
  | whileTrue hb _ _ ih₁ ih₂ =>
      have hbody := hwp.2.2 _ ⟨hwp.1, hb⟩
      have hIs := ih₁ hbody
      refine ih₂ ?_
      exact ⟨hIs, hwp.2.1, hwp.2.2⟩
  | whileFalse hn => exact hwp.2.1 _ ⟨hwp.1, hn⟩

end CSLibExt.Languages.MiniImp
