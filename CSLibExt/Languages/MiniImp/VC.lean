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
# Sufficient verification preconditions for MiniImp

`wp c Q s` is a sufficient condition for `Q` on every terminating run from `s`.
It is not claimed mathematically weakest: loop annotations are arbitrary ghost
predicates, and a read's precondition additionally requires in-bounds access
rather than admitting vacuous correctness of a stuck command. `wp_sound` proves
partial correctness only; `BinarySearch.lean` separately proves executable
termination for its concrete program.

While uses the annotated invariant `I`: `wp` requires `I` at entry,
`I ∧ ¬ b → Q` at exit, and `I ∧ b → wp c I` for the body.
-/

/-- Sufficient verification precondition, including read bounds and annotated
loop obligations. -/
def wp : Stmt → (State → Prop) → (State → Prop)
  | .skip, Q => Q
  | .assign x e, Q => fun s => Q (State.update s x (evalA e s))
  | .read x xs e, Q => fun s => ∃ h : evalA e s < xs.size,
      Q (State.update s x xs[evalA e s])
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
  | read _ => exact hwp.2
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
