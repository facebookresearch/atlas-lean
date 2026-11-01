/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.Semantics

@[expose] public section

namespace CSLibExt.Languages.MiniImp

/-!
# Hoare rules for MiniImp (Weeks 3-4 core, 90-day plan #3 LOGICS)

Partial-correctness Hoare triples, proved for skip / assignment /
sequencing / if / while. The while rule is induction on the `BigStep`
derivation with the loop invariant generalized.

VC generation (symbolic evaluation of these rules into verification
conditions) is the Weeks 5-8 deliverable; binary search is its demo.
-/

/-- Partial-correctness Hoare triple: every terminating run from `P`
ends in `Q`. -/
def Hoare (P : State → Prop) (c : Stmt) (Q : State → Prop) : Prop :=
  ∀ s s', P s → BigStep c s s' → Q s'

/-- Skip rule. -/
theorem hoare_skip (P : State → Prop) : Hoare P .skip P := by
  intro s s' hP h
  cases h with
  | skip => exact hP

/-- Assignment rule (backwards: precondition is `Q` with the update
applied). -/
theorem hoare_assign {x : String} {e : AExp} {Q : State → Prop} :
    Hoare (fun s => Q (State.update s x (evalA e s))) (.assign x e) Q := by
  intro s s' hP h
  cases h with
  | assign => exact hP

/-- Sequencing rule. -/
theorem hoare_seq {P R Q : State → Prop} {c₁ c₂ : Stmt} :
    Hoare P c₁ R → Hoare R c₂ Q → Hoare P (.seq c₁ c₂) Q := by
  intro h₁ h₂ s s' hP h
  cases h with
  | seq h₁' h₂' => exact h₂ _ _ (h₁ _ _ hP h₁') h₂'

/-- If rule. -/
theorem hoare_if {P Q : State → Prop} {b : BExp} {c₁ c₂ : Stmt} :
    Hoare (fun s => P s ∧ beval b s) c₁ Q →
      Hoare (fun s => P s ∧ ¬ beval b s) c₂ Q →
      Hoare P (.if_ b c₁ c₂) Q := by
  intro h₁ h₂ s s' hP h
  cases h with
  | ifTrue hb h₁' => exact h₁ _ _ ⟨hP, hb⟩ h₁'
  | ifFalse hb h₂' => exact h₂ _ _ ⟨hP, hb⟩ h₂'

/-- While rule: invariant `P` holds at entry and is preserved by the
body, so it holds at exit together with `¬ b`. Proved by induction on
the `BigStep` derivation, with the loop identified by an equality
hypothesis so the recursor's non-while cases are discharged by
constructor clash. -/
theorem hoare_while {P : State → Prop} {b : BExp} {c : Stmt} :
    Hoare (fun s => P s ∧ beval b s) c P →
      Hoare P (.while b c) (fun s => P s ∧ ¬ beval b s) := by
  intro hbody s s' hP h
  have key : ∀ {c' : Stmt} {s s' : State}, BigStep c' s s' →
      ∀ (b : BExp) (c₀ : Stmt), c' = .while b c₀ →
        Hoare (fun s => P s ∧ beval b s) c₀ P → P s → P s' ∧ ¬ beval b s' := by
    intro c' s s' h
    induction h with
    | skip => intro _ _ heq _ _; cases heq
    | assign => intro _ _ heq _ _; cases heq
    | seq _ _ _ _ => intro _ _ heq _ _; cases heq
    | ifTrue _ _ _ => intro _ _ heq _ _; cases heq
    | ifFalse _ _ _ => intro _ _ heq _ _; cases heq
    | whileFalse hn => intro _ _ heq _ hP; cases heq; exact ⟨hP, hn⟩
    | whileTrue hb h₁ _ _ ih₂ =>
        intro _ _ heq hbody' hP; cases heq
        exact ih₂ _ _ rfl hbody' (hbody' _ _ ⟨hP, hb⟩ h₁)
  exact key h _ _ rfl hbody hP

end CSLibExt.Languages.MiniImp
