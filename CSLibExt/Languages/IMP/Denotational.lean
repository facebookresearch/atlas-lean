/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Denotational semantics for IMP
-/
module

public import CSLibExt.Languages.IMP.BigStep
public import Mathlib.Order.FixedPoints

/-!
# Relational denotational semantics

Denotations are relations `State → State → Prop`. The denotation of a while
loop is the least fixed point of the monotone functional that performs one
loop iteration. This is a relational denotational semantics only: no
domain-theory or continuity claims are made. The main theorem states that
the denotational semantics agrees with the big-step operational semantics.
-/

@[expose] public section

namespace Cslib.IMP

/-- One unfolding of a while loop with the given guard and body denotation. -/
def whileFun (guard : BExp) (body : State → State → Prop)
    (R : State → State → Prop) : State → State → Prop :=
  fun s s' => (guard.eval s = false ∧ s' = s) ∨
    (guard.eval s = true ∧ ∃ m, body s m ∧ R m s')

/-- The while-loop functional is monotone in the candidate loop relation. -/
theorem whileFun_mono {guard : BExp} {body : State → State → Prop} :
    Monotone (whileFun guard body) := by
  intro R₁ R₂ hle s s' h
  rcases h with ⟨hfalse, rfl⟩ | ⟨htrue, m, hbody, hloop⟩
  · exact Or.inl ⟨hfalse, rfl⟩
  · exact Or.inr ⟨htrue, m, hbody, hle m s' hloop⟩

/-- The while-loop functional packaged as a monotone operator. -/
def whileOrderHom (guard : BExp) (body : State → State → Prop) :
    (State → State → Prop) →o (State → State → Prop) :=
  ⟨whileFun guard body, whileFun_mono⟩

@[simp]
theorem whileOrderHom_apply (guard : BExp) (body : State → State → Prop)
    (R : State → State → Prop) :
    whileOrderHom guard body R = whileFun guard body R := rfl

/-- The relational denotation of an IMP command. -/
def Denote : Cmd → State → State → Prop
  | .skip => fun s s' => s' = s
  | .assign n a => fun s s' => s' = Function.update s n (a.eval s)
  | .seq c₁ c₂ => fun s s' => ∃ m, Denote c₁ s m ∧ Denote c₂ m s'
  | .ite b t e => fun s s' =>
      (b.eval s = true ∧ Denote t s s') ∨ (b.eval s = false ∧ Denote e s s')
  | .while b c => (whileOrderHom b (Denote c)).lfp

namespace Denote

@[simp]
theorem skip_iff {s s' : State} : Denote .skip s s' ↔ s' = s := Iff.rfl

@[simp]
theorem assign_iff {n : Nat} {a : AExp} {s s' : State} :
    Denote (.assign n a) s s' ↔ s' = Function.update s n (a.eval s) := Iff.rfl

@[simp]
theorem seq_iff {c₁ c₂ : Cmd} {s s' : State} :
    Denote (.seq c₁ c₂) s s' ↔ ∃ m, Denote c₁ s m ∧ Denote c₂ m s' := Iff.rfl

@[simp]
theorem ite_iff {b : BExp} {t e : Cmd} {s s' : State} :
    Denote (.ite b t e) s s' ↔
      (b.eval s = true ∧ Denote t s s') ∨
        (b.eval s = false ∧ Denote e s s') := Iff.rfl

/-- The denotation of a while loop is a fixed point of the loop functional. -/
theorem while_eq {b : BExp} {c : Cmd} :
    Denote (.while b c) = whileFun b (Denote c) (Denote (.while b c)) :=
  (OrderHom.map_lfp (whileOrderHom b (Denote c))).symm

/-- The loop unfolding equation. Not a simp lemma: the right-hand side
mentions the loop denotation again, so simp would unfold indefinitely. -/
theorem while_iff {b : BExp} {c : Cmd} {s s' : State} :
    Denote (.while b c) s s' ↔
      (b.eval s = false ∧ s' = s) ∨
        (b.eval s = true ∧ ∃ m, Denote c s m ∧ Denote (.while b c) m s') := by
  conv_lhs => rw [while_eq]
  exact Iff.rfl

/-- Park induction: any relation closed under one loop unfolding contains
the loop denotation. -/
theorem while_ind {b : BExp} {c : Cmd} {P : State → State → Prop}
    (hP : ∀ s s', whileFun b (Denote c) P s s' → P s s')
    {s s' : State} (h : Denote (.while b c) s s') : P s s' :=
  OrderHom.lfp_le (whileOrderHom b (Denote c)) (fun s s' => hP s s') s s' h

/-- Every denotational execution is a big-step execution. -/
theorem bigStep_of_denote {c : Cmd} {s s' : State} (h : Denote c s s') :
    BigStep c s s' := by
  induction c generalizing s s' with
  | skip =>
      rw [skip_iff] at h
      subst h
      exact .skip _
  | assign n a =>
      rw [assign_iff] at h
      subst h
      exact .assign _ _ _
  | seq c₁ c₂ ih₁ ih₂ =>
      rw [seq_iff] at h
      obtain ⟨m, h₁, h₂⟩ := h
      exact .seq (ih₁ h₁) (ih₂ h₂)
  | ite b t e iht ihe =>
      rw [ite_iff] at h
      rcases h with ⟨hg, hb⟩ | ⟨hg, hb⟩
      · exact .iteTrue hg (iht hb)
      · exact .iteFalse hg (ihe hb)
  | «while» b c ih =>
      refine while_ind ?_ h
      intro s₁ s₂ hstep
      rcases hstep with ⟨hfalse, rfl⟩ | ⟨htrue, m, hbody, hloop⟩
      · exact .whileFalse hfalse
      · exact .whileTrue htrue (ih hbody) hloop

/-- Every big-step execution is a denotational execution. -/
theorem denote_of_bigStep {c : Cmd} {s s' : State} (h : BigStep c s s') :
    Denote c s s' := by
  induction h with
  | skip state =>
      rw [skip_iff]
  | assign state name value =>
      rw [assign_iff]
  | seq h₁ h₂ ih₁ ih₂ =>
      rw [seq_iff]
      exact ⟨_, ih₁, ih₂⟩
  | iteTrue hg hb ih =>
      rw [ite_iff]
      exact Or.inl ⟨hg, ih⟩
  | iteFalse hg hb ih =>
      rw [ite_iff]
      exact Or.inr ⟨hg, ih⟩
  | whileFalse hg =>
      rw [while_iff]
      exact Or.inl ⟨hg, rfl⟩
  | whileTrue hg hb hl ihb ihl =>
      rw [while_iff]
      exact Or.inr ⟨hg, _, ihb, ihl⟩

/-- The denotational and big-step semantics agree. -/
theorem iff_bigStep {c : Cmd} {s s' : State} :
    Denote c s s' ↔ BigStep c s s' :=
  ⟨bigStep_of_denote, denote_of_bigStep⟩

/-- Denotations are deterministic, by agreement with the big-step semantics. -/
theorem deterministic {c : Cmd} {s s₁ s₂ : State}
    (h₁ : Denote c s s₁) (h₂ : Denote c s s₂) : s₁ = s₂ :=
  BigStep.deterministic (iff_bigStep.mp h₁) (iff_bigStep.mp h₂)

end Denote

end Cslib.IMP
