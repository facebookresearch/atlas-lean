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

/-- **One-step unfolding functional of a while loop.** Given a Boolean expression $b$ (the guard)
and a binary relation $B$ on states (the body relation), the functional sends a relation $R$ on
states to the relation that relates $s$ to $s'$ exactly when either $b$ evaluates to false in
$s$ and $s' = s$, or $b$ evaluates to true in $s$ and there is a state $m$ with $B$ relating
$s$ to $m$ and $R$ relating $m$ to $s'$. -/
def whileFun (guard : BExp) (body : State → State → Prop)
    (R : State → State → Prop) : State → State → Prop :=
  fun s s' => (guard.eval s = false ∧ s' = s) ∨
    (guard.eval s = true ∧ ∃ m, body s m ∧ R m s')

/-- **Monotonicity of the while-loop unfolding functional.** Let $b$ be a Boolean expression, $B$
a binary relation on states, and $\Phi$ the one-step unfolding functional of a while loop with
guard $b$ and body relation $B$. Then $\Phi$ is monotone for inclusion of relations: for all
relations $R_1$ and $R_2$ on states with $R_1 \subseteq R_2$, we have
$\Phi(R_1) \subseteq \Phi(R_2)$. -/
theorem whileFun_mono {guard : BExp} {body : State → State → Prop} :
    Monotone (whileFun guard body) := by
  intro R₁ R₂ hle s s' h
  rcases h with ⟨hfalse, rfl⟩ | ⟨htrue, m, hbody, hloop⟩
  · exact Or.inl ⟨hfalse, rfl⟩
  · exact Or.inr ⟨htrue, m, hbody, hle m s' hloop⟩

/-- **The while-loop functional as a monotone map.** For a boolean guard $b$ and a relation $B$
between states (the body denotation), this is the map $\Phi$ on relations between states, ordered
by inclusion, where $\Phi(R)$ relates $s$ to $s'$ exactly when either $b$ is false in $s$ and
$s' = s$, or $b$ is true in $s$ and there is a state $m$ with $B(s, m)$ and $R(m, s')$. The map
$\Phi$ is monotone: $R_1 \subseteq R_2$ implies $\Phi(R_1) \subseteq \Phi(R_2)$. -/
def whileOrderHom (guard : BExp) (body : State → State → Prop) :
    (State → State → Prop) →o (State → State → Prop) :=
  ⟨whileFun guard body, whileFun_mono⟩

@[simp]
theorem whileOrderHom_apply (guard : BExp) (body : State → State → Prop)
    (R : State → State → Prop) :
    whileOrderHom guard body R = whileFun guard body R := rfl

/-- **Relational denotational semantics of IMP.** The denotation of an IMP command is a binary
relation on states, defined by recursion on the command. The command $\mathtt{skip}$ relates
$s$ to $s'$ iff $s' = s$. For a variable identifier $x$ and an arithmetic expression $a$, the
assignment $x := a$ relates $s$ to $s'$ iff $s'$ is $s$ with $x$ updated to the value of $a$
in $s$. The sequence $c_1; c_2$ relates $s$ to $s'$ iff there is a state $m$ such that $c_1$
relates $s$ to $m$ and $c_2$ relates $m$ to $s'$. For a Boolean expression $b$, the conditional
$\mathtt{if}\ b\ \mathtt{then}\ t\ \mathtt{else}\ e$ relates $s$ to $s'$ iff either $b$
evaluates to true in $s$ and $t$ relates $s$ to $s'$, or $b$ evaluates to false in $s$ and $e$
relates $s$ to $s'$. The denotation of $\mathtt{while}\ b\ \mathtt{do}\ c$ is the least fixed
point, for inclusion of relations, of the one-step unfolding functional of a while loop with
guard $b$ and body relation the denotation of $c$. -/
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

/-- **The while denotation is a fixed point.** Let $b$ be a Boolean expression and $c$ an IMP
command, let $W$ be the relational denotation of $\mathtt{while}\ b\ \mathtt{do}\ c$, and let
$\Phi$ be the one-step unfolding functional of a while loop with guard $b$ and body relation the
denotation of $c$. Then $W = \Phi(W)$. -/
theorem while_eq {b : BExp} {c : Cmd} :
    Denote (.while b c) = whileFun b (Denote c) (Denote (.while b c)) :=
  (OrderHom.map_lfp (whileOrderHom b (Denote c))).symm

/-- **Unfolding equation for the while denotation.** For every Boolean expression $b$, IMP command
$c$ and states $s$ and $s'$, the relational denotation of $\mathtt{while}\ b\ \mathtt{do}\ c$
relates $s$ to $s'$ if and only if either $b$ evaluates to false in $s$ and $s' = s$, or $b$
evaluates to true in $s$ and there is a state $m$ such that the denotation of $c$ relates $s$ to
$m$ and the denotation of the loop relates $m$ to $s'$. -/
theorem while_iff {b : BExp} {c : Cmd} {s s' : State} :
    Denote (.while b c) s s' ↔
      (b.eval s = false ∧ s' = s) ∨
        (b.eval s = true ∧ ∃ m, Denote c s m ∧ Denote (.while b c) m s') := by
  conv_lhs => rw [while_eq]
  exact Iff.rfl

/-- **Park induction for while loops.** Let $b$ be a Boolean expression, $c$ an IMP command and
$P$ a binary relation on states, and let $\Phi$ be the one-step unfolding functional of a while
loop with guard $b$ and body relation the denotation of $c$. If $\Phi(P) \subseteq P$, then
for all states $s$ and $s'$ related by the relational denotation of
$\mathtt{while}\ b\ \mathtt{do}\ c$, $P$ relates $s$ to $s'$. -/
theorem while_ind {b : BExp} {c : Cmd} {P : State → State → Prop}
    (hP : ∀ s s', whileFun b (Denote c) P s s' → P s s')
    {s s' : State} (h : Denote (.while b c) s s') : P s s' :=
  OrderHom.lfp_le (whileOrderHom b (Denote c)) (fun s s' => hP s s') s s' h

/-- **Denotational executions are big-step executions.** For every IMP command $c$ and all
states $s$ and $s'$, if the relational denotation of $c$ relates $s$ to $s'$, then executing $c$
from $s$ terminates in $s'$ according to the big-step semantics. -/
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

/-- **Big-step executions are denotational executions.** For every IMP command $c$ and all
states $s$ and $s'$, if executing $c$ from $s$ terminates in $s'$ according to the big-step
semantics, then the relational denotation of $c$ relates $s$ to $s'$. -/
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

/-- **Agreement of the denotational and big-step semantics of IMP.** For every IMP command $c$
and all states $s$ and $s'$, the relational denotation of $c$ relates $s$ to $s'$ if and only
if executing $c$ from $s$ terminates in $s'$ according to the big-step semantics. -/
theorem iff_bigStep {c : Cmd} {s s' : State} :
    Denote c s s' ↔ BigStep c s s' :=
  ⟨bigStep_of_denote, denote_of_bigStep⟩

/-- **The denotational semantics of IMP is deterministic.** For every IMP command $c$ and all
states $s$, $s_1$ and $s_2$, if the relational denotation of $c$ relates $s$ to $s_1$ and $s$
to $s_2$, then $s_1 = s_2$.

The proof goes through the agreement with the deterministic big-step semantics. -/
theorem deterministic {c : Cmd} {s s₁ s₂ : State}
    (h₁ : Denote c s s₁) (h₂ : Denote c s s₂) : s₁ = s₂ :=
  BigStep.deterministic (iff_bigStep.mp h₁) (iff_bigStep.mp h₂)

end Denote

end Cslib.IMP
