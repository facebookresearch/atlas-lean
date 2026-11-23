/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

import CSLibExt.Security.Noninterference.Soundness

/-! Positive IMP programs, explicit and implicit leaks, and a termination channel. -/

open Cslib.IMP
open Cslib.Security.Noninterference

namespace Cslib.Security.Noninterference.Tests

/-- Variable zero is public; variable one is secret. -/
def policy : Policy := fun x => decide (x = 1)

def zero : Store := fun _ => 0
def secretOne : Store := fun x => if x = 1 then 1 else 0

theorem initial_agreement : LowEquiv policy zero secretOne := by
  intro x hx
  simp [policy] at hx
  simp [zero, secretOne, hx]

/-- Test an arithmetic expression for being nonzero. -/
def nonzero (e : AExp) : BExp := .not (.eq e (.const 0))

/-- Public data may flow into a secret variable. -/
example : CmdSecure policy false (.assign 1 (.var 0)) :=
  .assign (by simp [policy]) (.var (by simp [policy]))

/-- A secret guard can control secret writes. -/
example : CmdSecure policy false
    (.ite (nonzero (.var 1)) (.assign 1 (.const 2)) (.assign 1 (.const 3))) :=
  .ite (l := true) (.not (.eq (.var (by simp [policy])) (.const _ _)))
    (.assign (by simp [policy]) (.const _ _))
    (.assign (by simp [policy]) (.const _ _))

/-- A public guard and a body that resets it form a secure loop. -/
def resetLoop : Cmd := .while (nonzero (.var 0)) (.assign 0 (.const 0))

theorem resetLoop_secure : CmdSecure policy false resetLoop :=
  .loop (l := false) (.not (.eq (.var (by simp [policy])) (.const _ _)))
    (.assign (by simp [policy]) (.const _ _))

/-- This loop actually iterates; the theorem is not restricted to skip loops. -/
example : BigStep resetLoop (fun _ => 1) (Function.update (fun _ => 1) 0 0) :=
  .whileTrue (by simp [nonzero, BExp.eval]) (.assign _ _ _)
    (.whileFalse (by simp [nonzero, BExp.eval]))

example {s s' t t' : Store} (h : LowEquiv policy s t)
    (hs : BigStep resetLoop s s') (ht : BigStep resetLoop t t') : LowEquiv policy s' t' :=
  termination_insensitive_noninterference resetLoop_secure h hs ht

/-- Dropping expression security admits direct secret-to-public copying. -/
def directLeak : Cmd := .assign 0 (.var 1)

theorem directLeak_untypable : ¬ CmdSecure policy false directLeak := by
  intro h
  cases h with
  | assign _ he =>
    cases he with
    | var h => exact Bool.noConfusion (h rfl)

theorem directLeak_counterexample : ∃ s' t', BigStep directLeak zero s' ∧
    BigStep directLeak secretOne t' ∧ ¬ LowEquiv policy s' t' := by
  refine ⟨_, _, .assign _ _ _, .assign _ _ _, ?_⟩
  intro h
  have := h 0 (by simp [policy])
  simp [zero, secretOne] at this

/-- Dropping the pc restriction admits an implicit flow even with constant RHSs. -/
def implicitLeak : Cmd :=
  .ite (nonzero (.var 1)) (.assign 0 (.const 1)) (.assign 0 (.const 0))

theorem implicitLeak_untypable : ¬ CmdSecure policy false implicitLeak := by
  intro h
  cases h with
  | ite he ha _ =>
    cases he with
    | not he =>
      cases he with
      | eq he _ =>
        cases he with
        | var hlevel =>
          cases ha with
          | assign hpc _ =>
            have : true ≤ false := le_trans (by simpa [policy] using hlevel) hpc
            exact Bool.noConfusion (this rfl)

theorem implicitLeak_counterexample : ∃ s' t', BigStep implicitLeak zero s' ∧
    BigStep implicitLeak secretOne t' ∧ ¬ LowEquiv policy s' t' := by
  refine ⟨_, _, .iteFalse (by simp [nonzero, BExp.eval, zero]) (.assign _ _ _),
    .iteTrue (by simp [nonzero, BExp.eval, secretOne]) (.assign _ _ _), ?_⟩
  intro h
  have := h 0 (by simp [policy])
  simp at this

/-- Initial low equivalence is essential even for skip. -/
example : ¬ LowEquiv policy zero (fun _ => 1) := by
  intro h
  exact Nat.zero_ne_one (h 0 (by simp [policy]))

/-- This secure program exposes a termination channel, outside the theorem's scope. -/
def secretLoop : Cmd := .while (nonzero (.var 1)) .skip

theorem secretLoop_secure : CmdSecure policy false secretLoop :=
  .loop (l := true) (.not (.eq (.var (by simp [policy])) (.const _ _))) (.skip _)

theorem secretLoop_zero : BigStep secretLoop zero zero :=
  .whileFalse (by simp [nonzero, BExp.eval, zero])

/-- A nonzero secret is unchanged by the body, so this run cannot terminate. -/
theorem secretLoop_nonterminating : ¬ ∃ t, BigStep secretLoop secretOne t := by
  rintro ⟨t, ht⟩
  have aux : ∀ {c s t}, BigStep c s t → c = secretLoop → s 1 = 1 → False := by
    intro c s t h
    induction h with
    | skip => intro hc; cases hc
    | assign => intro hc; cases hc
    | seq => intro hc; cases hc
    | iteTrue => intro hc; cases hc
    | iteFalse => intro hc; cases hc
    | whileFalse he =>
      intro hc hs
      cases hc
      simp [nonzero, BExp.eval, hs] at he
    | whileTrue he hb hl ihb ihl =>
      intro hc hs
      cases hc
      cases hb
      exact ihl rfl hs
  exact aux ht rfl (by simp [secretOne])

#print axioms termination_insensitive_noninterference
#print axioms IMP.BigStep.deterministic
#print axioms BigStepConfinement

end Cslib.Security.Noninterference.Tests
