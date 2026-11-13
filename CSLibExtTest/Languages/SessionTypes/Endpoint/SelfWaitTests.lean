/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.Typing
import CSLibExt.Languages.SessionTypes.Endpoint.ContextAlgebra
import CSLibExt.Languages.SessionTypes.Endpoint.Balance
import CSLibExt.Languages.SessionTypes.Endpoint.Priority
import CSLibExt.Languages.SessionTypes.Endpoint.RankedTyping
import CSLibExt.Languages.SessionTypes.Endpoint.FrontierProgress
import CSLibExt.Languages.SessionTypes.Endpoint.InputInvariant
import CSLibExt.Languages.PiCalculus.Behavioural

/-!
# Opposite-role self-wait on one physical channel

A physical-name-only dependency exemption would miss this configuration.
-/

namespace Cslib.SessionTypes.Endpoint.SelfWaitTests

open PiCalculus

private def positive : Key := ⟨.const 0, .positive⟩
private def negative : Key := ⟨.const 0, .negative⟩
private def done : Capability := ⟨0, .done⟩
private def ending : Context := ((∅ : Context).insert positive done).insert negative done

private theorem nil_ending (n : Nat) : HasType n ending .nil := by
  apply HasType.nil
  · exact (Context.completed_empty.insert (e := positive) rfl).insert (e := negative) rfl
  · intro e he
    rcases Finmap.mem_insert.mp he with he | he
    · subst e
      trivial
    · rcases Finmap.mem_insert.mp he with he | he
      · subst e
        trivial
      · exact False.elim (Finmap.notMem_empty he)

private def sending : Capability := ⟨0, .sendName .done⟩

/-- A single owner holds both active roles on physical channel zero. -/
def waiting : Context := ((∅ : Context).insert positive sending).insert negative sending.dual

/-- It waits for its own later output, which cannot run through the input guard. -/
def selfWait : Proc := .inp (.const 0) (.out (.const 0) (.const 7) .nil)

/-- Bare linear typing permits the self-wait; progress needs the discipline. -/
theorem selfWait_typed : HasType 0 waiting selfWait := by
  unfold waiting selfWait
  apply HasType.inpName (e := negative) (c := sending.dual) (s := .done)
  · simp
  · rfl
  · trivial
  · rw [Finmap.insert_insert, Context.lift_insert, Context.lift_insert, Context.lift_empty]
    change HasType 1 (((∅ : Context).insert positive sending).insert negative done)
      (.out (.const 0) (.const 7) .nil)
    apply HasType.outName (e := positive) (c := sending) (s := .done)
    · rw [Finmap.lookup_insert_of_ne _ (by decide)]
      simp
    · rfl
    · trivial
    · trivial
    · rw [Finmap.insert_insert_of_ne (s := (∅ : Context).insert positive sending)
        (a := negative) (a' := positive) (by decide), Finmap.insert_insert]
      exact nil_ending 1

/-- This input-guarded self-wait has no π step, even through all Cong laws. -/
theorem selfWait_no_step (q : Proc) : ¬ PiCalculus.Step selfWait q := by
  apply not_step_of_no_output
  simp [selfWait, HasUnguardedOutput]

/-- The peer role is a dependency even though the physical name coincides. -/
theorem selfWait_priority_rejected : ¬ GuardMin waiting negative 0 := by
  apply guardMin_rejects_peer (e := negative) (c := sending)
  · simp [waiting, positive, negative, Key.opposite, Role.opposite]
  · simp [sending, Protocol.unfold]

/-- The self-wait has dual protocols and equal ranks on its two roles. -/
theorem selfWait_balanced : Balanced waiting := by
  intro e c hc
  by_cases hn : e = negative
  · subst e
    simp only [waiting, Finmap.lookup_insert, Option.some.injEq] at hc
    subst c
    simp [waiting, negative, positive, Key.opposite, Role.opposite]
  · rw [waiting, Finmap.lookup_insert_of_ne _ hn] at hc
    by_cases hp : e = positive
    · subst e
      simp only [Finmap.lookup_insert, Option.some.injEq] at hc
      subst c
      simp [waiting, negative, positive, Key.opposite, Role.opposite]
    · rw [Finmap.lookup_insert_of_ne _ hp] at hc
      simp at hc

/-- The whole refinement rejects the bare-typed balanced self-wait,
regardless of which same-name role an attempted input derivation chooses. -/
theorem selfWait_ranked_rejected : ¬ RankedType 0 waiting selfWait := by
  intro h
  obtain ⟨e, c, he, hc, hg⟩ := h.inp_guard
  cases e with
  | mk a r =>
    change a = .const 0 at he
    subst a
    cases r with
    | positive =>
      have hu : c = sending := Context.unique hc (by
        simp [waiting, positive, negative, Finmap.lookup_insert_of_ne])
      subst c
      have hl := hg negative sending.dual (by simp [waiting])
        (by change Protocol.recvName .done ≠ .done; intro heq; cases heq) (by decide)
      exact (Nat.lt_irrefl 0) hl
    | negative =>
      have hu : c = sending.dual := Context.unique hc (by simp [waiting, negative])
      subst c
      exact selfWait_priority_rejected hg

/-- GENERAL frontier progress rejects this sequential same-name self-wait
for arbitrary balanced ownership and ambient depth, not only the chosen fixture. -/
theorem selfWait_any_balanced_refinement_rejected {n : Nat} {Δ : Context} (hb : Balanced Δ) :
    ¬ RankedType n Δ selfWait := by
  intro ht
  rcases (GuardFrontier.inp _ _).progress ht hb with hc | ⟨q, hs⟩
  · have hin : HasUnguardedInput selfWait := trivial
    exact (input_cong hc).mp hin
  · exact selfWait_no_step q hs

end Cslib.SessionTypes.Endpoint.SelfWaitTests
