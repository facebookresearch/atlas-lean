/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.OperationalSemantics
public import CSLibExt.Languages.IMP.SmallStep
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Semantics
import Mathlib.Logic.Function.Basic

/-! Tests for the operational-semantics anchor, following Peter Sewell,
Semantics of Programming Languages (Cambridge CST Part IB 2025-26). Model
boundaries: toy checks stuck/safe/determinacy edges, IMP and STLC are consumed
through the anchor only; no progress or preservation claim is tested. -/

@[expose] public section

set_option autoImplicit false

universe u v

open Cslib.Languages.LambdaCalculus
open scoped CslibStlc

namespace Cslib.Languages.OperationalSemanticsTests

/-- Toy configuration with three states for boundary tests. -/
inductive ToyCfg where
  | start : ToyCfg
  | blocked : ToyCfg
  | done : ToyCfg

/-- Toy semantics with the single transition `start` to `blocked`; final only
at `done`. -/
def toy : Cslib.Languages.OperationalSemantics.OpSem ToyCfg Unit where
  lts := { Tr := fun x _ y => x = .start ∧ y = .blocked }
  Final := fun c => c = .done
  final_terminal := by
    intro c hc μ s' h
    cases c <;> simp_all

/-- The toy transition pins `start` to `blocked`. -/
theorem toy_step_start_blocked :
    toy.Step ToyCfg.start ToyCfg.blocked := by
  exact ⟨(), rfl, rfl⟩

/-- `blocked` is stuck. -/
theorem toy_blocked_stuck : toy.Stuck ToyCfg.blocked := by
  apply (Cslib.Languages.OperationalSemantics.OpSem.stuck_iff toy).mpr
  show ¬ (ToyCfg.blocked = ToyCfg.done) ∧ ∀ (μ : Unit) (s' : ToyCfg),
    ¬ (ToyCfg.blocked = ToyCfg.start ∧ s' = ToyCfg.blocked)
  constructor
  · exact fun h => ToyCfg.noConfusion h
  · intro μ s' h
    exact ToyCfg.noConfusion h.1

/-- `start` is not safe; intended witness is `blocked` via the step. -/
theorem toy_not_safe_start : ¬ toy.Safe ToyCfg.start := by
  intro hsafe
  have hsteps : toy.Steps ToyCfg.start ToyCfg.blocked :=
    (Cslib.Languages.OperationalSemantics.OpSem.steps_iff_reflTransGen toy).mpr
      (Relation.ReflTransGen.head toy_step_start_blocked Relation.ReflTransGen.refl)
  exact hsafe _ hsteps toy_blocked_stuck

/-- `done` is final, so its terminality and safety hold by finality through
`final_terminal`, not by a self-loop. -/
theorem toy_done_final : toy.Final ToyCfg.done := by
  exact rfl

/-- `done` is safe. -/
theorem toy_safe_done : toy.Safe ToyCfg.done := by
  intro d hsteps hstuck
  obtain ⟨hnf, _⟩ := (Cslib.Languages.OperationalSemantics.OpSem.stuck_iff toy).mp hstuck
  have hrt : Relation.ReflTransGen toy.Step ToyCfg.done d :=
    (Cslib.Languages.OperationalSemantics.OpSem.steps_iff_reflTransGen toy).mp hsteps
  rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c, hstep, _⟩
  · exact hnf toy_done_final
  · have hterm : toy.lts.IsTerminal ToyCfg.done := toy.final_terminal toy_done_final
    obtain ⟨μ, htr⟩ := hstep
    exact hterm μ c htr

/-- The toy is deterministic. -/
theorem toy_deterministic : toy.Deterministic := by
  intro x y z h1 h2
  obtain ⟨_, h1⟩ := h1
  obtain ⟨_, h2⟩ := h2
  have hy : y = ToyCfg.blocked := (show x = ToyCfg.start ∧ y = ToyCfg.blocked from h1).2
  have hz : z = ToyCfg.blocked := (show x = ToyCfg.start ∧ z = ToyCfg.blocked from h2).2
  exact hy.trans hz.symm

/-- Reachable states from `start` are `start` or `blocked`. -/
theorem toy_steps_cases : ∀ {d : ToyCfg},
    toy.Steps ToyCfg.start d → d = ToyCfg.start ∨ d = ToyCfg.blocked := by
  intro d hsteps
  have hrt : Relation.ReflTransGen toy.Step ToyCfg.start d :=
    (Cslib.Languages.OperationalSemantics.OpSem.steps_iff_reflTransGen toy).mp hsteps
  rcases Relation.ReflTransGen.cases_head hrt with h | ⟨c, hstep, hrt2⟩
  · exact Or.inl h.symm
  · obtain ⟨_, htr⟩ := hstep
    have hs : ToyCfg.start = ToyCfg.start ∧ c = ToyCfg.blocked := htr
    have hc : c = ToyCfg.blocked := hs.2
    subst hc
    rcases Relation.ReflTransGen.cases_head hrt2 with h2 | ⟨c2, hstep2, _⟩
    · exact Or.inr h2.symm
    · obtain ⟨_, htr2⟩ := hstep2
      have hs2 : ToyCfg.blocked = ToyCfg.start ∧ c2 = ToyCfg.blocked := htr2
      exact False.elim (ToyCfg.noConfusion hs2.1)

/-- No final configuration is reachable from `start`. This separates uniqueness
(M2) from final existence; it does not by itself separate M1 from normal-form
existence, since `blocked` is a reachable terminal configuration. -/
theorem toy_no_final_reachable :
    ¬ ∃ d : ToyCfg, toy.Steps ToyCfg.start d ∧ toy.Final d := by
  rintro ⟨d, hsteps, hfinal⟩
  rcases toy_steps_cases hsteps with rfl | rfl
  · exact ToyCfg.noConfusion (show ToyCfg.start = ToyCfg.done from hfinal)
  · exact ToyCfg.noConfusion (show ToyCfg.blocked = ToyCfg.done from hfinal)

/-- Initial IMP state mapping every location to zero. -/
def s0 : Cslib.IMP.State := fun _ => 0

/-- IMP start configuration assigning `2` to location `0`. -/
def c0 : Cslib.IMP.Config := (.assign 0 (.const 2), s0)

/-- The assignment steps through the anchor to skip with updated state. -/
theorem imp_assign_anchor_step :
    Cslib.Languages.OperationalSemantics.imp.Step c0
      (Cslib.IMP.Cmd.skip, Function.update s0 0 2) := by
  apply Cslib.Languages.OperationalSemantics.imp_step_iff.mpr
  have h := Cslib.IMP.Step.assign s0 0 (Cslib.IMP.AExp.const 2)
  simpa [c0, Cslib.IMP.AExp.eval_const] using h

/-- The updated state maps `0` to `2`. -/
theorem imp_assign_state_zero : (Function.update s0 0 2) 0 = 2 := by
  exact Function.update_self 0 2 s0

/-- The assignment target is final. -/
theorem imp_assign_final :
    Cslib.Languages.OperationalSemantics.imp.Final
      (Cslib.IMP.Cmd.skip, Function.update s0 0 2) := by
  exact rfl

/-- The assignment start configuration is safe. -/
theorem imp_assign_safe :
    Cslib.Languages.OperationalSemantics.imp.Safe c0 := by
  exact Cslib.Languages.OperationalSemantics.imp_safe c0

/-- Base type atom for the STLC fibre. -/
def b : Stlc.Ty Unit := Stlc.Ty.base ()

/-- Identity at `b`. -/
def idT : Stlc.Tm ([] : List (Stlc.Ty Unit)) (b ⇒ b) := .lam (.var .zero)

/-- Redex applying the identity combinator to `idT`. -/
def r : Stlc.Tm ([] : List (Stlc.Ty Unit)) (b ⇒ b) :=
  .app (.lam (.var .zero)) idT

/-- Anchor instance for the `b ⇒ b` fibre. -/
def S : Cslib.Languages.OperationalSemantics.OpSem
    (Stlc.Tm ([] : List (Stlc.Ty Unit)) (b ⇒ b)) Unit :=
  Cslib.Languages.OperationalSemantics.stlc (Base := Unit) (A := b ⇒ b)

/-- The identity is final. -/
theorem stlc_id_final : S.Final idT := by
  exact Stlc.Value.lam _

/-- The redex steps to the instantiated body. -/
theorem stlc_beta_step :
    S.Step r (Stlc.Tm.instantiate (.var .zero) idT) := by
  apply Cslib.Languages.OperationalSemantics.stlc_step_iff.mpr
  exact Stlc.Step.beta (show Stlc.Value idT from stlc_id_final)

/-- Instantiation computes to the identity. -/
theorem stlc_beta_result :
    Stlc.Tm.instantiate (.var .zero) idT = idT := by
  unfold Stlc.Tm.instantiate
  rw [Stlc.Tm.subst_var, Stlc.Sub.single_zero]

/-- The instantiation result is final. -/
theorem stlc_beta_result_final :
    S.Final (Stlc.Tm.instantiate (.var .zero) idT) := by
  rw [stlc_beta_result]
  exact stlc_id_final

end Cslib.Languages.OperationalSemanticsTests
