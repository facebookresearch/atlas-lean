/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.SessionTypes.Endpoint.RankedConversionGlobal

/-!
# Sequential central actor branching and completed interfaces

The central actor owns TWO different active channels and sends first at rank2,
then at rank4. This is not two independent pair components relabeled connected.
-/

namespace Cslib.SessionTypes.Endpoint.RankedConversionBranchingTests

open PiCalculus

def a : Key := ⟨.var 0, .positive⟩
def b : Key := ⟨.var 1, .positive⟩
def c₂ : Capability := ⟨2, .sendName .done⟩
def c₄ : Capability := ⟨4, .sendName .done⟩
def actorCtx : Context := (Finmap.singleton a c₂).insert b c₄
def leftCtx : Context := Finmap.singleton a.opposite c₂.dual
def rightCtx : Context := Finmap.singleton b.opposite c₄.dual
def world : Context := actorCtx ∪ (leftCtx ∪ rightCtx)
def actor : Proc := .out a.name (.const 500) (.out b.name (.const 600) .nil)
def left : Proc := .inp a.name .nil
def right : Proc := .inp b.name .nil
def network : Proc := .par actor (.par left right)

/-- First central guard compares its OTHER active owned channel explicitly. -/
theorem central_guard : GuardMin actorCtx a 2 := by
  intro x c hx ha hn
  rcases Finmap.mem_insert.mp (Finmap.mem_of_lookup_eq_some hx) with he | he
  · subst x
    rw [actorCtx, Finmap.lookup_insert] at hx
    cases hx
    exact (by decide : 2 < 4)
  · exact False.elim (hn ((Finmap.mem_singleton _ _ _).mp he))

/-- The second action ignores only the ACTUALLY completed first role. -/
theorem central_second : Conversion.RankedType 2 (actorCtx.insert a ⟨2, .done⟩)
    (.out b.name (.const 600) .nil) := by
  rw [actorCtx, Finmap.insert_insert_of_ne (s := (Finmap.singleton a c₂ : Context))
    (a := b) (a' := a) (by simp [a, b]), Finmap.insert_singleton_eq]
  apply Conversion.RankedType.outName (e := b) (c := c₄) (s := .done)
  · intro x c hx ha hn
    rw [Finmap.lookup_insert_of_ne _ hn] at hx
    have he := (Finmap.mem_singleton _ _ _).mp (Finmap.mem_of_lookup_eq_some hx)
    subst x
    rw [Finmap.lookup_singleton_eq] at hx
    cases hx
    exact False.elim (ha rfl)
  · exact Finmap.lookup_insert _
  · rfl
  · change 1 < 2
    decide
  · trivial
  · rw [Finmap.insert_insert]
    have ht : Conversion.RankedType 2 (Finmap.singleton a (⟨2, .done⟩ : Capability)) .nil :=
      Conversion.RankedType.nil_of_hasType (Conversion.HasType.of_raw
        (Endpoint.HasType.nil_singleton_completed (Nat.zero_lt_succ 1) rfl))
    exact ht.weaken_completed (by simp [a, b, Finmap.mem_singleton]) rfl (by change 1 < 2; decide)

/-- A genuinely sequential two-channel central actor satisfies the static discipline. -/
theorem actor_ranked : Conversion.RankedType 2 actorCtx actor := by
  apply Conversion.RankedType.outName (e := a) (c := c₂) (s := .done) central_guard
  · simp [actorCtx, a, b]
  · rfl
  · exact Nat.zero_lt_succ 1
  · trivial
  · exact central_second

/-- Both receiver leaves use their actual singleton guards and scoped nil bodies. -/
theorem left_ranked : Conversion.RankedType 2 leftCtx left := by
  apply Conversion.RankedType.inpName (e := a.opposite) (c := c₂.dual) (s := .done)
    (guardMin_singleton _ _)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · exact Nat.zero_lt_succ 1
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact Conversion.RankedType.nil_of_hasType (Conversion.HasType.of_raw
      (Endpoint.HasType.nil_singleton_completed (by change 1 < 3; decide) rfl))

theorem right_ranked : Conversion.RankedType 2 rightCtx right := by
  apply Conversion.RankedType.inpName (e := b.opposite) (c := c₄.dual) (s := .done)
    (guardMin_singleton _ _)
  · exact Finmap.lookup_singleton_eq
  · rfl
  · change 1 < 2
    decide
  · rw [Finmap.insert_singleton_eq, Context.lift_singleton]
    exact Conversion.RankedType.nil_of_hasType (Conversion.HasType.of_raw
      (Endpoint.HasType.nil_singleton_completed (by change 2 < 3; decide) rfl))

/-- Actual three-component disjoint typing, with two channels at the central leaf. -/
theorem network_ranked : Conversion.RankedType 2 world network := by
  apply Conversion.RankedType.par
  · simp [actorCtx, leftCtx, rightCtx, a, b, Key.opposite, Role.opposite,
      Finmap.Disjoint, Finmap.mem_singleton]
  · exact actor_ranked
  · apply Conversion.RankedType.par
    · simp [leftCtx, rightCtx, a, b, Key.opposite, Finmap.Disjoint, Finmap.mem_singleton]
    · exact left_ranked
    · exact right_ranked

def privateCtx : Context := Context.bind c₂ (Context.bind c₄ ∅)

private theorem lookup_singleton_ne (a x : Key) (c : Capability) (h : x ≠ a) :
    (Finmap.singleton a c : Context).lookup x = none :=
  Finmap.lookup_eq_none.mpr (by simpa using h)

attribute [local simp] lookup_singleton_ne Finmap.lookup_singleton_eq

/-- The four-role interface is the same actual literal-dual private pair tower. -/
theorem world_equivalent : ContextEquivalent world privateCtx := by
  intro x
  by_cases h₀ : x = ⟨.var 0, .positive⟩ <;>
    by_cases h₁ : x = ⟨.var 0, .negative⟩ <;>
    by_cases h₂ : x = ⟨.var 1, .positive⟩ <;>
    by_cases h₃ : x = ⟨.var 1, .negative⟩
  all_goals subst_vars
  all_goals
    rw [privateCtx, Context.bind_empty, Context.bind, Context.lift_union,
      Context.lift_singleton, Context.lift_singleton] <;>
      try simp [Finmap.Disjoint, Finmap.mem_singleton]
  all_goals
    simp_all [world, actorCtx, leftCtx, rightCtx, a, b, Key.mapName, liftName,
      Key.opposite, Role.opposite, Finmap.mem_singleton, Finmap.lookup_union_right]
  all_goals exact Capability.Equivalent.refl _

/-- Semantic balance is derived from the actual four-role pair interface. -/
theorem world_balanced : Conversion.Balanced world :=
  ((Conversion.balanced_empty.bind c₄).bind c₂).retype world_equivalent.symm

/-- GENERAL global progress admits the truly sequential central actor. -/
theorem central_global : Cong network .nil ∨ ∃ q, PiCalculus.Step network q :=
  network_ranked.progress_balanced world_balanced

/-- Real private closure uses the new retyping and both actual restriction rules. -/
theorem closed_ranked : Conversion.RankedType 0 ∅ (.nu (.nu network)) :=
  Conversion.RankedType.nu (Conversion.RankedType.nu (network_ranked.retype world_equivalent))

/-- Global empty progress derives its own restriction/frontier normalization. -/
theorem closed_central_global : Cong (.nu (.nu network)) .nil ∨
    ∃ q, PiCalculus.Step (.nu (.nu network)) q := closed_ranked.progress_empty

def afterFirst : Proc := .par (.out b.name (.const 600) .nil) (.par .nil right)

/-- Actual first central communication retains the remaining central action. -/
theorem first_step : PiCalculus.Step network afterFirst :=
  PiCalculus.Step.cong (Cong.symm (Cong.par_assoc _ _ _))
    (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
    (Cong.par_assoc _ _ _)

/-- Reachable central progress uses actual ranked preservation before the theorem. -/
theorem central_reachable_progress : Cong (.nu (.nu afterFirst)) .nil ∨
    ∃ q, PiCalculus.Step (.nu (.nu afterFirst)) q :=
  closed_ranked.reachable_progress (Relation.ReflTransGen.refl.tail
    (PiCalculus.Step.nu (PiCalculus.Step.nu first_step)))

/-- The SAME central actor performs its second channel communication next. -/
theorem second_step : PiCalculus.Step afterFirst (.par .nil (.par .nil .nil)) :=
  PiCalculus.Step.cong (Cong.par_cong (Cong.refl _) (Cong.par_comm .nil right))
    (PiCalculus.Step.cong (Cong.symm (Cong.par_assoc _ _ _))
      (PiCalculus.Step.parL (PiCalculus.Step.commSelect (Select.refl _) (Select.refl _)))
      (Cong.par_assoc _ _ _)) (Cong.refl _)

end Cslib.SessionTypes.Endpoint.RankedConversionBranchingTests
