/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Cslib.Foundations.Semantics.LTS.Termination
public import Cslib.Foundations.Data.OmegaSequence.Defs
public import CSLibExt.Languages.IMP.SmallStep
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Semantics
import Mathlib.Logic.Relation

/-! Operational-semantics anchor over the pinned CSLib labelled-transition
system interface, following Peter Sewell, Semantics of Programming Languages
(Cambridge CST Part IB 2025-26). Model boundaries: unlabelled determinacy as
successor uniqueness, divergence as arbitrary-label infinite execution, final
implies terminal as a hypothesis, uniqueness as at most one reachable normal
form; no progress or preservation claim for either instance language. -/

@[expose] public section

set_option autoImplicit false

universe u v

open Cslib.Languages.LambdaCalculus

namespace Cslib.Languages.OperationalSemantics

/-- An operational semantics: a labelled transition system with a value/final predicate.
`Final` is the language's value/final predicate and is not defined as terminality; the
`final_terminal` field records that every final configuration is terminal. -/
structure OpSem (Config : Type u) (Label : Type v) where
  /-- Underlying labelled transition system. -/
  lts : Cslib.LTS Config Label
  /-- Value/final predicate, not defined as terminality. -/
  Final : Config → Prop
  /-- Every final configuration is terminal. -/
  final_terminal : ∀ {c : Config}, Final c → lts.IsTerminal c

namespace OpSem

/-- Unlabelled one-step relation, forgetting labels. -/
def Step {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) : Config → Config → Prop :=
  S.lts.UnlabelledTr

/-- Finite reachability: some finite label trace `μs` leads from `x` to `y`
(`S.lts.MTr x μs y`). -/
def Steps {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) (x y : Config) : Prop :=
  ∃ μs, S.lts.MTr x μs y

/-- Stuck configurations: non-final with no outgoing transition. -/
def Stuck {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) (c : Config) : Prop :=
  S.lts.Stuck S.Final c

/-- Stuck unfolds to non-final plus terminal. -/
theorem stuck_iff {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) {c : Config} :
    S.Stuck c ↔ ¬ S.Final c ∧ S.lts.IsTerminal c := by
  unfold OpSem.Stuck Cslib.LTS.Stuck Cslib.LTS.IsTerminal
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun μ s' h => h2 ⟨μ, s', h⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨μ, s', h⟩ => h2 μ s' h⟩

/-- Safety: no reachable configuration is stuck. -/
def Safe {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) (c : Config) : Prop :=
  ∀ d : Config, S.Steps c d → ¬ S.Stuck d

/-- Divergence: arbitrary-label infinite execution from `c`. -/
def Diverges {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) (c : Config) : Prop :=
  ∃ (ss : Cslib.ωSequence Config) (μs : Cslib.ωSequence Label),
    ss 0 = c ∧ S.lts.OmegaExecution ss μs

/-- Unlabelled determinacy as successor uniqueness, distinct from per-label
`LTS.Deterministic` when several labels can leave one state. -/
def Deterministic {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) : Prop :=
  ∀ {x y z : Config}, S.Step x y → S.Step x z → y = z

/-- Finite bridge: multistep reachability is the reflexive-transitive closure
of the unlabelled step. -/
theorem steps_iff_reflTransGen {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) {x y : Config} :
    S.Steps x y ↔ Relation.ReflTransGen S.Step x y := by
  constructor
  · rintro ⟨μs, hm⟩
    induction hm with
    | refl => exact Relation.ReflTransGen.refl
    | stepL htr _ ih =>
      exact Relation.ReflTransGen.head (show S.Step _ _ from ⟨_, htr⟩) ih
  · intro h
    induction h with
    | refl => exact ⟨[], Cslib.LTS.MTr.refl⟩
    | tail _ hstep ih =>
      obtain ⟨μs, hm⟩ := ih
      obtain ⟨μ, htr⟩ := hstep
      exact ⟨μs ++ [μ], Cslib.LTS.MTr.comp S.lts hm (Cslib.LTS.MTr.single S.lts htr)⟩

/-- Infinite bridge: divergence is an unlabelled infinite step sequence. The
recovered label stream is not a claim about any particular action or fairness
trace. -/
theorem diverges_iff {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) {c : Config} :
    S.Diverges c ↔
      ∃ f : Nat → Config, f 0 = c ∧ ∀ i : Nat, S.Step (f i) (f (i + 1)) := by
  constructor
  · rintro ⟨ss, μs, h0, hexec⟩
    exact ⟨fun i => ss i, h0, fun i => ⟨μs i, hexec i⟩⟩
  · rintro ⟨f, h0, hstep⟩
    have h : ∀ i, ∃ μ, S.lts.Tr (f i) μ (f (i + 1)) := hstep
    obtain ⟨g, hg⟩ := Classical.skolem.mp h
    exact ⟨⟨f⟩, ⟨g⟩, h0, hg⟩

/-- Unique normal form: at most one reachable terminal configuration. -/
theorem eq_of_steps_of_terminal {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) {x y z : Config}
    (hdet : S.Deterministic) (hxy : S.Steps x y) (hxz : S.Steps x z)
    (hy : S.lts.IsTerminal y) (hz : S.lts.IsTerminal z) : y = z := by
  obtain ⟨μs1, hm1⟩ := hxy
  revert hxz hz
  induction hm1 with
  | refl =>
    rintro ⟨μs2, hm2⟩ hz
    cases hm2 with
    | refl => rfl
    | stepL htr _ => exact False.elim (hy _ _ htr)
  | stepL htr1 _ ih =>
    rintro ⟨μs2, hm2⟩ hz
    cases hm2 with
    | refl => exact False.elim (hz _ _ htr1)
    | stepL htr2 hm2' =>
      have heq := hdet (show S.Step _ _ from ⟨_, htr1⟩) (show S.Step _ _ from ⟨_, htr2⟩)
      subst heq
      exact ih hy ⟨_, hm2'⟩ hz

/-- Unique final configuration: at most one reachable final configuration,
derived from the terminal case and `final_terminal`. -/
theorem eq_of_steps_of_final {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) {x y z : Config}
    (hdet : S.Deterministic) (hxy : S.Steps x y) (hxz : S.Steps x z)
    (hy : S.Final y) (hz : S.Final z) : y = z := by
  exact OpSem.eq_of_steps_of_terminal S hdet hxy hxz (S.final_terminal hy) (S.final_terminal hz)

end OpSem

/-- IMP adapter with unit labels; steps are exactly `Cslib.IMP.Step`, and a configuration is
final iff its command is `skip`. -/
def imp : OpSem Cslib.IMP.Config Unit where
  lts := { Tr := fun x _ y => Cslib.IMP.Step x y }
  Final := fun c => c.1 = Cslib.IMP.Cmd.skip
  final_terminal := by
    intro c hc μ s' h
    obtain ⟨cmd, state⟩ := c
    simp at hc
    subst hc
    exact Cslib.IMP.Step.skip_not_step h

/-- IMP unlabelled steps coincide with native steps. -/
theorem imp_step_iff {x y : Cslib.IMP.Config} :
    OpSem.Step imp x y ↔ Cslib.IMP.Step x y := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨(), h⟩

/-- IMP reachability coincides with native reflexive-transitive closure. -/
theorem imp_steps_iff {x y : Cslib.IMP.Config} :
    OpSem.Steps imp x y ↔ Cslib.IMP.Steps x y := by
  rw [OpSem.steps_iff_reflTransGen imp]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (imp_step_iff.mp hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (imp_step_iff.mpr hstep)

/-- IMP is deterministically unlabelled. -/
theorem imp_deterministic : OpSem.Deterministic imp := by
  intro x y z h1 h2
  exact Cslib.IMP.Step.deterministic (imp_step_iff.mp h1) (imp_step_iff.mp h2)

/-- Every IMP configuration is safe. -/
theorem imp_safe (c : Cslib.IMP.Config) : OpSem.Safe imp c := by
  intro d _ hstuck
  obtain ⟨hnf, hterm⟩ := (OpSem.stuck_iff imp).mp hstuck
  obtain ⟨cmd, state⟩ := d
  have hne : cmd ≠ Cslib.IMP.Cmd.skip := hnf
  obtain ⟨next, hstep⟩ := Cslib.IMP.Step.exists_step hne
  exact hterm () next hstep

/-- Closed simply typed terms of type `A` as an operational semantics with unit labels: its
steps are exactly the call-by-value steps `Stlc.Step`, and its final configurations are the
values `Stlc.Value`. -/
def stlc {Base : Type u} {A : Stlc.Ty Base} :
    OpSem (Stlc.Tm ([] : List (Stlc.Ty Base)) A) Unit where
  lts := { Tr := fun x _ y => Stlc.Step x y }
  Final := Stlc.Value
  final_terminal := by
    intro c hv μ s' h
    exact Stlc.Step.value_irreducible hv h

/-- For closed STLC terms of one type, an unlabelled step of the adapter is exactly a native
call-by-value step. -/
theorem stlc_step_iff {Base : Type u} {A : Stlc.Ty Base}
    {x y : Stlc.Tm ([] : List (Stlc.Ty Base)) A} :
    OpSem.Step stlc x y ↔ Stlc.Step x y := by
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨(), h⟩

/-- The STLC adapter on closed terms of one type is deterministic: two unlabelled successors
of the same closed term are equal. -/
theorem stlc_deterministic {Base : Type u} {A : Stlc.Ty Base} :
    OpSem.Deterministic (stlc (Base := Base) (A := A)) := by
  intro x y z h1 h2
  exact Stlc.Step.deterministic (stlc_step_iff.mp h1) (stlc_step_iff.mp h2)

end Cslib.Languages.OperationalSemantics
