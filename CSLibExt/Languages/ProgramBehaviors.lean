/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.OperationalSemantics

/-!
Program behaviors and homogeneous semantic preservation after Leroy's
"Formal verification of a realistic compiler" (§2.1), over the operational-semantics anchor.
A behavior is observational: termination or going wrong after a finite label trace, or
reaction with an infinite label trace. Final and stuck configurations stay existential in
`Beh`; every anchor label counts as an observable event, and results are observed only as labels.
Excluded: Leroy's silent divergence (a finite observable trace followed by silent infinite
execution) and any tau companion (the anchor has no tau), cross-language preservation with a label
map, and any soundness claim about a compiler.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Languages.ProgramBehaviors

open Cslib.Languages.OperationalSemantics

/-- Observable program behaviors over label traces: termination, reaction, or going wrong. -/
inductive Behavior (Label : Type v) where
  | terminates (trace : List Label)
  | reacts (trace : Cslib.ωSequence Label)
  | goesWrong (trace : List Label)

/-- The behaviors of `c`: `terminates μs` when an execution from `c` with trace `μs` reaches a
final configuration, `reacts μs` when an infinite execution from `c` has labels `μs`, and
`goesWrong μs` when an execution from `c` with trace `μs` reaches a stuck configuration. -/
def Beh {Config : Type u} {Label : Type v} (S : OpSem Config Label) (c : Config) :
    Set (Behavior Label) :=
  {b | match b with
    | .terminates μs => ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Final c'
    | .reacts μs => ∃ ss : Cslib.ωSequence Config, ss 0 = c ∧ S.lts.OmegaExecution ss μs
    | .goesWrong μs => ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Stuck c'}

/-- `terminates μs` is a behavior of `c` iff an execution from `c` with trace exactly `μs`
reaches a final configuration. -/
theorem terminates_mem_iff {Config : Type u} {Label : Type v} (S : OpSem Config Label)
    {c : Config} {μs : List Label} :
    Behavior.terminates μs ∈ Beh S c ↔ ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Final c' := by
  exact Iff.rfl

/-- `reacts μs` is a behavior of `c` iff an infinite execution starting at `c` has labels
exactly `μs`. -/
theorem reacts_mem_iff {Config : Type u} {Label : Type v} (S : OpSem Config Label)
    {c : Config} {μs : Cslib.ωSequence Label} :
    Behavior.reacts μs ∈ Beh S c ↔
      ∃ ss : Cslib.ωSequence Config, ss 0 = c ∧ S.lts.OmegaExecution ss μs := by
  exact Iff.rfl

/-- `goesWrong μs` is a behavior of `c` iff an execution from `c` with trace exactly `μs`
reaches a stuck configuration. -/
theorem goesWrong_mem_iff {Config : Type u} {Label : Type v} (S : OpSem Config Label)
    {c : Config} {μs : List Label} :
    Behavior.goesWrong μs ∈ Beh S c ↔ ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Stuck c' := by
  exact Iff.rfl

/-- Every configuration terminates, goes wrong, or reacts. The three cases are exhaustive but
not exclusive: a nondeterministic configuration can exhibit more than one. -/
theorem terminates_or_goesWrong_or_reacts {Config : Type u} {Label : Type v}
    (S : OpSem Config Label) (c : Config) :
    (∃ (μs : List Label) (c' : Config), S.lts.MTr c μs c' ∧ S.Final c') ∨
    (∃ (μs : List Label) (c' : Config), S.lts.MTr c μs c' ∧ S.Stuck c') ∨
    ∃ μs : Cslib.ωSequence Label, Behavior.reacts μs ∈ Beh S c := by
  by_cases hterm : ∃ (μs : List Label) (c' : Config), S.lts.MTr c μs c' ∧ S.Final c'
  · exact Or.inl hterm
  · by_cases hwrong : ∃ (μs : List Label) (c' : Config), S.lts.MTr c μs c' ∧ S.Stuck c'
    · exact Or.inr (Or.inl hwrong)
    · have hsucc : ∀ x : {x // S.Steps c x}, ∃ y : {x // S.Steps c x}, S.Step x.1 y.1 := by
        intro x
        have hnotfin : ¬ S.Final x.1 := by
          intro hfin
          obtain ⟨μs, hmtr⟩ := x.2
          exact hterm ⟨μs, x.1, hmtr, hfin⟩
        have hnotstuck : ¬ S.Stuck x.1 := by
          intro hstuck
          obtain ⟨μs, hmtr⟩ := x.2
          exact hwrong ⟨μs, x.1, hmtr, hstuck⟩
        have hnotterm : ¬ S.lts.IsTerminal x.1 := by
          intro hterml
          exact hnotstuck ((OpSem.stuck_iff S).mpr ⟨hnotfin, hterml⟩)
        have hex : ∃ μ y, S.lts.Tr x.1 μ y := by
          by_contra hcon
          apply hnotterm
          intro μ y htr
          exact hcon ⟨μ, y, htr⟩
        obtain ⟨μ, y, htr⟩ := hex
        have hstep : S.Step x.1 y := ⟨μ, htr⟩
        obtain ⟨μs, hmtr⟩ := x.2
        have hsingle : S.lts.MTr x.1 [μ] y := Cslib.LTS.MTr.single S.lts htr
        have hmtr' : S.lts.MTr c (μs ++ [μ]) y := Cslib.LTS.MTr.comp S.lts hmtr hsingle
        exact ⟨⟨y, μs ++ [μ], hmtr'⟩, hstep⟩
      have hbase : S.Steps c c := ⟨[], Cslib.LTS.MTr.refl⟩
      obtain ⟨seq, hseq0, hseqS⟩ : ∃ seq : Nat → {x // S.Steps c x},
          seq 0 = ⟨c, hbase⟩ ∧ ∀ n, seq (n + 1) = Classical.choose (hsucc (seq n)) :=
        ⟨Nat.rec (motive := fun _ => {x // S.Steps c x}) ⟨c, hbase⟩
          (fun _ x => Classical.choose (hsucc x)), rfl, fun n => rfl⟩
      suffices hdiv : S.Diverges c by
        obtain ⟨ss, μs, h0, hexec⟩ := hdiv
        exact Or.inr (Or.inr ⟨μs, (reacts_mem_iff S).mpr ⟨ss, h0, hexec⟩⟩)
      refine (OpSem.diverges_iff S).mpr ⟨fun n => (seq n).1, ?_, ?_⟩
      · change (seq 0).1 = c
        rw [hseq0]
      · change ∀ i, S.Step (seq i).1 (seq (i + 1)).1
        intro i
        rw [hseqS i]
        exact Classical.choose_spec (hsucc (seq i))

/-- Every configuration has at least one behavior. -/
theorem exists_behavior {Config : Type u} {Label : Type v} (S : OpSem Config Label) (c : Config) :
    (Beh S c).Nonempty := by
  obtain hterm | hwrong | hreact := terminates_or_goesWrong_or_reacts S c
  · obtain ⟨μs, c', hmtr, hfin⟩ := hterm
    exact ⟨Behavior.terminates μs, (terminates_mem_iff S).mpr ⟨c', hmtr, hfin⟩⟩
  · obtain ⟨μs, c', hmtr, hstuck⟩ := hwrong
    exact ⟨Behavior.goesWrong μs, (goesWrong_mem_iff S).mpr ⟨c', hmtr, hstuck⟩⟩
  · obtain ⟨μs, hmem⟩ := hreact
    exact ⟨Behavior.reacts μs, hmem⟩

/-- Leroy form (1): source and target share exactly the same behaviors. -/
def Preserves1 {Config : Type u} {Label : Type v} (S T : OpSem Config Label) (src tgt : Config) :
    Prop :=
  Beh S src = Beh T tgt

/-- Leroy form (2): safe sources include all target behaviors. -/
def Preserves2 {Config : Type u} {Label : Type v} (S T : OpSem Config Label) (src tgt : Config) :
    Prop :=
  S.Safe src → Beh T tgt ⊆ Beh S src

/-- Preservation in form (2) sends safe sources to safe targets. -/
theorem Preserves2.safe_target {Config : Type u} {Label : Type v} {S T : OpSem Config Label}
    {src tgt : Config} : Preserves2 S T src tgt → S.Safe src → T.Safe tgt := by
  intro hpres hsafeS
  unfold Preserves2 at hpres
  have hsub := hpres hsafeS
  unfold OpSem.Safe
  intro d hsteps hstuck
  unfold OpSem.Steps at hsteps
  obtain ⟨μs, hmtr⟩ := hsteps
  have hmemT : Behavior.goesWrong μs ∈ Beh T tgt :=
    (goesWrong_mem_iff T).mpr ⟨d, hmtr, hstuck⟩
  have hmemS := hsub hmemT
  rw [goesWrong_mem_iff] at hmemS
  obtain ⟨s, hmtrS, hstuckS⟩ := hmemS
  unfold OpSem.Safe at hsafeS
  exact hsafeS s ⟨μs, hmtrS⟩ hstuckS

/-- Preservation in form (2) composes vertically. -/
theorem Preserves2.trans {Config : Type u} {Label : Type v} {S T U : OpSem Config Label}
    {src mid tgt : Config} : Preserves2 S T src mid → Preserves2 T U mid tgt →
      Preserves2 S U src tgt := by
  intro h1 h2
  unfold Preserves2
  intro hsafeS
  have hsafeT : T.Safe mid := Preserves2.safe_target h1 hsafeS
  unfold Preserves2 at h1 h2
  have hsub1 := h1 hsafeS
  have hsub2 := h2 hsafeT
  exact hsub2.trans hsub1

/-- Configurations of the nondeterminism counterexample toy semantics: exactly `a`, `b1` and
`b2`. -/
inductive NondetToyCfg where
  | a
  | b1
  | b2
deriving DecidableEq

/-- Nondeterministic toy: `a` emits `true` to reach `b1` or `false` to reach `b2`. -/
def nondetToy : OpSem NondetToyCfg Bool where
  lts := { Tr := fun x μ y => (x = .a ∧ μ = true ∧ y = .b1) ∨ (x = .a ∧ μ = false ∧ y = .b2) }
  Final := fun c => c = .b1 ∨ c = .b2
  final_terminal := by intro c hc μ s' h; cases c <;> simp_all

/-- Deterministic toy: `a` emits `true` and steps only to `b1`. -/
def detToy : OpSem NondetToyCfg Bool where
  lts := { Tr := fun x μ y => x = .a ∧ μ = true ∧ y = .b1 }
  Final := fun c => c = .b1 ∨ c = .b2
  final_terminal := by intro c hc μ s' h; cases c <;> simp_all

/-- Preservation in form (1) fails from the nondeterministic to the deterministic toy, both
starting at `a`. -/
theorem preserves1_fails_nondet_to_det :
    ¬ Preserves1 nondetToy detToy NondetToyCfg.a NondetToyCfg.a := by
  unfold Preserves1
  intro heq
  have hTrN : nondetToy.lts.Tr NondetToyCfg.a false NondetToyCfg.b2 :=
    Or.inr ⟨rfl, rfl, rfl⟩
  have hMTrN : nondetToy.lts.MTr NondetToyCfg.a [false] NondetToyCfg.b2 :=
    Cslib.LTS.MTr.single _ hTrN
  have hFinN : nondetToy.Final NondetToyCfg.b2 := Or.inr rfl
  have hmemN : Behavior.terminates [false] ∈
      Beh nondetToy NondetToyCfg.a :=
    (terminates_mem_iff nondetToy).mpr ⟨NondetToyCfg.b2, hMTrN, hFinN⟩
  rw [heq] at hmemN
  obtain ⟨e, hMTrD, _⟩ := (terminates_mem_iff detToy).mp hmemN
  have hTrD : detToy.lts.Tr NondetToyCfg.a false e :=
    (Cslib.LTS.MTr.singleton_iff detToy.lts _ _ _).mp hMTrD
  obtain ⟨_, hlabel, _⟩ := hTrD
  cases hlabel

/-- Preservation in form (2) holds from the nondeterministic to the deterministic toy, both
starting at `a`. -/
theorem preserves2_nondet_to_det :
    Preserves2 nondetToy detToy NondetToyCfg.a NondetToyCfg.a := by
  unfold Preserves2
  intro _ b hb
  have hTr : ∀ {x : NondetToyCfg} {μ : Bool} {y : NondetToyCfg},
      detToy.lts.Tr x μ y → nondetToy.lts.Tr x μ y := fun h => Or.inl h
  have hMTr : ∀ {x : NondetToyCfg} {μs : List Bool} {y : NondetToyCfg},
      detToy.lts.MTr x μs y → nondetToy.lts.MTr x μs y := by
    intro x μs y h
    induction h with
    | refl => exact Cslib.LTS.MTr.refl
    | stepL htr _ ih => exact Cslib.LTS.MTr.stepL (hTr htr) ih
  have hfrom : ∀ {μs : List Bool} {y : NondetToyCfg},
      detToy.lts.MTr NondetToyCfg.a μs y → y = NondetToyCfg.a ∨ y = NondetToyCfg.b1 := by
    intro μs y h
    cases h with
    | refl => exact Or.inl rfl
    | stepL htr hrest =>
      obtain ⟨_, _, rfl⟩ := htr
      cases hrest with
      | refl => exact Or.inr rfl
      | stepL htr2 _ =>
        obtain ⟨hb1, _, _⟩ := htr2
        cases hb1
  cases b with
  | terminates μs =>
    obtain ⟨c', hm, hf⟩ := (terminates_mem_iff detToy).mp hb
    exact (terminates_mem_iff nondetToy).mpr ⟨c', hMTr hm, hf⟩
  | reacts μs =>
    obtain ⟨ss, _, hexec⟩ := (reacts_mem_iff detToy).mp hb
    obtain ⟨_, _, h1⟩ := hexec 0
    obtain ⟨h2, _, _⟩ := hexec 1
    have hcontra : NondetToyCfg.b1 = NondetToyCfg.a := h1.symm.trans h2
    cases hcontra
  | goesWrong μs =>
    obtain ⟨c', hm, hst⟩ := (goesWrong_mem_iff detToy).mp hb
    obtain ⟨hnf, hterm⟩ := (OpSem.stuck_iff detToy).mp hst
    rcases hfrom hm with rfl | rfl
    · exact (hterm true NondetToyCfg.b1 ⟨rfl, rfl, rfl⟩).elim
    · exact (hnf (Or.inl rfl)).elim

end Cslib.Languages.ProgramBehaviors
