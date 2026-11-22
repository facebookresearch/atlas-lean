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
divergence with an infinite label trace. Final and stuck configurations stay existential in
`Beh`; every anchor label counts as an observable event, and results are observed only as labels.
Excluded: silent (finite reactive trace) divergence and any tau companion (the anchor has no
tau), cross-language preservation with a label map, and any soundness claim about a compiler.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Cslib.Languages.ProgramBehaviors

open Cslib.Languages.OperationalSemantics

/-- Observable program behaviors over label traces: termination, divergence, or going wrong. -/
inductive Behavior (Label : Type v) where
  | terminates (trace : List Label)
  | diverges (trace : Cslib.ωSequence Label)
  | goesWrong (trace : List Label)

/-- The behavior set of a configuration; final and stuck configurations stay existential. -/
def Beh {Config : Type u} {Label : Type v} (S : OpSem Config Label) (c : Config) :
    Set (Behavior Label) :=
  fun b => match b with
    | .terminates μs => ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Final c'
    | .diverges μs => ∃ ss : Cslib.ωSequence Config, ss 0 = c ∧ S.lts.OmegaExecution ss μs
    | .goesWrong μs => ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Stuck c'

/-- Termination membership unfolds to a multistep reaching some final configuration. -/
theorem terminates_mem_iff {Config : Type u} {Label : Type v} (S : OpSem Config Label)
    {c : Config} {μs : List Label} :
    Behavior.terminates μs ∈ Beh S c ↔ ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Final c' := by
  exact Iff.rfl

/-- Divergence membership unfolds to an infinite omega execution. -/
theorem diverges_mem_iff {Config : Type u} {Label : Type v} (S : OpSem Config Label)
    {c : Config} {μs : Cslib.ωSequence Label} :
    Behavior.diverges μs ∈ Beh S c ↔
      ∃ ss : Cslib.ωSequence Config, ss 0 = c ∧ S.lts.OmegaExecution ss μs := by
  exact Iff.rfl

/-- Wrong-going membership unfolds to a multistep reaching some stuck configuration. -/
theorem goesWrong_mem_iff {Config : Type u} {Label : Type v} (S : OpSem Config Label)
    {c : Config} {μs : List Label} :
    Behavior.goesWrong μs ∈ Beh S c ↔ ∃ c' : Config, S.lts.MTr c μs c' ∧ S.Stuck c' := by
  exact Iff.rfl

/-- Every configuration terminates, goes wrong, or diverges. -/
theorem trichotomy {Config : Type u} {Label : Type v} (S : OpSem Config Label) (c : Config) :
    (∃ (μs : List Label) (c' : Config), S.lts.MTr c μs c' ∧ S.Final c') ∨
    (∃ (μs : List Label) (c' : Config), S.lts.MTr c μs c' ∧ S.Stuck c') ∨ S.Diverges c := by
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
      refine Or.inr (Or.inr ((OpSem.diverges_iff S).mpr ⟨fun n => (seq n).1, ?_, ?_⟩))
      · change (seq 0).1 = c
        rw [hseq0]
      · change ∀ i, S.Step (seq i).1 (seq (i + 1)).1
        intro i
        rw [hseqS i]
        exact Classical.choose_spec (hsucc (seq i))

/-- Every configuration has at least one behavior. -/
theorem exists_behavior {Config : Type u} {Label : Type v} (S : OpSem Config Label) (c : Config) :
    (Beh S c).Nonempty := by
  obtain hterm | hwrong | hdiv := trichotomy S c
  · obtain ⟨μs, c', hmtr, hfin⟩ := hterm
    exact ⟨Behavior.terminates μs, (terminates_mem_iff S).mpr ⟨c', hmtr, hfin⟩⟩
  · obtain ⟨μs, c', hmtr, hstuck⟩ := hwrong
    exact ⟨Behavior.goesWrong μs, (goesWrong_mem_iff S).mpr ⟨c', hmtr, hstuck⟩⟩
  · obtain ⟨ss, μs, h0, hexec⟩ := hdiv
    exact ⟨Behavior.diverges μs, (diverges_mem_iff S).mpr ⟨ss, h0, hexec⟩⟩

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

/-- Configurations of the nondeterminism counterexample toy semantics. -/
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

/-- Preservation in form (1) fails from the nondeterministic to the deterministic toy. -/
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

end Cslib.Languages.ProgramBehaviors
