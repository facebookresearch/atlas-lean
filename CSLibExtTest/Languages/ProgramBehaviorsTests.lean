/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.ProgramBehaviors

/-!
Tests for `Cslib.Languages.ProgramBehaviors`: toy semantics and statement checks.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Languages.ProgramBehaviorsTests

open Cslib.Languages.OperationalSemantics Cslib.Languages.ProgramBehaviors

/-- Stuck toy: no steps and no final configurations. -/
def stuckToy : OpSem Unit Unit where
  lts := { Tr := fun _ _ _ => False }
  Final := fun _ => False
  final_terminal := by intro c hc; exact False.elim hc

/-- Looping toy: the single configuration always steps. -/
def loopToy : OpSem Unit Unit where
  lts := { Tr := fun _ _ _ => True }
  Final := fun _ => False
  final_terminal := by intro c hc; exact False.elim hc

/-- `IMP` skip terminates immediately with the empty trace. -/
theorem terminates_imp_skip :
    Behavior.terminates ([] : List Unit) ∈
      Beh Cslib.Languages.OperationalSemantics.imp (Cslib.IMP.Cmd.skip, fun _ => 0) := by
  apply (terminates_mem_iff Cslib.Languages.OperationalSemantics.imp).mpr
  exact ⟨(Cslib.IMP.Cmd.skip, fun _ => 0), Cslib.LTS.MTr.refl, rfl⟩

/-- The stuck toy goes wrong immediately with the empty trace. -/
theorem goesWrong_stuckToy : Behavior.goesWrong ([] : List Unit) ∈ Beh stuckToy () := by
  have hnf : ¬ stuckToy.Final () := fun h => h
  have ht : stuckToy.lts.IsTerminal () := fun _ _ h => h
  have hs : stuckToy.Stuck () := (OpSem.stuck_iff stuckToy).mpr ⟨hnf, ht⟩
  exact (goesWrong_mem_iff stuckToy).mpr ⟨(), Cslib.LTS.MTr.refl, hs⟩

/-- The looping toy reacts with the constant trace. -/
theorem reacts_loopToy :
    Behavior.reacts (Cslib.ωSequence.const ()) ∈ Beh loopToy () := by
  have h0 : (Cslib.ωSequence.const ()) 0 = () := rfl
  have he : loopToy.lts.OmegaExecution (Cslib.ωSequence.const ()) (Cslib.ωSequence.const ()) :=
    fun i => trivial
  exact (reacts_mem_iff loopToy).mpr ⟨Cslib.ωSequence.const (), h0, he⟩

/-- Preservation in form (2) is reflexive on `IMP`. -/
theorem preserves2_refl_imp (c : Cslib.IMP.Config) :
    Preserves2 Cslib.Languages.OperationalSemantics.imp Cslib.Languages.OperationalSemantics.imp
      c c := by
  unfold Preserves2
  intro _ b hb
  exact hb

/-- The nondeterministic toy exhibits two observably distinct termination behaviors. -/
theorem nondet_has_two_behaviors :
    Behavior.terminates [true] ∈ Beh nondetToy NondetToyCfg.a ∧
      Behavior.terminates [false] ∈ Beh nondetToy NondetToyCfg.a := by
  have hT1 : nondetToy.lts.Tr NondetToyCfg.a true NondetToyCfg.b1 := Or.inl ⟨rfl, rfl, rfl⟩
  have hM1 : nondetToy.lts.MTr NondetToyCfg.a [true] NondetToyCfg.b1 := Cslib.LTS.MTr.single _ hT1
  have hF1 : nondetToy.Final NondetToyCfg.b1 := Or.inl rfl
  have hT2 : nondetToy.lts.Tr NondetToyCfg.a false NondetToyCfg.b2 := Or.inr ⟨rfl, rfl, rfl⟩
  have hM2 : nondetToy.lts.MTr NondetToyCfg.a [false] NondetToyCfg.b2 := Cslib.LTS.MTr.single _ hT2
  have hF2 : nondetToy.Final NondetToyCfg.b2 := Or.inr rfl
  have hm1 : Behavior.terminates [true] ∈ Beh nondetToy NondetToyCfg.a :=
    (terminates_mem_iff nondetToy).mpr ⟨NondetToyCfg.b1, hM1, hF1⟩
  have hm2 : Behavior.terminates [false] ∈ Beh nondetToy NondetToyCfg.a :=
    (terminates_mem_iff nondetToy).mpr ⟨NondetToyCfg.b2, hM2, hF2⟩
  exact ⟨hm1, hm2⟩

/-- From the nondeterministic to the deterministic toy, form (1) fails while form (2) holds. -/
theorem nondet_to_det_preserves1_fails_preserves2_holds :
    ¬ Preserves1 nondetToy detToy NondetToyCfg.a NondetToyCfg.a ∧
      Preserves2 nondetToy detToy NondetToyCfg.a NondetToyCfg.a :=
  ⟨preserves1_fails_nondet_to_det, preserves2_nondet_to_det⟩

end Cslib.Languages.ProgramBehaviorsTests
