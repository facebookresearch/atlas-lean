/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.CslibBridge

@[expose] public section

set_option autoImplicit false

namespace Cslib.Semantics.LTS.CslibBridgeTests

/-- The natural-number counter: `n` steps to `n + 1` under the unit label. -/
def counter : _root_.Cslib.LTS ℕ Unit := ⟨fun n _ m => m = n + 1⟩

example : ofCslib (toCslib counter) = counter :=
  ofCslib_toCslib counter

example : toCslib (ofCslib (toCslib counter)) = toCslib counter :=
  toCslib_ofCslib (toCslib counter)

/-- A three-step counter trace from `0` to `3`. -/
theorem counterTrace3 : counter.MTr 0 [(), (), ()] 3 :=
  _root_.Cslib.LTS.MTr.stepL rfl
    (_root_.Cslib.LTS.MTr.stepL rfl
      (_root_.Cslib.LTS.MTr.stepL rfl _root_.Cslib.LTS.MTr.refl))

example : (toCslib counter).MTr 0 [(), (), ()] 3 :=
  trace_iff_mTr.mp counterTrace3

example : counter.MTr 0 [(), (), ()] 3 :=
  trace_iff_mTr.mpr (trace_iff_mTr.mp counterTrace3)

example :
    ∃ (μs : List Unit) (ss' : List ℕ),
      (toCslib counter).Execution 0 μs 3 ss' ∧ μs.length = 3 := by
  have hrun : Cslib.LTS.FiniteRun (lts := counter) (fun i => i) 3 := fun i _ => ⟨(), rfl⟩
  obtain ⟨μs, ss', hexec, hlen, hagree⟩ := execution_of_finiteRun hrun
  have hss'len : ss'.length = 4 := by rw [hexec.length, hlen]
  have h0 : ss'[0]'(by omega) = 0 := hagree 0 (by omega)
  have h3 : ss'[3]'(by omega) = 3 := hagree 3 (by omega)
  exact ⟨μs, ss', hexec, hlen⟩

/-- A nondeterministic diamond: `0` steps to `1` or `2`, and both step
to `3`. Endpoints and length alone do not determine the intermediate
state. -/
def diamond : _root_.Cslib.LTS ℕ Unit :=
  ⟨fun s _ t => (s = 0 ∧ (t = 1 ∨ t = 2)) ∨ ((s = 1 ∨ s = 2) ∧ t = 3)⟩

theorem diamondStep02 : (toCslib diamond).Tr 0 () 2 :=
  Or.inl ⟨rfl, Or.inr rfl⟩

theorem diamondStep23 : (toCslib diamond).Tr 2 () 3 :=
  Or.inr ⟨Or.inr rfl, rfl⟩

/-- The execution from `0` to `3` passing through `2`. -/
theorem diamondExecution :
    (toCslib diamond).Execution 0 [(), ()] 3 [0, 2, 3] :=
  _root_.Cslib.LTS.Execution.stepL diamondStep02
    (_root_.Cslib.LTS.Execution.stepL diamondStep23
      (_root_.Cslib.LTS.Execution.refl (lts := toCslib diamond) 3))

/-- Reverse conversion pins the intermediate state. Regression test:
against the former endpoints-and-length-only statement of
`finiteRun_of_execution`, a run through `1` satisfies the conclusion
just as well, so `ss 1 = 2` did not follow. -/
example : ∃ ss : ℕ → ℕ, ss 0 = 0 ∧ ss 1 = 2 ∧ ss 2 = 3 ∧
    Cslib.LTS.FiniteRun (lts := diamond) ss 2 := by
  obtain ⟨ss, h0, h2, hrun, hagree⟩ :=
    finiteRun_of_execution diamondExecution
  exact ⟨ss, h0, hagree 1 (by decide), h2, hrun⟩

/-- A hand-built infinite execution of the counter. -/
theorem counterOmegaExecution :
    (toCslib counter).OmegaExecution ⟨fun i => i⟩ ⟨fun _ => ()⟩ := by
  intro i
  rfl

example : ∃ label, counter.Tr 2 label 3 := by
  have h := (omegaRun_of_omegaExecution counterOmegaExecution) 2
  exact h

example :
    _root_.Cslib.LTS.Bisimilarity (toCslib counter) (toCslib counter) 0 0 :=
  bisimilar_iff.mp (_root_.Cslib.LTS.HomBisimilarity.refl 0)

#print axioms Cslib.Semantics.LTS.trace_iff_mTr
#print axioms Cslib.Semantics.LTS.execution_of_finiteRun
#print axioms Cslib.Semantics.LTS.isBisimulation_iff

end Cslib.Semantics.LTS.CslibBridgeTests
