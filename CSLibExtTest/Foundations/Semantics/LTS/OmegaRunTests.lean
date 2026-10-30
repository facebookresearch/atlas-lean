/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.OmegaRun

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS.OmegaRunTests

/-- The natural-number counter: `n` steps to `n + 1` under the unit label. -/
def counter : LTS ℕ Unit := ⟨fun n _ m => m = n + 1⟩

example : counter.UnlabelledTr 2 3 := ⟨(), rfl⟩

example : counter.OmegaRun (fun i => i) := by
  intro i
  exact ⟨(), rfl⟩

example : counter.OmegaRun (fun i => i + 7) := by
  intro i
  refine ⟨(), ?_⟩
  show (i + 1) + 7 = (i + 7) + 1
  omega

example : counter.CanReach 0 5 := by
  apply LTS.finiteRun_canReach (ss := fun i => i) (k := 5)
  intro i _
  exact ⟨(), rfl⟩

/-- A three-step counter multistep transition from `0` to `3`. -/
theorem counterTrace3 : counter.MTr 0 [(), (), ()] 3 :=
  .stepL rfl (.stepL rfl (.stepL rfl .refl))

example :
    ∃ ss : ℕ → ℕ, ss 0 = 0 ∧ ss 3 = 3 ∧ counter.FiniteRun ss 3 := by
  obtain ⟨ss, h0, h3, hrun⟩ :=
    LTS.exists_finiteRun_of_mtr counterTrace3
  exact ⟨ss, h0, h3, hrun⟩

example : counter.OmegaRun (Semantics.shiftSeq (fun i => i) 3) :=
  LTS.omegaRun_shift (fun _ => ⟨(), rfl⟩) 3

example : Semantics.shiftSeq (fun i => i) 0 = (fun i => i) :=
  Semantics.shiftSeq_zero _

#print axioms Cslib.LTS.exists_finiteRun_of_mtr
#print axioms Cslib.LTS.finiteRun_canReach

end Cslib.LTS.OmegaRunTests
