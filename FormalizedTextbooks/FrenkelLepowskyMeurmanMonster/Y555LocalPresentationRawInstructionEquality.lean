/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal raw instruction equality detects exact acyclic source-word instructions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The raw instruction retains all information of its bound-checked acyclic instruction. -/
theorem y322InstructionRaw_injective {earlier : ℕ} :
    Function.Injective (y322InstructionRaw (earlier := earlier)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [y322InstructionRaw, Fin.ext_iff]

/-- Exact bound-checked source-word instructions have decidable literal equality. -/
instance y322WordInstructionDecidableEq (earlier : ℕ) :
    DecidableEq (Y322WordInstruction earlier) :=
  Function.Injective.decidableEq y322InstructionRaw_injective

/-- Equal raw instructions certify equality of their precise acyclic source instructions. -/
theorem y322Instruction_eq_of_raw_eq {earlier : ℕ} (a b : Y322WordInstruction earlier)
    (h : y322InstructionRaw a = y322InstructionRaw b) : a = b :=
  y322InstructionRaw_injective h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
