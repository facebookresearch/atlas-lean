/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.NonTautologyDefs

namespace MetaMathlibExt.Complexity.NPComplete.NonTautology

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Logic.LegacyPL

private theorem accepts_encoding (i : NonTautologyInstance) :
    nonTautologyDec (bitEncode i) = true ↔ WellFormed i ∧ NonTautologyFeasible i := by
  simp [nonTautologyDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : nonTautologyDec [true] = false := by
  have h : bitDecode (α := NonTautologyInstance) [true] = none := rfl
  simp [nonTautologyDec, h]

/-- `u₀ → u₁` (postfix `u₀ u₁ →`) is falsified by `u₀ = true`, `u₁ = false`. -/
example : nonTautologyDec (bitEncode ((2, [(0, 0), (0, 1), (4, 0)]) : NonTautologyInstance)) =
    true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, _, rfl, fun x => decide (x = 0), ?_⟩
  rfl

/-- `u₀ ∨ ¬u₀` (postfix `u₀ u₀ ¬ ∨`) is a tautology. -/
example :
    nonTautologyDec (bitEncode ((1, [(0, 0), (0, 0), (1, 0), (3, 0)]) : NonTautologyInstance)) =
      false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, E, hE, σ, hσ⟩ := (accepts_encoding _).1 hacc
  have hparse : parse [(0, 0), (0, 0), (1, 0), (3, 0)] =
      some (.or (.atom ((0 : ℕ) : WithBot ℕ))
        (.imp (.atom ((0 : ℕ) : WithBot ℕ)) (.atom ⊥))) := rfl
  rw [hparse, Option.some.injEq] at hE
  subst hE
  simp [Proposition.evalBool, valuation] at hσ

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((1, [(0, 0), (0, 0), (1, 0), (3, 0)]) : NonTautologyInstance) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.NonTautology
