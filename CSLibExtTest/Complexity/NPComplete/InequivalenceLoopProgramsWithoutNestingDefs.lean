/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNestingDefs

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNesting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : InequivalenceLoopProgramsInstance) :
    inequivalenceLoopProgramsDec (bitEncode i) = true ↔
      WellFormed i ∧ InequivalenceLoopProgramsFeasible i := by
  simp [inequivalenceLoopProgramsDec, bitDecode_bitEncode]

/-- `loop x₁; x₀ ← x₀ + 1; end`: adds `x₁` to `x₀`. -/
private abbrev countUp : List Instruction := [(3, 1, 0), (1, 0, 0), (4, 0, 0)]

/-- `x₀ ← x₁`. -/
private abbrev copy : List Instruction := [(0, 0, 1)]

private theorem iterate_inc (k : ℕ) (s : ℕ → ℕ) :
    ((fun t : ℕ → ℕ => Function.update t 0 (t 0 + 1))^[k] s) 0 = s 0 + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [Function.update_self]
    rw [ih]
    omega

private theorem run_countUp (s : ℕ → ℕ) : run s none countUp 0 = s 0 + s 1 := by
  simp [run, step, iterate_inc]

private theorem run_copy (s : ℕ → ℕ) : run s none copy 0 = s 1 := by
  simp [run, step]

/-- A lone continuation bit is a truncated instance encoding. -/
example : inequivalenceLoopProgramsDec [true] = false := by
  have h : bitDecode (α := InequivalenceLoopProgramsInstance) [true] = none := rfl
  simp [inequivalenceLoopProgramsDec, h]

/-- With input `x₁ = 1`, the counting loop leaves `x₀ = 1` while the empty program leaves
`x₀ = 0`. -/
example :
    inequivalenceLoopProgramsDec
      (bitEncode ((2, [1], 0, countUp, []) : InequivalenceLoopProgramsInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by simp [WellFormed, LoopsUnnested], fun _ => 1, by simp, ?_⟩
  rw [run_countUp]
  simp [run]

/-- The counting loop and the copy `x₀ ← x₁` agree on every input, so the programs are
equivalent. -/
example :
    inequivalenceLoopProgramsDec
      (bitEncode ((2, [1], 0, countUp, copy) : InequivalenceLoopProgramsInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, f, -, hne⟩ := (accepts_encoding _).1 hacc
  apply hne
  rw [run_countUp, run_copy]
  simp

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((2, [1], 0, countUp, copy) : InequivalenceLoopProgramsInstance) :=
  by simp [WellFormed, LoopsUnnested]

end MetaMathlibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNesting
