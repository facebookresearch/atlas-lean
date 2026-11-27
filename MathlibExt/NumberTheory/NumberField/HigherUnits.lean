/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Higher unit groups of the completions of a number field

For a finite place `v` of a number field `K` and `n : ℕ`, `higherUnitsAt K v n` (in the namespace
`LanglandsTunnell.TateLocal`) is the higher unit group `1 + 𝔭ᵥⁿ` of the completion `K_v`, as a
set of units; for `n = 0` it is the unit group of the valuation ring. A character of `K_vˣ` that
is trivial on one of these sets has finite conductor.
-/

@[expose] public section

open IsDedekindDomain NumberField

namespace LanglandsTunnell.TateLocal

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The higher unit group `1 + 𝔭ᵥⁿ` of the completion `K_v`, as a set of units: the units of
valuation `1` whose distance to `1` has valuation at most `exp (-n)`; for `n = 0` it is the full
unit group of the valuation ring. -/
def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)))}

theorem mem_higherUnitsAt_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v n ↔ Valued.v (u : v.adicCompletion K) = 1 ∧
      (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))) :=
  Iff.rfl

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem mem_higherUnitsAt_zero_iff {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  simp [mem_higherUnitsAt_iff]

theorem one_mem_higherUnitsAt (n : ℕ) :
    (1 : (v.adicCompletion K)ˣ) ∈ higherUnitsAt K v n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le

theorem higherUnitsAt_antitone : Antitone (higherUnitsAt K v) := by
  intro m n hmn u hu
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.mpr (by omega))

end LanglandsTunnell.TateLocal
