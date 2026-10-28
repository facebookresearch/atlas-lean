/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.TensorSimple
public import MathlibExtTest.NumberTheory.SelbergClass.RankinSelberg
public import MathlibExtTest.NumberTheory.SelbergClass.Primitive

/-!
# Tests for `isTensorSimple_iff_isSelbergPrimitive`

The hypotheses other than Selberg's conjectures are met by `ζ` (with `ζ ⊗ ζ̄ = ζ ∈ 𝒮`) and by
`1` (with `1 ⊗ 1 = 1 ∈ 𝒮`); both sides of the equivalence are true for `ζ` and false for `1`.
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

example (hA : ConjectureA) (hB : ConjectureB) :
    IsTensorSimple zetaC ↔ IsSelbergPrimitive zetaC :=
  isTensorSimple_iff_isSelbergPrimitive hA hB zetaC zeta_mem_selbergClass zetaLog
    isEulerLog_zeta ⟨zetaC, zeta_mem_selbergClass, by rw [tensorLog_zetaLog]; exact isEulerLog_zeta⟩

example (hA : ConjectureA) (hB : ConjectureB) :
    IsTensorSimple (1 : ArithmeticFunction ℂ) ↔ IsSelbergPrimitive 1 := by
  have h0 : tensorLog (0 : ℕ → ℂ) (fun n => starRingEnd ℂ ((0 : ℕ → ℂ) n)) = 0 :=
    funext fun n => by simp [tensorLog]
  exact isTensorSimple_iff_isSelbergPrimitive hA hB 1 one_mem_selbergClass 0 isEulerLog_one
    ⟨1, one_mem_selbergClass, by rw [h0]; exact isEulerLog_one⟩

/-- Both sides hold for `ζ` unconditionally. -/
example : IsTensorSimple zetaC ∧ IsSelbergPrimitive zetaC :=
  ⟨isTensorSimple_zeta, isSelbergPrimitive_zeta⟩

/-- Both sides fail for `1` unconditionally. -/
example : ¬ IsTensorSimple (1 : ArithmeticFunction ℂ) ∧ ¬ IsSelbergPrimitive 1 :=
  ⟨not_isTensorSimple_one, fun h => h.2.1 rfl⟩

end SelbergClassTest
