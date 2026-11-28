/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_CuspidalClass.lean` and
`Theorems/Thm_ModularCurve_cuspidalClass_ne_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
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

public import MathlibExt.NumberTheory.ModularForms.CuspidalDivisor

@[expose] public section

namespace ModularCurve

variable {C : Type*}

/-- The cuspidal class is nonzero whenever the cuspidal divisor is not
in the chosen principal subgroup. -/
theorem cuspidalClass_ne_zero_of_not_mem
    (principal : AddSubgroup (CurveDivisor C)) (cuspZero cuspInfty : C)
    (h : cuspidalDivisor cuspZero cuspInfty ∉ principal) :
    cuspidalClass principal cuspZero cuspInfty ≠ 0 := by
  rw [Ne, cuspidalClass_eq_zero_iff]
  exact h

/-- Exemplar of cuspidal-class non-vanishing: modulo the trivial
principal subgroup, distinct cusps give a nonzero cuspidal class. -/
theorem cuspidalClass_bot_ne_zero (cuspZero cuspInfty : C)
    (h : cuspZero ≠ cuspInfty) :
    cuspidalClass (⊥ : AddSubgroup (CurveDivisor C)) cuspZero cuspInfty ≠ 0 := by
  apply cuspidalClass_ne_zero_of_not_mem
  simp only [AddSubgroup.mem_bot]
  exact cuspidalDivisor_ne_zero cuspZero cuspInfty h

end ModularCurve
