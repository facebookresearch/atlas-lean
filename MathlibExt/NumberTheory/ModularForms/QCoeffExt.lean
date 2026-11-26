/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean`
and
`P2M/Sol/S_ModularFormClass_eq_of_forall_qCoeff_eq.lean`
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

public import MathlibExt.NumberTheory.ModularForms.CuspFormConj

/-!
# Modular forms are determined by their `q`-expansion coefficients

A modular form for a group with `1` as a strict period is determined by its
`q`-expansion coefficients `ModularFormClass.qCoeff`. The proof compares the
two `q`-expansions given by `ModularForm.hasSum_qExpansion`.

## Main results

* `ModularFormClass.eq_of_forall_qCoeff_eq`
-/

@[expose] public section

open UpperHalfPlane

namespace ModularFormClass

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- **`q`-expansion coefficients determine a modular form.** Two modular forms for a group
with `1` as a strict period are equal when their `q`-expansion coefficients agree. -/
public theorem eq_of_forall_qCoeff_eq [ModularFormClass F Γ k] {f g : F}
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  refine DFunLike.ext f g fun τ => ?_
  have hf := ModularForm.hasSum_qExpansion (f := f) one_pos hΓ τ
  have hg := ModularForm.hasSum_qExpansion (f := g) one_pos hΓ τ
  simp only [← qCoeff_eq, h] at hf
  simp only [← qCoeff_eq] at hg
  exact hf.unique hg

end ModularFormClass
