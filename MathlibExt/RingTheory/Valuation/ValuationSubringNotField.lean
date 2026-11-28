/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean`
and
`P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean`
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

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# A proper valuation subring is not a field

A valuation subring of a field that is not the whole field cannot itself
be a field: an element outside the subring has its inverse inside, and a
field inverse for that inverse would put the element back inside.
-/

@[expose] public section

/-- A valuation subring of a field, if it is not the whole field, is not
a field. No discreteness or value-group hypothesis is needed. -/
public theorem ValuationSubring.not_isField_of_ne_top (F : Type*) [Field F]
    {A : ValuationSubring F} (hA : A ≠ ⊤) : ¬ IsField A := by
  intro hf
  apply hA
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  by_cases hx : x ∈ A
  · exact hx
  · exfalso
    have hx0 : x ≠ 0 := fun h => hx (h ▸ A.zero_mem)
    have hxi : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hx
    have hxi0 : (⟨x⁻¹, hxi⟩ : A) ≠ 0 := by
      simp only [ne_eq, Subtype.ext_iff]
      exact inv_ne_zero hx0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hxi0
    have hb' : x⁻¹ * (b : F) = 1 := by
      have h := congrArg (Subtype.val) hb
      simpa using h
    have hbx : (b : F) = x := by
      field_simp at hb'
      exact hb'
    exact hx (hbx ▸ b.2)
