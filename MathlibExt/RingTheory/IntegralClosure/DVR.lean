/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal`
`.lean` and
`P2M/Sol/S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal`
`.lean`
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

public import MathlibExt.RingTheory.DiscreteValuationRing.IntegralClosureComplete

/-!
# Integral closures of complete DVRs in finite separable extensions

Let `𝒪` be a discrete valuation ring which is complete for its maximal
ideal, and `L'` a finite separable extension of its fraction field.
Then the integral closure of `𝒪` in `L'` is finite over `𝒪`, is a
discrete valuation ring, and is complete for its maximal ideal.
-/

@[expose] public section

/-- The integral closure of a complete discrete valuation ring in a finite
separable extension of its fraction field is finite over the base, is a
discrete valuation ring, and is complete for its maximal ideal. -/
theorem integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (L : Type*) [Field L] [Algebra 𝒪 L] [IsFractionRing 𝒪 L]
    (L' : Type*) [Field L'] [Algebra 𝒪 L'] [Algebra L L'] [IsScalarTower 𝒪 L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L'] :
    Module.Finite 𝒪 (integralClosure 𝒪 L') ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L'),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L'))
        (integralClosure 𝒪 L') := by
  let _ : IsLocalRing (integralClosure 𝒪 L') :=
    IsIntegralClosure.isLocalRing_of_isAdicComplete 𝒪 L L' _
  let _ : IsDiscreteValuationRing (integralClosure 𝒪 L') :=
    IsIntegralClosure.isDiscreteValuationRing_of_isAdicComplete 𝒪 L L' _
  refine ⟨IsIntegralClosure.finite 𝒪 L L' _, inferInstance, ?_⟩
  exact IsIntegralClosure.isAdicComplete_of_isAdicComplete
    (A := 𝒪) (K := L) (L := L') (B := integralClosure 𝒪 L')
