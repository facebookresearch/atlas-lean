/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_
forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport.lean`
and
`P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_
forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport.lean`
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

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import MathlibExt.Analysis.Normed.Field.UltrametricOpenSubgroup

@[expose] public section

open NumberField IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

/-- A compactly supported locally constant function on the square of a
`v`-adic completion is invariant in its first coordinate under a common
open subgroup of units. This is the number-field form of the general
ultrametric result; no vanishing on the axes is needed. -/
public theorem exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Φ : (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧
      ∀ t ∈ U, ∀ b z : v.adicCompletion K, Φ (b * (t : v.adicCompletion K), z) = Φ (b, z) :=
  @IsLocallyConstant.exists_isOpen_subgroup_forall_apply_mul_eq_of_hasCompactSupport
    (v.adicCompletion K) (v.adicCompletion K) ℂ _ _ _ _ _ _ Φ hΦ hΦc

end IsDedekindDomain.HeightOneSpectrum
