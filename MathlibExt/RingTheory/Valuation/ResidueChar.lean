/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_charP_residueField_of_liesOverPrime.lean` and
`P2M/Sol/S_ValuationSubring_charP_residueField_of_liesOverPrime.lean`
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
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import MathlibExt.RingTheory.Valuation.LiesOverPrime
public import MathlibExt.RingTheory.LocalRing.CharP

/-!
# Characteristic of the residue field at a place above a prime

If a valuation subring of a field lies over a rational prime `ℓ`, then `ℓ`
lies in its maximal ideal, so its residue field has characteristic `ℓ`.
-/

@[expose] public section

/-- If a valuation subring `A` of a field lies over the prime `ℓ`, its
residue field has characteristic `ℓ`. -/
public theorem ValuationSubring.charP_residueField_of_liesOverPrime
    {L : Type*} [Field L] (A : ValuationSubring L) (ℓ : ℕ) [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) : CharP (IsLocalRing.ResidueField A) ℓ := by
  have hmem : (ℓ : A) ∈ IsLocalRing.maximalIdeal A := by
    have h : (ℓ : L) ∈ A.nonunits := hA
    have h2 : ((ℓ : A) : L) ∈ A.nonunits := by
      have hcast : ((ℓ : A) : L) = (ℓ : L) := by simp
      rwa [hcast]
    exact ValuationSubring.coe_mem_nonunits_iff.mp h2
  exact IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A ℓ hmem
