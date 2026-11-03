/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal.lean` and
`P2M/Sol/S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal.lean`
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

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Basic

/-!
# Characteristic of a residue field

If a prime `p` lies in the maximal ideal of a local ring, the residue field
has characteristic `p`.
-/

@[expose] public section

/-- If `(p : A)` lies in the maximal ideal of a local ring `A`, the residue
field has characteristic `p`: `p` maps to zero in the residue field. -/
theorem IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal
    (A : Type*) [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    CharP (IsLocalRing.ResidueField A) p := by
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hAp
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h0
