/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.lean`
and
`P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.lean`
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

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
import MathlibExt.RingTheory.DedekindDomain.AdicCompletionResidueField

/-!
# Finiteness of the residue field of adic completion integers

At a place of a Dedekind domain with finite residue field, the residue
field of the adic completion integers is finite.
-/

@[expose] public section

universe u v

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

/-- The residue field of the adic completion integers at a place with finite
residue field is finite. -/
theorem finite_residueField_adicCompletionIntegers (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  Finite.of_equiv (R ⧸ v.asIdeal)
    (v.completionResidueFieldEquiv (K := K)).symm.toEquiv

end IsDedekindDomain.HeightOneSpectrum
