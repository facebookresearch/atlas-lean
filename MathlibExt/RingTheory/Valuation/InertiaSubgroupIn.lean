/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FLTPrelim_Ramification.lean`
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
framework; the statement is reused here with that machinery removed and
the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The inertia subgroup in the full automorphism group

Mathlib defines the inertia subgroup of a valuation subring `A` of `L` as a
subgroup of the decomposition subgroup of `A`. This file views it as a
subgroup of the full `K`-algebra automorphism group of `L`.
-/

@[expose] public section

namespace ValuationSubring

variable {L : Type*} [Field L]

variable (K : Type*) [Field K] [Algebra K L]

/-- The inertia subgroup of a valuation subring, viewed as a subgroup of
the full `K`-algebra automorphism group of `L`. -/
noncomputable def inertiaSubgroupIn (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring
