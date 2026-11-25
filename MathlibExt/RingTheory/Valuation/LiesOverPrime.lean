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

public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Valuation subrings lying over a rational prime

A valuation subring lies over a rational prime `q` when `q`, viewed in the
ambient field, is a nonunit of the subring.
-/

@[expose] public section

namespace ValuationSubring

variable {L : Type*} [Field L]

/-- A valuation subring of `L` lies over the rational prime `q` when `q`,
viewed in `L`, is a nonunit of the subring. -/
def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

end ValuationSubring
