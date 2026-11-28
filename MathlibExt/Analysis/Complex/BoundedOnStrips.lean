/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LanglandsTunnell_HonestLDatum.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.Analysis.Complex.Basic

/-!
# Functions bounded on vertical strips

`Complex.BoundedOnStrips Λ` says that `Λ : ℂ → ℂ` is bounded on every vertical strip
$a \le \operatorname{Re} s \le b$.
-/

@[expose] public section

namespace Complex

/-- A function is bounded on every vertical strip. -/
def BoundedOnStrips (Λ : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ C

end Complex
