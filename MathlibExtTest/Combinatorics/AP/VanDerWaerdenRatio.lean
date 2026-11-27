/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/138.lean` (Formal Conjectures):
Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Combinatorics.AP.VanDerWaerdenRatio

@[expose] public section

/-!
# Tests for `MathlibExt.Combinatorics.AP.VanDerWaerdenRatio`

The first test is the source-faithfulness check: the statement of
`FormalConjectures/ErdosProblems/138.lean`'s `erdos_138.variants.dvd_two_pow`, written out
verbatim, is proved by this library's declaration.
-/

namespace MathlibExtTest.Combinatorics.AP.VanDerWaerdenRatio

open Filter Erdos138

-- Source faithfulness: the Formal Conjectures statement, verbatim.
example : atTop.Tendsto (fun k => ((W k : ℚ) / (2 ^ k))) atTop :=
  erdos_138.variants.dvd_two_pow

-- The `Prop` abbreviation really is that statement.
example :
    erdos_138_variants_dvd_two_pow_statement =
      atTop.Tendsto (fun k => ((W k : ℚ) / (2 ^ k))) atTop := rfl

-- `W k` is the two-colour van der Waerden number: it is the infimum of the guarantee set.
example (k : ℕ) : W k = sInf (monoAP_guarantee_set 2 k) := rfl

-- The guarantee set for length `0` already contains `0`.
example : (0 : ℕ) ∈ monoAP_guarantee_set 2 0 := zero_mem_monoAP_guarantee_set_zero

end MathlibExtTest.Combinatorics.AP.VanDerWaerdenRatio
