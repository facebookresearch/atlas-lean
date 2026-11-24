/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/337.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.Combinatorics.Additive.RuzsaTurjanyi

@[expose] public section

/-!
# Tests for `MathlibExt.Combinatorics.Additive.RuzsaTurjanyi`
-/

namespace MathlibExtTest.Combinatorics.Additive.RuzsaTurjanyi

open Filter Set Asymptotics Erdos337
open scoped Pointwise

-- Source faithfulness: the Formal Conjectures statement
-- `Erdos337.erdos_337.variants.ruzsa_turjanyi`, verbatim.
example :
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop :=
  erdos_337.variants.ruzsa_turjanyi

-- `ℕ` itself is an asymptotic additive basis of order `1`, so the hypothesis is satisfiable
-- (its density hypothesis is not, which is what makes the theorem non-vacuous elsewhere).
example : (Set.univ : Set ℕ).IsAsymptoticAddBasisOfOrder 1 := by
  simp [Set.IsAsymptoticAddBasisOfOrder]

end MathlibExtTest.Combinatorics.Additive.RuzsaTurjanyi
