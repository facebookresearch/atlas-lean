/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace MetaMathlibExt

@[expose] public section

/-- The partial-fraction (roots-of-unity filter) identity
`u ^ α / (1 - u ^ β) = (1 / β) ∑_{k < β} ζ ^ (-k α) / (1 - ζ ^ k u)`
with `ζ = e ^ (2πi / β)`, for `0 ≤ α < β` and `1 - u ^ β ≠ 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 7 (`jis-2024-24.3.6-lem-7`). -/
public theorem_wanted pow_div_one_sub_pow_eq_sum (α β : ℕ) (hα : α < β)
    (u : ℂ) (hu : 1 - u ^ β ≠ 0) :
    u ^ α / (1 - u ^ β)
      = (1 / (β : ℂ)) * ∑ k ∈ Finset.range β,
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ (-((k : ℤ) * (α : ℤ)))
            / (1 - (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ k * u)

end

end MetaMathlibExt
