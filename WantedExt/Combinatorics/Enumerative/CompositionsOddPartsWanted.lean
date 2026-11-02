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

/-- **Roots-of-unity partial fraction identity.** Let $\alpha < \beta$ be natural numbers and
let $\zeta = e^{2 \pi i / \beta}$. For every complex number $u$ with $1 - u^\beta \ne 0$,
$$\frac{u^\alpha}{1 - u^\beta} =
\frac{1}{\beta} \sum_{k=0}^{\beta - 1} \frac{\zeta^{-k \alpha}}{1 - \zeta^k u}.$$

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
