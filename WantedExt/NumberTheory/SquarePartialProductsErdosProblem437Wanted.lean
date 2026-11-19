/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Square partial products of increasing sequences (Erdős Problem 437)

Erdős Problem 437: let `1 ≤ a₁ < ⋯ < a_k ≤ x`. How many of the partial products `a₁, a₁a₂, …, a₁ ⋯
a_k` can be squares? For every `ε > 0`, can there be more than `x^{1-ε}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.SquarePartialProductsErdosProblem437Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #437, https://www.erdosproblems.com/437 (status
PROVED). UnsolvedMath record UM-30006868 (`EP-437`), dataset ulamai/UnsolvedMath v1.8.0.

The second question is the target: for every `ε > 0` and all large integers `x` some sequence has
more than `x^{1-ε}` square partial products; the first (how many can be squares) is not stated. The
sequence is `a 0 < ⋯ < a (k - 1)`. Compared with the formal-conjectures statement
`ErdosProblems/437.lean` (equivalent; no code imported).
-/

/-- The number of partial products `a 0, a 0 * a 1, …, a 0 * ⋯ * a (k - 1)` that are perfect
squares. -/
def squarePartialProductCount (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun j => IsSquare (∏ i ∈ Finset.range (j + 1), a i)).card

/-- Erdős Problem 437: for every `ε > 0` and all large `x`, some `1 ≤ a₁ < ⋯ < a_k ≤ x` have more
than `x ^ (1 - ε)` partial products `a₁ ⋯ a_j` that are perfect squares. -/
def manySquarePartialProducts : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop, ∃ k : ℕ, ∃ a : ℕ → ℕ,
    StrictMonoOn a (Set.Iio k) ∧ (∀ i < k, 1 ≤ a i ∧ a i ≤ x) ∧
      (x : ℝ) ^ (1 - ε) < squarePartialProductCount a k

/--
Resolved true: Tao showed, from work of Bui, Pratt and Zaharescu, that the maximal number `L(x)` of
square partial products satisfies `L(x) ≥ x exp(-(√2 + o(1)) (log x log log x)^{1/2})`, which
exceeds `x^{1 - ε}` for large `x`; erdosproblems.com/437 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #437, https://www.erdosproblems.com/437 (status PROVED); resolution:
H. M. Bui, K. Pratt and A. Zaharescu, A problem of Erdős-Graham-Granville-Selfridge on integral
points on hyperelliptic curves, Math. Proc. Cambridge Philos. Soc. (2024), 309-323; T. Tao, A result
of Bui-Pratt-Zaharescu, and Erdős problem #437 (blog post, 2024), L(x) ≥ x exp(-(√2 + o(1)) (log x
log log x)^{1/2}) (erdosproblems.com/437),
https://terrytao.wordpress.com/2024/08/09/a-result-of-bui-pratt-zaharescu-and-erdos-problem-437/.
-/
public theorem_wanted manySquarePartialProducts_holds : manySquarePartialProducts

end MathlibExt.NumberTheory.SquarePartialProductsErdosProblem437Wanted
