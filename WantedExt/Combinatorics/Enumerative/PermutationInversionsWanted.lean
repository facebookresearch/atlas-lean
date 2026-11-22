/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.PermutationInversions
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Inversions of a permutation: wanted results

* `sum_X_pow_permInversionCount`: the generating function of inversions,
  `∑_{σ ∈ S_n} q ^ inv(σ) = (1 + q)(1 + q + q ^ 2) ⋯ (1 + q + ⋯ + q ^ (n - 1))` (Stanley,
  *Enumerative Combinatorics*, Vol. 1, 2nd ed., Corollary 1.3.13, equation (1.30)). Stanley's
  proof goes through the inversion table (Proposition 1.3.12), which is not formalized here.
-/

@[expose] public section

open Polynomial

namespace MetaMathlibExt

/-- **Generating function of inversions** (Stanley, *Enumerative Combinatorics*, Vol. 1,
2nd ed., Corollary 1.3.13, equation (1.30)). For every `n`, the polynomial
`∑_{σ ∈ S_n} q ^ inv(σ)` over the permutations of `Fin n` is
`∏_{k = 0}^{n - 1} (1 + q + ⋯ + q ^ k) = (1 + q)(1 + q + q ^ 2) ⋯ (1 + q + ⋯ + q ^ (n - 1))`. -/
theorem_wanted sum_X_pow_permInversionCount (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n), (X : ℕ[X]) ^ permInversionCount σ =
      ∏ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), (X : ℕ[X]) ^ i

end MetaMathlibExt
