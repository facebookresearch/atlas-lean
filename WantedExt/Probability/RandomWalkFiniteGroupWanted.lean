/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Probability.RandomTranspositionLower

/-!
# Random walks on finite groups: wishlist

The upper cutoff estimate for random transpositions is deferred. Its Fourier-analytic tools
(the upper bound lemma `MathlibExt.Probability.RandomWalkFiniteGroup.upper_bound_lemma` and the
transform of the random-transposition measure `fourier_randomTransposition`) are proved.
The lower bound `diaconis_shahshahani_lower` is in the imported proved module.

The Bayer–Diaconis formula for riffle shuffles is proved:
`MathlibExt.Probability.RiffleShuffle.card_sort_eq`.

Conventions. Diaconis and Shahshahani's `‖·‖` is the `ℓ¹` norm, twice the total variation distance
`MathlibExt.Probability.MarkovMixing.tvDist`; the Saint-Flour notes use total variation.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.Probability.RandomWalkFiniteGroupWanted

open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (convPow)
open MathlibExt.Probability.RandomWalkFiniteGroup (uniform randomTransposition)
open MathlibExt.Probability.MarkovMixing (tvDist)

/-- **Random transpositions: `(1/2) n log n + c n` steps suffice (Diaconis–Shahshahani).** There
is a constant `b > 0` such that for all `n ≥ 10` and all `k` with
`c = (k - (1/2) n log n) / n > 0`, the law `T^{*k}` of `k` random transpositions satisfies
`‖T^{*k} - U‖ ≤ b e^{-2c}` in the `ℓ¹` norm `‖·‖ = 2 ‖·‖_TV` (Diaconis and Shahshahani 1981,
Theorem 1 with (1.1)–(1.4); the constant is universal, Section 3 and Remark 1 of Section 5 compute
it explicitly). -/
theorem_wanted diaconis_shahshahani_upper :
    ∃ b : ℝ, 0 < b ∧ ∀ (n k : ℕ) [NeZero n], 10 ≤ n →
      0 < ((k : ℝ) - n * Real.log n / 2) / n →
      2 * tvDist (convPow (randomTransposition n) k) (uniform (Equiv.Perm (Fin n))) ≤
        b * Real.exp (-2 * (((k : ℝ) - n * Real.log n / 2) / n))

end MathlibExt.Probability.RandomWalkFiniteGroupWanted
