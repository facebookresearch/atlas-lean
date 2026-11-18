/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Probability.RandomWalkFiniteGroup

/-!
# Random walks on finite groups: wishlist

Established results of Diaconis and Shahshahani whose proofs are deferred; the tools they rest on
(the upper bound lemma `MathlibExt.Probability.RandomWalkFiniteGroup.upper_bound_lemma` and the
transform of the random-transposition measure `fourier_randomTransposition`) are proved.

* `diaconis_shahshahani_upper`, `diaconis_shahshahani_lower`: random transpositions mix after
  `(1/2) n log n + c n` steps, and not before.

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
    ∃ b : ℝ, 0 < b ∧ ∀ n k : ℕ, 10 ≤ n →
      0 < ((k : ℝ) - n * Real.log n / 2) / n →
      2 * tvDist (convPow (randomTransposition n) k) (uniform (Equiv.Perm (Fin n))) ≤
        b * Real.exp (-2 * (((k : ℝ) - n * Real.log n / 2) / n))

/-- **Random transpositions: fewer than `(1/2) n log n` steps do not suffice
(Diaconis–Shahshahani).** For every choice of step numbers `k = k(n)`, with
`c = (k - (1/2) n log n) / n`, `‖T^{*k} - U‖ ≥ 2 (1/e - exp(-e^{-2c})) + o(1)` as `n → ∞`, in the
`ℓ¹` norm `‖·‖ = 2 ‖·‖_TV` (Diaconis and Shahshahani 1981, Theorem 2, proved there with the set
of permutations having a fixed point, an argument they credit to Charles Stein). -/
theorem_wanted diaconis_shahshahani_lower (k : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * (Real.exp (-1) - Real.exp (-Real.exp (-2 * (((k n : ℝ) - n * Real.log n / 2) / n))))
        - ε ≤ 2 * tvDist (convPow (randomTransposition n) (k n)) (uniform (Equiv.Perm (Fin n)))

end MathlibExt.Probability.RandomWalkFiniteGroupWanted
