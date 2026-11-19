/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.Summation
public import MathlibExt.Biology.PopulationGenetics.Inference.Numerics.FloatLoglik
import Mathlib.Algebra.BigOperators.Fin

/-!
# Enclosure of a rounded log-likelihood sum

This instantiates the elementary enclosure in
`MathlibExt.Biology.PopulationGenetics.Inference.Numerics.FloatLoglik` with
the existing recursive summation `rsum`. For `1 ≤ p`, `rsum p` is binary
round-to-nearest, ties-to-even, unbounded-exponent summation. The enclosure
inequality also holds at `p = 0`, but that case is only the formal extension
of `fl` from `Summation`, not a zero-bit floating-point format.

For computed site log-likelihoods `lhat i` with supplied per-site errors
`|lhat i - l i| ≤ δ i`, the rounded recursive sum differs from the exact total
by at most

`((1 + u) ^ n - 1) * ∑ i, |lhat i| + ∑ i, δ i`,

where `u = unitRoundoff p = 2 ^ (-p)`.

## Main result

* `abs_rsum_sub_sum_le`: the rounded-sum enclosure.

## References

* N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
  SIAM (2002), ch. 2.
-/

@[expose] public section

namespace Cslib.Bioinformatics.PopulationGenetics.FloatLoglik

open Cslib.Algorithms.Lean.Numerical.Summation

/-- **Certified enclosure for a rounded recursive log-likelihood sum.** If
`|lhat i - l i| ≤ δ i` for every site, then the rounded recursive sum of the
computed values `lhat` differs from the exact total `∑ i, l i` by at most the
rounded-summation bound plus the total supplied per-site error. The bound is
stated for every `p`; its binary floating-point interpretation is for
`1 ≤ p`, while `p = 0` is only the formal extension from `Summation`. -/
theorem abs_rsum_sub_sum_le (p : ℕ) {n : ℕ} (l lhat δ : Fin n → ℝ)
    (hsite : ∀ i, |lhat i - l i| ≤ δ i) :
    |rsum p (List.ofFn lhat) - ∑ i, l i| ≤
      ((1 + unitRoundoff p) ^ n - 1) * (∑ i, |lhat i|) + ∑ i, δ i := by
  refine MathlibExt.Biology.PopulationGenetics.Inference.Numerics.abs_sub_sum_le_enclosure
    l lhat δ _ _ hsite ?_
  have h := rsum_abs_sub_le p (List.ofFn lhat)
  simpa [Fin.sum_ofFn, List.length_ofFn, List.map_ofFn, Function.comp_def] using h

end Cslib.Bioinformatics.PopulationGenetics.FloatLoglik
