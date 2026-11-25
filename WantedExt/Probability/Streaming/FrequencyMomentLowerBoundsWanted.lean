/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Streaming.MaxFreqLowerBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Space lower bounds for approximating frequency moments

N. Alon, Y. Matias and M. Szegedy ("The space complexity of approximating the frequency moments",
J. Comput. System Sci. 58 (1999) 137–147, Section 3) prove that approximating the largest
multiplicity `F*_∞` needs linear space and that approximating `F_k` for `k ≥ 6` needs
`n^{1 - 5/k}` space, by turning a streaming algorithm into a communication protocol for set
disjointness: the memory content is the message. Both bounds use the model of
`MathlibExt.Probability.Streaming.StreamingAlgorithm`, in which the random seed is not charged to
the memory. That makes the statements at least as strong as the source's, and they remain true:
the source's reductions use the seed only as the public coin of the communication protocol, and
the communication lower bounds they rely on hold against arbitrary public randomness (the
public-coin disjointness bound for Proposition 3.1, a distributional argument for Proposition 3.3).
The module documentation of `StreamingAlgorithm` gives the two reductions.
-/

@[expose] public section

namespace MathlibExt.Probability.Streaming

/-- **Polynomial space for approximating `F_k`, `k ≥ 6`.** For every fixed integer `k > 5` and
every `0 < γ < 1/2` there is `c > 0` such that every randomized streaming algorithm over `Fin n`
with `s` bits of memory that, on every stream of at most `n` elements, outputs `Z` with
`|Z - F_k| > 0.1 F_k` with probability less than `γ` uses `s ≥ c n^{1 - 5/k}` bits (N. Alon,
Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), Theorem 3.2, via the multiparty
unique-intersection game of Proposition 3.3). The seed is not charged to the memory. This is
harmless because Proposition 3.3 is proved against a fixed input distribution: after amplification
by independent copies and averaging over that distribution, one seed can be fixed, which gives a
deterministic protocol to which the distributional bound applies, whatever the size of the seed
space. -/
theorem_wanted space_lower_bound_freqMoment :
    ∀ k : ℕ, 5 < k → ∀ γ : ℝ, 0 < γ → γ < 1 / 2 → ∃ c : ℝ, 0 < c ∧
      ∀ (n s : ℕ) (R : Type) [Fintype R] [Nonempty R] (A : StreamingAlgorithm (Fin n) R s),
        (∀ l : List (Fin n), l.length ≤ n →
          A.failProb (fun l z => |z - freqMoment k l| ≤ 0.1 * (freqMoment k l : ℝ)) l < γ) →
        c * (n : ℝ) ^ (1 - 5 / (k : ℝ)) ≤ s

end MathlibExt.Probability.Streaming
