/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lincoln–Petersen and Chapman capture–recapture estimators

In a closed population of `N` animals, `n₁` are captured and marked; a second, independent
sample of `n₂` animals, each subset of size `n₂` equally likely, contains `m` marked animals. Then
`m` is hypergeometric:
`P(m = k) = C(n₁, k) C(N - n₁, n₂ - k) / C(N, n₂)`. The Lincoln–Petersen estimate `n₁ n₂ / m` is
undefined (infinite) when `m = 0`, which has positive probability exactly when `n₁ + n₂ ≤ N`.
Chapman's estimate `(n₁ + 1)(n₂ + 1)/(m + 1) - 1` is always defined, and its expectation is
`N - (N + 1) C(N - n₁, n₂ + 1) / C(N + 1, n₂ + 1)`; so it is exactly unbiased when `n₁ + n₂ ≥ N`
and strictly biased downward when `n₁ + n₂ < N`.

The hypergeometric moments are proved in `MathlibExt.Probability.Distributions.Hypergeometric`.
Chapman's exact results are derived here from the hypergeometric law.

Sources: D. G. Chapman, "Some properties of the hypergeometric distribution with applications
to zoological sample censuses", Univ. California Publ. Statist. 1 (1951) 131–160; F. C. Lincoln,
"Calculating waterfowl abundance on the basis of banding returns", U.S. Dept. Agric. Circ. 118
(1930); C. G. J. Petersen, Rep. Danish Biol. Stn. 6 (1896) 1–48.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.Powerset
public import MathlibExt.Probability.Distributions.Hypergeometric

@[expose] public section

namespace WantedExt.Biology.Ecology.CaptureRecaptureWanted

open ProbabilityTheory

/-- Chapman's estimate `(n₁ + 1)(n₂ + 1)/(m + 1) - 1`. -/
noncomputable def chapman (n₁ n₂ m : ℕ) : ℝ :=
  ((n₁ : ℝ) + 1) * ((n₂ : ℝ) + 1) / ((m : ℝ) + 1) - 1

/-- **The recapture count is hypergeometric** (Chapman 1951). Let a population `Fin N` contain a
marked set `A` of size `n₁`, and let the second sample be a uniformly random subset of size
`n₂ ≤ N`. For every `k`, the proportion of `n₂`-subsets `S` with `#(S ∩ A) = k` is
`hypergeometricReal N n₁ n₂ k = C(n₁, k) C(N - n₁, n₂ - k) / C(N, n₂)`.

Sources: Chapman (1951). -/
public theorem_wanted card_filter_inter_eq {N n₁ n₂ : ℕ} (A : Finset (Fin N)) (hA : A.card = n₁)
    (hn₂ : n₂ ≤ N) (k : ℕ) :
    (((Finset.univ : Finset (Fin N)).powersetCard n₂).filter fun S => (S ∩ A).card = k).card /
        (N.choose n₂ : ℝ) = hypergeometricReal N n₁ n₂ k

/-- **Expectation of Chapman's estimate** (Chapman 1951; derived). For `n₁ ≤ N` and `n₂ ≤ N`,
with `m` hypergeometric,
`E[(n₁ + 1)(n₂ + 1)/(m + 1) - 1] = N - (N + 1) C(N - n₁, n₂ + 1) / C(N + 1, n₂ + 1)`.

Sources: Chapman (1951); derived. -/
public theorem_wanted expectation_chapman {N n₁ n₂ : ℕ} (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N) :
    ∑ k ∈ Finset.range (n₂ + 1), hypergeometricReal N n₁ n₂ k * chapman n₁ n₂ k =
      N - (N + 1) * ((N - n₁).choose (n₂ + 1) : ℝ) / ((N + 1).choose (n₂ + 1) : ℝ)

/-- **Exact unbiasedness and strict bias of Chapman's estimate** (Chapman 1951; derived). For
`n₁ ≤ N` and `n₂ ≤ N`, with `m` hypergeometric: if `n₁ + n₂ ≥ N` then
`E[(n₁ + 1)(n₂ + 1)/(m + 1) - 1] = N`, and if `n₁ + n₂ < N` then this expectation is strictly less
than `N`.

Sources: Chapman (1951); derived. -/
public theorem_wanted chapman_unbiased_iff {N n₁ n₂ : ℕ} (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N) :
    (N ≤ n₁ + n₂ →
        ∑ k ∈ Finset.range (n₂ + 1), hypergeometricReal N n₁ n₂ k * chapman n₁ n₂ k = N) ∧
      (n₁ + n₂ < N →
        ∑ k ∈ Finset.range (n₂ + 1), hypergeometricReal N n₁ n₂ k * chapman n₁ n₂ k < N)

/-- **When the Lincoln–Petersen estimate is undefined** (Chapman 1951; derived). For `n₁ ≤ N` and
`n₂ ≤ N`, the probability `P(m = 0)` that the second sample contains no marked animal, where the
Lincoln–Petersen estimate `n₁ n₂ / m` is infinite, is positive if and only if `n₁ + n₂ ≤ N`.

Sources: Chapman (1951); derived. -/
public theorem_wanted hypergeometricReal_zero_pos_iff {N n₁ n₂ : ℕ} (hn₁ : n₁ ≤ N)
    (hn₂ : n₂ ≤ N) :
    0 < hypergeometricReal N n₁ n₂ 0 ↔ n₁ + n₂ ≤ N

end WantedExt.Biology.Ecology.CaptureRecaptureWanted
