/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.FreeProbability.FreeCumulants
public import MathlibExt.Probability.FreeProbability.Freeness
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.Complex.Order

/-!
# Free probability: additivity of free cumulants and the free central limit theorem (wanted)

In a noncommutative probability space `(A, φ)`, free cumulants linearise free additive convolution:
if `a` and `b` are free then `κₙ(a + b) = κₙ(a) + κₙ(b)` for every `n ≥ 1`, so the R-transform is
additive (Anderson, Guionnet and Zeitouni (manuscript numbering), Lemma 5.3.21 and Corollary
5.3.23). As a consequence,
normalised sums of free, centred, unit-variance variables converge in moments to the semicircle law,
the free Gaussian: this is the free central limit theorem (Lemma 5.3.32), whose limit moments count
noncrossing pair partitions.

## Source

G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §5.3.2–5.3.4:
Lemma 5.3.21,
Corollary 5.3.23 and Lemma 5.3.32.
-/

@[expose] public section

open Filter Topology
open scoped ComplexOrder
open MathlibExt.Probability.FreeProbability NoncrossingPartition

namespace MathlibExt.Probability.FreeProbabilityWanted

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Free cumulants are additive for free variables** (Anderson, Guionnet and Zeitouni, *An
Introduction to Random Matrices*, Lemma 5.3.21). Let `(A, φ)` be a noncommutative probability space
(`φ` linear with `φ 1 = 1`) and let `a, b ∈ A` be free. Then for every `n ≥ 1` the `n`-th free
cumulant of `a + b` is the sum of those of `a` and `b`:
`κₙ(a + b) = κₙ(a) + κₙ(b)`, where `κₙ(x)` is the free cumulant of the moment sequence
`k ↦ φ (xᵏ)`. Equivalently the R-transform is additive, `R_{a+b} = R_a + R_b`
(Corollary 5.3.23). The source states it for bounded operators; its proof (multilinearity of the
cumulants and the vanishing of mixed cumulants, Theorem 5.3.15) is algebraic. -/
theorem_wanted freeCumulant_add_of_areFree (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a b : A)
    (hfree : AreFree φ ![a, b]) {n : ℕ} (hn : 1 ≤ n) :
    freeCumulant (fun k => φ ((a + b) ^ k)) n =
      freeCumulant (fun k => φ (a ^ k)) n + freeCumulant (fun k => φ (b ^ k)) n

/-- **The free central limit theorem** (Anderson, Guionnet and Zeitouni, *An Introduction to Random
Matrices*, Lemma 5.3.32). Let `(A, φ)` be a noncommutative probability space with a tracial state:
`φ` is linear, `φ 1 = 1`, `φ (x y) = φ (y x)` and `φ (x⋆ x) ≥ 0`. Let `a₀, a₁, …` be free
self-adjoint elements with `φ aᵢ = 0`, `φ (aᵢ²) = 1` and `sup_i |φ (aᵢᵏ)| < ∞` for every `k`.
Then `X_N = N^{-1/2} (a₀ + ⋯ + a_{N-1})` converges in moments to the standard semicircle law:
for every `p`, `φ (X_Nᵖ)` tends to the number of noncrossing pair partitions of `{1, …, p}`,
which is the `p`-th moment of the semicircle law. -/
theorem_wanted free_central_limit [StarRing A] [StarModule ℂ A] (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1)
    (htrace : ∀ x y, φ (x * y) = φ (y * x)) (hpos : ∀ x, 0 ≤ φ (star x * x))
    (a : ℕ → A) (hfree : AreFree φ a) (hsa : ∀ i, IsSelfAdjoint (a i))
    (hmean : ∀ i, φ (a i) = 0) (hvar : ∀ i, φ (a i ^ 2) = 1)
    (hbdd : ∀ k : ℕ, ∃ C : ℝ, ∀ i, ‖φ (a i ^ k)‖ ≤ C) (p : ℕ) :
    Tendsto (fun N : ℕ => φ (((((Real.sqrt N)⁻¹ : ℝ) : ℂ) • ∑ i ∈ Finset.range N, a i) ^ p))
      atTop (𝓝 (Fintype.card {P : _root_.NoncrossingPartition p // IsPairPartition P.val} : ℂ))

end MathlibExt.Probability.FreeProbabilityWanted
