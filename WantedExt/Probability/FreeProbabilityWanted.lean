/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.FreeProbability.CentralLimit
public import MathlibExt.Probability.FreeProbability.FreeCumulants
public import MathlibExt.Probability.FreeProbability.Freeness
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Analysis.Complex.Order

/-!
# Additivity of free cumulants (wanted)

In a noncommutative probability space `(A, φ)`, free cumulants linearise free additive convolution:
if `a` and `b` are free then `κₙ(a + b) = κₙ(a) + κₙ(b)` for every `n ≥ 1`, so the R-transform is
additive (Anderson, Guionnet and Zeitouni (manuscript numbering), Lemma 5.3.21 and Corollary
5.3.23).

## Source

G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §5.3.2:
Lemma 5.3.21 and Corollary 5.3.23.
-/

@[expose] public section

open MathlibExt.Probability.FreeProbability

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
    (hfree : AreFree φ hφ ![a, b]) {n : ℕ} (hn : 1 ≤ n) :
    freeCumulant (fun k => φ ((a + b) ^ k)) n =
      freeCumulant (fun k => φ (a ^ k)) n + freeCumulant (fun k => φ (b ^ k)) n

end MathlibExt.Probability.FreeProbabilityWanted
