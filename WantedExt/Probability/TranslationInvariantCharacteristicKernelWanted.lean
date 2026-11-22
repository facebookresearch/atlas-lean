/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Support
public import MathlibExt.Probability.KernelMeanEmbedding

/-!
# Characteristic translation-invariant kernels on `ℝ^d`

A bounded continuous translation-invariant kernel `k(x, y) = ψ(x - y)` on `ℝ^d` is the Fourier
transform of a finite nonnegative Borel measure `Λ` by Bochner's theorem,
`ψ(x) = ∫ exp(-i xᵀω) dΛ(ω)`. Sriperumbudur, Gretton, Fukumizu, Schölkopf and Lanckriet showed
that such a kernel is characteristic (its kernel mean embedding is injective on Borel probability
measures) exactly when `Λ` has full support. This covers the Gaussian, Laplacian and `B_{2n+1}`
spline kernels, whose spectra have full support, and excludes periodic kernels and the sinc
kernel, whose spectra do not. For sufficiency the proof writes the squared MMD as
`∫ |φ_P(ω) - φ_Q(ω)|² dΛ(ω)` in terms of the characteristic functions of `P` and `Q`
(Corollary 4(i)) and uses their uniqueness; for necessity it constructs `P ≠ Q` with equal
embeddings when `Λ` misses an open set (Lemma 16). Neither step is in Mathlib or the repository.

For a bounded continuous kernel every Borel probability measure has a Bochner integrable feature
map, so `KernelMeanEmbedding.IsCharacteristic` (injectivity on probability measures with
integrable feature map) is the paper's notion here. The dimension is `d ≥ 1`: on the one-point
space `ℝ^0` every kernel is characteristic, while the zero measure has empty support.

Reference: B. K. Sriperumbudur, A. Gretton, K. Fukumizu, B. Schölkopf and G. R. G. Lanckriet,
"Hilbert space embeddings and metrics on probability measures", *J. Mach. Learn. Res.* **11**
(2010), 1517–1561, Theorem 9 (with Assumption 1 and equation (11)).
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.KernelMeanEmbedding
open scoped InnerProductSpace

namespace MathlibExt.Probability.TranslationInvariantCharacteristicKernelWanted

/-- **Characterization of characteristic translation-invariant kernels** (Sriperumbudur,
Gretton, Fukumizu, Schölkopf and Lanckriet, *Hilbert space embeddings and metrics on probability
measures*, JMLR 11 (2010), Theorem 9). Let `d ≥ 1` and let `H` be a real RKHS on `ℝ^d`
whose kernel is `k(x, y) = ψ(x - y)` with `ψ(x) = ∫ exp(-i xᵀω) dΛ(ω)` for a finite Borel
measure `Λ`, so that `ψ` is a bounded continuous real positive-definite function
(equation (11)). Then `k` is characteristic if and only if the support of `Λ` is all of
`ℝ^d`. -/
theorem_wanted isCharacteristic_iff_support_eq_univ {d : ℕ} (hd : 0 < d) {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H (EuclideanSpace ℝ (Fin d)) ℝ]
    (Λ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure Λ]
    (hk : ∀ x y : EuclideanSpace ℝ (Fin d), (kernelValue H x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I) ∂Λ) :
    IsCharacteristic H ↔ Λ.support = Set.univ

end MathlibExt.Probability.TranslationInvariantCharacteristicKernelWanted
