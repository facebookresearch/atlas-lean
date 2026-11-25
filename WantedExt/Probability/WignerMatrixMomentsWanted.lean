/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Distributions.Semicircle
public import MathlibExt.Probability.FunctionalInequalities.LogSobolevTalagrand
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

/-!
# The two halves of the moment method for Wigner matrices (wanted)

Anderson, Guionnet and Zeitouni prove Wigner's theorem (their Theorem 2.1.1) by the moment method
in two steps: the expected moments `𝔼 ⟨L_N, xᵏ⟩ = N⁻¹ 𝔼 tr X_Nᵏ` of the empirical spectral measure
converge to the moments of the semicircle law (Lemma 2.1.6, proved by counting Wigner words, which
correspond to noncrossing pair partitions), and the fluctuations around the mean vanish
(Lemma 2.1.7). For entries satisfying a logarithmic Sobolev inequality the fluctuations are in fact
exponentially small at scale `N²` (Theorem 2.3.5, the Guionnet–Zeitouni concentration inequality).

## Source

G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §2.1 (the Wigner
matrices
(2.1.1)–(2.1.2), Lemma 2.1.6) and §2.3.3 (Theorem 2.3.5); A. Guionnet and O. Zeitouni,
"Concentration of the spectral measure for large matrices", *Electron. Comm. Probab.* 5 (2000),
119–136, as reproduced in A. Guionnet, *Probability Surveys* 1 (2004), Theorem 3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.LogSobolevTalagrand

namespace MathlibExt.Probability.WignerMatrixMomentsWanted

/-- **Normalised real Wigner matrix** `X_N(i, j) = Z_{min(i,j), max(i,j)} / √N` built from the
upper-triangular array `Z : ℕ → ℕ → Ω → ℝ` (Anderson, Guionnet and Zeitouni, (2.1.2), where the
diagonal entries are called `Yᵢ / √N`). -/
noncomputable def wignerMatrixReal {Ω : Type*} (Z : ℕ → ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => Z (min (i : ℕ) j) (max (i : ℕ) j) ω / Real.sqrt N

/-- **Expected moments of a Wigner matrix converge to the semicircle moments** (Anderson, Guionnet
and Zeitouni, *An Introduction to Random Matrices* (manuscript numbering), Lemma 2.1.6). Let the
entries `Z i j`
(`i ≤ j`) be independent, with the off-diagonal entries (`i < j`) identically distributed, the
diagonal entries identically distributed, all centred, the off-diagonal ones of variance `1`, and
all of finite moments of every order (the assumptions (2.1.1) of the source). Then for every `k`,
`𝔼 [N⁻¹ tr X_Nᵏ] → ∫ xᵏ dσ(x)`, the `k`-th moment of the semicircle law, which is the number of
noncrossing pair partitions of `{1, …, k}`. -/
theorem_wanted tendsto_expected_moment_wignerMatrixReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ i j, i ≤ j → Measurable (Z i j))
    (hindep : iIndepFun (fun p : {p : ℕ × ℕ // p.1 ≤ p.2} => Z p.1.1 p.1.2) P)
    (hoff : ∀ i j i' j', i < j → i' < j' → IdentDistrib (Z i j) (Z i' j') P P)
    (hdiag : ∀ i i', IdentDistrib (Z i i) (Z i' i') P P)
    (hmom : ∀ i j, i ≤ j → ∀ k : ℕ, Integrable (fun ω => Z i j ω ^ k) P)
    (hmean : ∀ i j, i ≤ j → ∫ ω, Z i j ω ∂P = 0)
    (hvar : ∀ i j, i < j → ∫ ω, Z i j ω ^ 2 ∂P = 1) (k : ℕ) :
    Tendsto (fun N : ℕ => ∫ ω, (N : ℝ)⁻¹ * Matrix.trace (wignerMatrixReal Z N ω ^ k) ∂P)
      atTop (𝓝 (∫ x, x ^ k ∂semicircleReal))

/-- **Symmetric matrix of an upper-triangular array**: the real symmetric `N × N` matrix with
upper-triangular entries `X i j` (`i ≤ j`), as a complex matrix so that Mathlib's spectral theorem
for Hermitian matrices gives its eigenvalues. -/
noncomputable def symmetricMatrix {Ω : Type*} {N : ℕ} (X : Fin N → Fin N → Ω → ℝ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((X (min i j) (max i j) ω : ℝ) : ℂ)

/-- **The symmetric matrix of an array is Hermitian.** -/
theorem symmetricMatrix_isHermitian {Ω : Type*} {N : ℕ} (X : Fin N → Fin N → Ω → ℝ) (ω : Ω) :
    (symmetricMatrix X ω).IsHermitian := by
  ext i j
  simp [symmetricMatrix, Matrix.conjTranspose_apply, min_comm i j, max_comm i j]

/-- **Concentration of linear spectral statistics** (Anderson, Guionnet and Zeitouni, *An
Introduction to Random Matrices*, Theorem 2.3.5, inequality (2.3.9); Guionnet and Zeitouni 2000).
Let the entries `X i j` (`i ≤ j`) of a real symmetric `N × N` random matrix be independent, and let
the law of each satisfy the logarithmic Sobolev inequality with constant `c / N` in the source's
normalisation, `Ent(f²) ≤ 2 (c/N) ∫ |f'|²` (this is `SatisfiesLogSobolev` with `α = N / c`). Then
for every `L`-Lipschitz `f : ℝ → ℝ` and `δ > 0`,
`P(|tr f(X_N) - 𝔼 tr f(X_N)| ≥ δ N) ≤ 2 exp(-N² δ² / (4 c L²))`,
where `tr f(X_N) = ∑ᵢ f(λᵢ)` over the eigenvalues. -/
theorem_wanted concentration_trace_lipschitz {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : 0 < c)
    (X : Fin N → Fin N → Ω → ℝ) (hmeas : ∀ i j, i ≤ j → Measurable (X i j))
    (hindep : iIndepFun (fun p : {p : Fin N × Fin N // p.1 ≤ p.2} => X p.1.1 p.1.2) P)
    (hLSI : ∀ i j, i ≤ j → SatisfiesLogSobolev (P.map (X i j)) (N / c))
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzWith L f) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | δ * N ≤ |∑ i, f ((symmetricMatrix_isHermitian X ω).eigenvalues i) -
        ∫ ω', ∑ i, f ((symmetricMatrix_isHermitian X ω').eigenvalues i) ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-(N : ℝ) ^ 2 * δ ^ 2 / (4 * c * (L : ℝ) ^ 2)))

end MathlibExt.Probability.WignerMatrixMomentsWanted
