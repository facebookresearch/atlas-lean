/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Grone-Merris conjecture (AIM spectra of matrices described by graphs, Question 6)

AIM workshop Spectra of families of matrices described by graphs, digraphs, and sign patterns, open
questions, Question 6 (Grone-Merris conjecture): for a graph `G` with Laplacian eigenvalues `λ =
(λ₁, …, λₙ)` and conjugate degree sequence `d*`, is `λ` majorized by `d*`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section

namespace MathlibExt.GraphTheory.GroneMerrisLaplacianMajorizationAIMLinearAlgebraProblem18Wanted

/-!
Source: AIM workshop Spectra of families of matrices described by graphs, digraphs, and sign
patterns (October 2006), open questions prepared by I.-J. Kim and A. Wangsness Wehe, Question 6,
https://aimath.org/WWN/matrixspectrum/matrixspectrum.pdf. UnsolvedMath record UM-20002224
(`AIM-LINEAR_ALGEBRA-0018`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite simple graphs on a finite type `V` with `n = |V|`. The Laplacian is Mathlib's
`SimpleGraph.lapMatrix` (`D - A`) and its eigenvalues `λ₁ ≥ ⋯ ≥ λₙ` are
`Matrix.IsHermitian.eigenvalues₀`, which are sorted in decreasing order. The conjugate degree
sequence is `d*_k = #{v | k ≤ deg v}` for `k = 1, …, n`, as in Bai's paper. Majorization of
nonincreasing sequences is stated through partial sums: `λ₁ + ⋯ + λₖ ≤ d*₁ + ⋯ + d*ₖ` for every `k ≤
n`, with equality at `k = n` (both totals equal `2|E|`).
-/

/-- The conjugate degree sequence of `G`: `d*_k = #{v | k ≤ deg v}`. -/
def conjugateDegree {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ℕ :=
  (Finset.univ.filter fun v => k ≤ G.degree v).card

/-- The Grone-Merris conjecture as a claim: for every finite simple graph `G` on `n` vertices, the
Laplacian eigenvalues `λ₁ ≥ ⋯ ≥ λₙ` of `G` are majorized by the conjugate degree sequence `d*`:
`λ₁ + ⋯ + λₖ ≤ d*₁ + ⋯ + d*ₖ` for every `k ≤ n`, with equality at `k = n`. -/
def groneMerrisMajorization : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ k ≤ Fintype.card V,
      ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i ≤
        ∑ j ∈ Finset.Icc 1 k, (conjugateDegree G j : ℝ)) ∧
    ∑ i, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i =
      ∑ j ∈ Finset.Icc 1 (Fintype.card V), (conjugateDegree G j : ℝ)

/--
Resolved true: Bai proved the Grone-Merris conjecture: for every finite simple graph the Laplacian
spectrum `λ₁ ≥ ⋯ ≥ λₙ` is majorized by the conjugate degree sequence `d*_k = #{v | k ≤ deg v}`.
Source: AIM workshop Spectra of families of matrices described by graphs, digraphs, and sign
patterns (October 2006), open questions prepared by I.-J. Kim and A. Wangsness Wehe, Question 6,
https://aimath.org/WWN/matrixspectrum/matrixspectrum.pdf; resolution: H. Bai, The Grone-Merris
conjecture, Trans. Amer. Math. Soc. 363 (2011), no. 8, 4463-4474, arXiv:0911.2172, main theorem (the
Grone-Merris Conjecture, stated in the introduction and proved in the paper): for every finite
simple graph G the Laplacian spectrum λ(G), listed in non-increasing order, is majorized by the
conjugate degree sequence d'(G), d'_k = #{i : d_i ≥ k},
https://doi.org/10.1090/S0002-9947-2011-05393-6.
-/
public theorem_wanted groneMerrisMajorization_holds : groneMerrisMajorization

end MathlibExt.GraphTheory.GroneMerrisLaplacianMajorizationAIMLinearAlgebraProblem18Wanted
