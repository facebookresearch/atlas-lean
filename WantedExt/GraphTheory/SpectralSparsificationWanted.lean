/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Twice-Ramanujan spectral sparsifiers (wanted)

Linear-size spectral sparsifiers (Batson, Spielman and Srivastava, *Twice-Ramanujan
sparsifiers*, SIAM J. Comput. 41 (2012), arXiv:0808.0163, Theorems 3.1 and 1.1), stated in the
Loewner order, the first for rank-one decompositions of the identity and the second for the
weighted Laplacian `EndpointMapMultigraph.laplacian`.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.SpectralSparsificationWanted

open EndpointMapMultigraph Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

/-- **Batson–Spielman–Srivastava, vector form.** Let `d > 1` and let `v₁, …, v_m ∈ ℝⁿ` satisfy
`∑ vᵢ vᵢᵀ = I`. Then there are scalars `sᵢ ≥ 0`, at most `d n` of them nonzero, with
`I ≼ ∑ sᵢ vᵢ vᵢᵀ ≼ κ I` for `κ = (d + 1 + 2√d) / (d + 1 - 2√d)` (Batson, Spielman and
Srivastava, *Twice-Ramanujan sparsifiers*, arXiv:0808.0163, Theorem 3.1). -/
theorem_wanted exists_sparse_reweighting {m n : ℕ} {d : ℝ} (hd : 1 < d) (v : Fin m → Fin n → ℝ)
    (hv : ∑ i, vecMulVec (v i) (v i) = 1) :
    ∃ s : Fin m → ℝ, 0 ≤ s ∧ ((Finset.univ.filter fun i => s i ≠ 0).card : ℝ) ≤ d * n ∧
      (∑ i, s i • vecMulVec (v i) (v i) - 1).PosSemidef ∧
      (((d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        ∑ i, s i • vecMulVec (v i) (v i)).PosSemidef

/-- **Twice-Ramanujan sparsifiers.** For every `d > 1`, every weighted graph `G` on `n ≥ 1`
vertices has a reweighted subgraph `H` (its weights `w'` are supported on edges of `G`) with at
most `⌈d (n - 1)⌉` edges such that `L_G ≼ L_H ≼ κ L_G` for `κ = (d + 1 + 2√d) / (d + 1 - 2√d)`
(Batson, Spielman and Srivastava, *Twice-Ramanujan sparsifiers*, arXiv:0808.0163, Theorem 1.1).
It is stated here for multigraphs, which follows from the graph case by merging parallel edges;
`n - 1` is truncated subtraction, which only matters for the empty graph. -/
theorem_wanted exists_twice_ramanujan_sparsifier (end₁ end₂ : E → V) {w : E → ℝ} (hw : 0 ≤ w)
    {d : ℝ} (hd : 1 < d) :
    ∃ w' : E → ℝ, 0 ≤ w' ∧ (∀ e, w e = 0 → w' e = 0) ∧
      (Finset.univ.filter fun e => w' e ≠ 0).card ≤
        ⌈d * ((Fintype.card V - 1 : ℕ) : ℝ)⌉₊ ∧
      (laplacian end₁ end₂ w' - laplacian end₁ end₂ w).PosSemidef ∧
      (((d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)) • laplacian end₁ end₂ w -
        laplacian end₁ end₂ w').PosSemidef

end MathlibExt.GraphTheory.SpectralSparsificationWanted
