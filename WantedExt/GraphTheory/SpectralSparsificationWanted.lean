/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian
public import MathlibExt.LinearAlgebra.Matrix.SpectralSparsification
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Twice-Ramanujan spectral sparsifiers (wanted)

Linear-size spectral sparsifiers (Batson, Spielman and Srivastava, *Twice-Ramanujan
sparsifiers*, SIAM J. Comput. 41 (2012), arXiv:0808.0163, Theorems 3.1 and 1.1), stated in the
Loewner order, the first for rank-one decompositions of the identity and the second for the
weighted Laplacian `EndpointMapMultigraph.laplacian`. The first, the vector form, is proved in
`MathlibExt.LinearAlgebra.Matrix.SpectralSparsification`; the second remains wanted here.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.SpectralSparsificationWanted

open EndpointMapMultigraph Matrix

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]

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
