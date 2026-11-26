/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.WeightedLaplacian

/-!
# Spectral approximation and cut approximation

A spectral approximation controls the Laplacian energy of every real vertex potential.
Restricting to indicator potentials controls the weight of every cut. Both comparisons use
relative error with respect to the original graph, not the approximating graph.

See D. A. Spielman and N. Srivastava, *Graph Sparsification by Effective Resistances*,
[arXiv:0803.0929v4](https://arxiv.org/abs/0803.0929), equation (1) and §1, pp. 1–2.
We use only the approximation criterion, not the construction of a sparse subgraph. The
indicator argument itself needs no sign conditions on weights or error; the definitions
below restrict to nonnegative weights and `0 < ε < 1` for the relative-error interpretation.
-/

@[expose] public section

namespace EndpointMapMultigraph

/-- Two endpoint maps and a nonnegative weight for each edge. Bundling just this data lets
comparisons share a vertex type while each graph retains its own edge type. -/
structure WeightedPresentation (V E : Type*) where
  /-- First endpoint. -/
  end₁ : E → V
  /-- Second endpoint. The ordering of the two endpoints does not orient the graph. -/
  end₂ : E → V
  /-- Real edge weights, counted separately on parallel edges. -/
  weight : E → ℝ
  /-- Each edge has nonnegative weight. -/
  weight_nonneg : 0 ≤ weight

namespace WeightedPresentation

open Matrix

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
variable [DecidableEq V] [DecidableEq E] [DecidableEq F]
variable (H : WeightedPresentation V F) (G : WeightedPresentation V E) (ε : Set.Ioo (0 : ℝ) 1)

/-- `H` is a cut approximation of `G` with tolerance `ε` if for every finite vertex set `S`,
the total weight of the edges of `H` crossing `S` lies between `1 - ε` and `1 + ε` times
the corresponding total for `G`. On finite vertex types `Finset V` ranges over all subsets. -/
def IsCutApproximation : Prop :=
  ∀ S : Finset V,
    let g := ∑ e ∈ cut G.end₁ G.end₂ S, G.weight e
    let h := ∑ e ∈ cut H.end₁ H.end₂ S, H.weight e
    (1 - (ε : ℝ)) * g ≤ h ∧ h ≤ (1 + (ε : ℝ)) * g

/-- `H` is a spectral approximation of `G` with tolerance `ε` if for every real vertex
potential `x`, its energy in `H` lies between `1 - ε` and `1 + ε` times its energy in `G`. -/
def IsSpectralApproximation : Prop :=
  ∀ x : V → ℝ,
    let g := x ⬝ᵥ (laplacian G.end₁ G.end₂ G.weight *ᵥ x)
    let h := x ⬝ᵥ (laplacian H.end₁ H.end₂ H.weight *ᵥ x)
    (1 - (ε : ℝ)) * g ≤ h ∧ h ≤ (1 + (ε : ℝ)) * g

/-- Spectral approximation implies cut approximation: test the energy bounds on `indicator S`
for each cut. No relation between the two edge types or their endpoint maps is needed. -/
theorem IsSpectralApproximation.isCutApproximation {H : WeightedPresentation V F}
    {G : WeightedPresentation V E} {ε : Set.Ioo (0 : ℝ) 1} (h : H.IsSpectralApproximation G ε) :
    H.IsCutApproximation G ε := by
  intro S
  simpa only [indicator_dotProduct_mulVec_laplacian] using h (indicator S)

/-- Equivalently, the two differences in the Loewner bounds `(1 - ε)L_G ≼ L_H ≼ (1 + ε)L_G`
are positive semidefinite. The matrices are compared on vertices, not on edges. -/
theorem isSpectralApproximation_iff_posSemidef :
    let LG := laplacian G.end₁ G.end₂ G.weight
    let LH := laplacian H.end₁ H.end₂ H.weight
    H.IsSpectralApproximation G ε ↔
      (LH - (1 - (ε : ℝ)) • LG).PosSemidef ∧ ((1 + (ε : ℝ)) • LG - LH).PosSemidef := by
  have hG := (posSemidef_laplacian G.end₁ G.end₂ G.weight_nonneg).isHermitian
  have hH := (posSemidef_laplacian H.end₁ H.end₂ H.weight_nonneg).isHermitian
  simp only [IsSpectralApproximation, posSemidef_iff_dotProduct_mulVec,
    hH.sub (hG.smul (IsSelfAdjoint.all (1 - (ε : ℝ)))),
    (hG.smul (IsSelfAdjoint.all (1 + (ε : ℝ)))).sub hH, true_and, star_trivial,
    sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, sub_nonneg, forall_and]

end WeightedPresentation

end EndpointMapMultigraph
