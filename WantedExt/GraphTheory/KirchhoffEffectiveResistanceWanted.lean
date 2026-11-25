/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.EndpointMapMultigraph.EffectiveResistance
public import MathlibExt.Combinatorics.SimpleGraph.KirchhoffEffectiveResistance
public import MathlibExt.Combinatorics.SimpleGraph.MatrixTree
public import Mathlib.Combinatorics.SimpleGraph.Dart

/-!
# Kirchhoff's effective resistance formula (wanted)

For a uniformly random spanning tree `T` of a finite connected graph and an edge `e = uv`,
`P[e ∈ T] = R_eff(u, v)`, the effective resistance between the endpoints of `e` when every edge
is a unit resistor (G. Kirchhoff, 1847; R. Lyons and Y. Peres, *Probability on Trees and
Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026,
Section 4.2, Kirchhoff's Effective Resistance Formula). The source proves the weighted version,
`P[e ∈ T] = c(e) R(e⁻ ↔ e⁺)` for the spanning tree drawn with probability proportional to the
product of its conductances, with Wilson's algorithm. The imported unit-conductance case is
proved by edge deletion and Cramer's rule. This module records the weighted formula and the
weighted matrix-tree theorem
`Ξ(G) = det Δ_G^{(x)}` (Lyons and Peres, Section 4.4, the paragraph before Exercise 4.16), of which
`MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.kirchhoff_matrix_tree_lapMatrix` is the
unit-conductance case.

Conductances are a function `c : Sym2 V → ℝ` on the edges of `G`; the network is the multigraph of
darts of `G` with conductance `c(d.edge) / 2` on the dart `d`, so that its Laplacian is the network
Laplacian `Δ_G` of Lyons and Peres, Exercise 2.62 (each edge appears as two opposite darts).
-/

@[expose] public section

namespace MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted

open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-- **Kirchhoff's effective resistance formula, weighted.** In a finite connected simple graph `G`
with positive conductances `c` on its edges, let `T` be the random spanning tree drawn with
probability proportional to `Ξ(T) = ∏_{e ∈ T} c(e)`. For every edge `uv`,
`P[uv ∈ T] = c(uv) R(u ↔ v)` (R. Lyons and Y. Peres, *Probability on Trees and Networks*,
Cambridge University Press 2016, corrected online version of 19 August 2026, Section 4.2,
Kirchhoff's Effective Resistance Formula). The effective resistance is that of the dart multigraph
of `G` with conductance `c(d.edge) / 2` on the dart `d`. -/
theorem_wanted weighted_spanningTree_adj_div {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) {u v : V} (huv : G.Adj u v) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T ∧ T.Adj u v}, ∏ᶠ e ∈ T.1.edgeSet, c e) /
        (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e) =
      c s(u, v) * EndpointMapMultigraph.effectiveResistance (fun d : G.Dart => d.fst)
        (fun d : G.Dart => d.snd) (fun d => c d.edge / 2) u v

/-- **Weighted matrix-tree theorem.** In a finite simple graph `G` with conductances `c` on its
edges, the weighted spanning-tree sum `Ξ(G) = ∑_T ∏_{e ∈ T} c(e)` equals `det Δ_G^{(x)}` for every
vertex `x`, where `Δ_G` is the network Laplacian (`c(x, y)` summed into the diagonal, `-c(x, y)`
off it) and `Δ_G^{(x)}` strikes the row and column of `x` (R. Lyons and Y. Peres, *Probability on
Trees and Networks*, Cambridge University Press 2016, corrected online version of
19 August 2026, Section 4.4, the paragraph before Exercise 4.16, stated there for simple networks;
the network Laplacian is that of Exercise 2.62). The network Laplacian is the Laplacian of the
dart multigraph with conductance `c(d.edge) / 2` on the dart `d`. -/
theorem_wanted weighted_matrix_tree {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → ℝ) (x : V) :
    (∑ᶠ T : {T : G.Subgraph // IsSpanningTree T}, ∏ᶠ e ∈ T.1.edgeSet, c e) =
      ((EndpointMapMultigraph.laplacian (fun d : G.Dart => d.fst) (fun d : G.Dart => d.snd)
        (fun d => c d.edge / 2)).submatrix (Subtype.val : {y : V // y ≠ x} → V)
          (Subtype.val : {y : V // y ≠ x} → V)).det

end MathlibExt.GraphTheory.KirchhoffEffectiveResistanceWanted
