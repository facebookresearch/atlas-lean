/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Seymour's r-graph conjecture (Open Problem Garden 2226)

Open Problem Garden, Seymour's r-graph conjecture (P. D. Seymour): an `r`-graph is an `r`-regular
graph `G` with `|δ(X)| ≥ r` for every `X ⊆ V(G)` of odd size; every `r`-graph has chromatic index at
most `r + 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.Combinatorics.EndpointMapMultigraph

@[expose] public section

namespace MathlibExt.GraphTheory.SeymourRGraphEdgeColoringOpenGardenProblem2226Wanted

/-!
Source: Open Problem Garden, Seymour's r-graph conjecture (node 2226; P. D. Seymour),
http://www.openproblemgarden.org/op/seymours_r_graph_conjecture. UnsolvedMath record UM-00003203
(`OPG-2226`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite loopless multigraphs, as in Seymour's setting and in Chen-Jing-Zang (for simple
graphs Vizing's theorem gives the bound): the edge `e` joins `src e ≠ tgt e`, and parallel edges are
allowed (MathlibExt's endpoint-map multigraphs). The degree counts endpoint incidences
(`EndpointMapMultigraph.degreeWithin`), `δ(X)` is `EndpointMapMultigraph.cut`, the set of edges with
exactly one end in `X`, and `χ'(G) ≤ r + 1` is the existence of a proper edge colouring with `r + 1`
colours. As in Chen-Jing-Zang, `r` is a positive integer.
-/

variable {V E : Type}

/-- The loopless multigraph with vertex set `V` and edge set `E`, the edge `e` joining `src e` and
`tgt e`, is an `r`-graph: no loops, every vertex has degree `r`, and for every vertex set `X` of odd
size at least `r` edges have exactly one end in `X`. -/
def IsRGraph (r : ℕ) [Fintype E] (src tgt : E → V) : Prop :=
  (∀ e, src e ≠ tgt e) ∧
    (∀ v, EndpointMapMultigraph.degreeWithin src tgt Finset.univ v = r) ∧
    ∀ X : Finset V, Odd X.card → r ≤ (EndpointMapMultigraph.cut src tgt X).card

/-- `c` is a proper edge colouring: distinct edges with a common end get distinct colours. -/
def IsProperEdgeColoring {k : ℕ} (src tgt : E → V) (c : E → Fin k) : Prop :=
  ∀ e f, e ≠ f → (src e = src f ∨ src e = tgt f ∨ tgt e = src f ∨ tgt e = tgt f) → c e ≠ c f

/-- Seymour's `r`-graph conjecture: every finite `r`-graph (`r ≥ 1`) has chromatic index at most
`r + 1`. -/
def rGraphChromaticIndexLeSucc : Prop :=
  ∀ (r : ℕ) (V E : Type) [Fintype V] [Fintype E] (src tgt : E → V), 0 < r → IsRGraph r src tgt →
    ∃ c : E → Fin (r + 1), IsProperEdgeColoring src tgt c

/--
Resolved true: Chen, Jing and Zang prove the Goldberg-Seymour conjecture (Theorem 1.1) and deduce
(Theorem 1.2) that every `r`-graph `G` satisfies `χ'(G) ≤ r + 1`. Source: Open Problem Garden,
Seymour's r-graph conjecture (node 2226; P. D. Seymour),
http://www.openproblemgarden.org/op/seymours_r_graph_conjecture; resolution: G. Chen, G. Jing and W.
Zang, Proof of the Goldberg-Seymour conjecture on edge-colorings of multigraphs, J. Comb. Optim. 50
(2025); arXiv:1901.10316, Theorem 1.2: every r-graph G satisfies χ'(G) ≤ r + 1 (Seymour's
conjecture, their Conjecture 1.2), a corollary of Theorem 1.1 (the Goldberg-Seymour conjecture);
r-graph as defined there: regular of degree r with at least r edges between X and V - X for every
odd X ⊆ V, https://arxiv.org/abs/1901.10316.
-/
public theorem_wanted rGraphChromaticIndexLeSucc_holds : rGraphChromaticIndexLeSucc

end MathlibExt.GraphTheory.SeymourRGraphEdgeColoringOpenGardenProblem2226Wanted
