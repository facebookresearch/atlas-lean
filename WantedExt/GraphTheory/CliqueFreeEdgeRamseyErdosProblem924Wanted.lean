/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graphs without K_{l+1} that are edge-Ramsey for K_l (Erdős Problem 924)

Erdős Problem 924: let `k ≥ 2` and `l ≥ 3`. Is there a graph `G` which contains no `K_{l+1}` such
that every `k`-colouring of the edges of `G` contains a monochromatic copy of `K_l`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.CliqueFreeEdgeRamseyErdosProblem924Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #924, https://www.erdosproblems.com/924 (status
PROVED). UnsolvedMath record UM-30007091 (`EP-924`), dataset ulamai/UnsolvedMath v1.8.0.

Finite graphs, on `Fin N`. A `k`-colouring of the edges is a function `Sym2 (Fin N) → Fin k` (its
values off the edge set are irrelevant), and a monochromatic `K_l` is an `l`-clique of `G` all of
whose edges have one colour. formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 924: for all `k ≥ 2` and `l ≥ 3` there is a finite graph with no `K_{l+1}` such
that every colouring of its edges with `k` colours has a monochromatic `K_l` (colourings are
functions on `Sym2 V`; their values off the edge set are irrelevant). -/
def cliqueFreeEdgeRamseyGraph : Prop :=
  ∀ k l : ℕ, 2 ≤ k → 3 ≤ l → ∃ (N : ℕ) (G : SimpleGraph (Fin N)), G.CliqueFree (l + 1) ∧
    ∀ c : Sym2 (Fin N) → Fin k, ∃ s : Finset (Fin N), G.IsNClique l s ∧ ∃ i : Fin k,
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c s(x, y) = i

/--
Resolved true: Nešetřil and Rödl proved that for every finite graph `G` with clique number `m` and
every number `r` of colours there is a finite graph with clique number `m` every `r`-colouring of
whose edges has an induced monochromatic copy of `G`; for `G = K_l` this is a graph without
`K_{l+1}` in which every `k`-colouring has a monochromatic `K_l` (Folkman had proved the case `k =
2`). Source: T. F. Bloom, Erdős Problems, Problem #924, https://www.erdosproblems.com/924 (status
PROVED); resolution: J. Folkman, Graphs with monochromatic complete subgraphs in every edge
coloring, SIAM J. Appl. Math. 18 (1970), 19-24; J. Nešetřil and V. Rödl, The Ramsey property for
graphs with forbidden complete subgraphs, J. Combin. Theory Ser. B 20 (1976), 243-249,
Nešetřil-Rödl, main theorem (abstract): for every finite graph G with clique number m and every r ≥
1 there is a finite graph H with clique number m such that every r-colouring of the edges of H has
an induced monochromatic copy of G; Folkman proved the case k = 2 (erdosproblems.com/924),
https://www.sciencedirect.com/science/article/pii/0095895676900150.
-/
public theorem_wanted cliqueFreeEdgeRamseyGraph_holds : cliqueFreeEdgeRamseyGraph

end MathlibExt.GraphTheory.CliqueFreeEdgeRamseyErdosProblem924Wanted
