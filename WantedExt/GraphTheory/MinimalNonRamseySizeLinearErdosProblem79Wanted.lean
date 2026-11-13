/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal non-Ramsey-size-linear graphs (Erdős Problem 79)

Erdős Problem 79 (Erdős, Faudree, Rousseau and Schelp): a graph `G` is Ramsey size linear if `R(G,
H) ≪ m` for all graphs `H` with `m` edges and no isolated vertices. Are there infinitely many graphs
`G` that are not Ramsey size linear but all of whose subgraphs are?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.MinimalNonRamseySizeLinearErdosProblem79Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #79, https://www.erdosproblems.com/79 (status PROVED).
UnsolvedMath record UM-30006714 (`EP-79`), dataset ulamai/UnsolvedMath v1.8.0.

Ramsey size linearity is `MathlibExt`'s `SimpleGraph.IsRamseySizeLinear` (`R(G, H) ≤ c e(H)` for
every finite `H` without isolated vertices, with `graphPairRamsey`). 'All of its subgraphs' means
the proper subgraphs, as in Wigderson's paper; 'infinitely many' is 'with arbitrarily many
vertices', which for minimal graphs (no isolated vertices) is the same as infinitely many up to
isomorphism. Compared with the formal-conjectures statement `ErdosProblems/79.lean` (equivalent; no
code imported).
-/

open Classical in
/-- Erdős Problem 79: there are infinitely many finite graphs `G` that are not Ramsey size linear
while every proper subgraph of `G` is. -/
def infinitelyManyMinimalNonRamseySizeLinear : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ G : SimpleGraph (Fin n), ¬ G.IsRamseySizeLinear ∧
    ∀ H : G.Subgraph, H ≠ ⊤ → H.coe.IsRamseySizeLinear

/--
Resolved true: Wigderson proved that there are infinitely many graphs that are not Ramsey size
linear while each of their proper subgraphs is (the proof is not explicit; `K₄` remains the only
known example); erdosproblems.com/79 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #79, https://www.erdosproblems.com/79 (status PROVED); resolution: Y. Wigderson,
Infinitely many minimally non-Ramsey size-linear graphs, arXiv:2409.05931 (2024), Theorem 1: there
exist infinitely many graphs G which are not Ramsey size-linear but every proper subgraph of G is
Ramsey size-linear, answering the question of Erdős, Faudree, Rousseau and Schelp,
https://arxiv.org/abs/2409.05931.
-/
public theorem_wanted infinitelyManyMinimalNonRamseySizeLinear_holds :
    infinitelyManyMinimalNonRamseySizeLinear

end MathlibExt.GraphTheory.MinimalNonRamseySizeLinearErdosProblem79Wanted
