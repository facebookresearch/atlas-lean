/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF CO-BIPARTITE GRAPHS is NP-complete

Source:
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024;
H. L. Bodlaender, É. Bonnet, L. Jaffke, D. Knop, P. T. Lima, M. Milanič, S. Ordyniak, S. Pandey
and O. Suchý, "Treewidth is NP-complete on cubic graphs", Electronic Journal of Combinatorics
32(3) (2025), #P3.36, doi:10.37236/13205 (arXiv:2301.10031, "Treewidth is NP-complete on cubic
graphs (and related results)": Section 2 defines co-bipartite graphs, Corollary 3.2 states
"Treewidth is NP-complete on co-bipartite graphs", and the introduction attributes this to
Arnborg, Corneil and Proskurowski: "their proof also gives NP-completeness on co-bipartite
graphs").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TreewidthCoBipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthCoBipartite

open MetaMathlibExt.Complexity.NPComplete.Treewidth

/-!
# TREEWIDTH OF CO-BIPARTITE GRAPHS is NP-complete

INSTANCE: a co-bipartite graph `G = (V, E)` and an integer `K`.
QUESTION: is the treewidth of `G` at most `K`?

This is TREEWIDTH (`WantedExt.Complexity.NPComplete.TreewidthWanted`) restricted to co-bipartite
graphs: the instance type, graph, well-formedness and question are those of that module, and
the restriction is added to well-formedness. Bodlaender et al. (Section 2): "A graph `G` is
co-bipartite if `V(G) = A ∪ B` with `A` a clique and `B` a clique (that is, the complement of
`G` is bipartite)." The restriction is stated as Mathlib's `SimpleGraph.IsBipartite` (a proper
2-coloring) of the complement `(Graph i)ᶜ`: the two color classes of the complement are the
cliques `A` and `B` of `G`. ISGCI (class `gc_486`) records TREEWIDTH as NP-complete on this
class, citing Arnborg, Corneil and Proskurowski (1987) and Bodlaender and Thilikos (1997).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TREEWIDTH OF CO-BIPARTITE GRAPHS is NP-complete.** Source: Arnborg, Corneil and
Proskurowski (1987); Bodlaender et al. (2025), Corollary 3.2. -/
public theorem_wanted treewidthCoBipartite_npComplete :
    treewidthCoBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthCoBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthCoBipartite
