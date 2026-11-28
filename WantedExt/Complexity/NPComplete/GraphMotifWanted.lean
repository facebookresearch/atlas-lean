/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH MOTIF is NP-complete

Source:
M. R. Fellows, G. Fertin, D. Hermelin and S. Vialette, "Upper and lower bounds for finding
connected motifs in vertex-colored graphs", Journal of Computer and System Sciences 77(4)
(2011), 799-811, doi:10.1016/j.jcss.2010.07.003;
V. Lacroix, C. G. Fernandes and M.-F. Sagot, "Motif search in graphs: application to metabolic
networks", IEEE/ACM Transactions on Computational Biology and Bioinformatics 3(4) (2006),
360-368, doi:10.1109/TCBB.2006.55.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GraphMotifDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphMotif

/-!
# GRAPH MOTIF is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected), a vertex coloring `c : V → C`,
and a multiset `M` of colors.
QUESTION: is there a connected subgraph whose vertex color multiset equals `M`?

Fellows, Fertin, Hermelin and Vialette ask "Does G have a connected subset of vertices whose
multiset of colors equals M?", where an occurrence of `M` is a vertex set `V'` with color
multiset `M` whose induced subgraph `G[V']` is connected. Colors are naturals; the coloring is
the list of the colors of the vertices `0, …, n - 1`, and `M` is a list read as a multiset.
`G[V']` is Mathlib's `SimpleGraph.induce`; connected graphs are nonempty in Mathlib, so the
empty motif has no occurrence.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GRAPH MOTIF is NP-complete.** Source: Fellows, Fertin, Hermelin and Vialette (2011);
Lacroix, Fernandes and Sagot (2006). -/
public theorem_wanted graphMotif_npComplete :
    graphMotifDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphMotifDec

end MetaMathlibExt.Complexity.NPComplete.GraphMotif
