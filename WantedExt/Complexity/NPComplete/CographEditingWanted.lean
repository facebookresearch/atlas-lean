/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COGRAPH EDITING is NP-complete

Source:
Y. Liu, J. Wang, J. Guo and J. Chen, "Complexity and parameterized algorithms for Cograph
Editing", Theoretical Computer Science 461 (2012), 45-54, doi:10.1016/j.tcs.2011.11.040.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CographEditingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CographEditing

/-!
# COGRAPH EDITING is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected) and a nonnegative integer `K`.
QUESTION: can `G` be made `P₄`-free (a cograph) by adding and deleting at most `K` edges?

The edited graph is a `SimpleGraph` `H` on the same vertices; the edges added or deleted are the
symmetric difference `symmDiff G.edgeSet H.edgeSet`. `H` is `P₄`-free when the path on four
vertices (Mathlib's `SimpleGraph.pathGraph 4`) is not an induced subgraph of `H` (Mathlib's
`SimpleGraph.IsIndContained`, as in `InducedPathWanted`); the `P₄`-free graphs are exactly the
cographs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COGRAPH EDITING is NP-complete.** Source: Liu, Wang, Guo and Chen (2012). -/
public theorem_wanted cographEditing_npComplete :
    cographEditingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cographEditingDec

end MetaMathlibExt.Complexity.NPComplete.CographEditing
