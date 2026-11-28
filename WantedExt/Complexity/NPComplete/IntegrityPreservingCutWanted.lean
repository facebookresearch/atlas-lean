/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRITY PRESERVING CUT is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [5] INTEGRITY PRESERVING CUT (reference: M. Luby,
private communication; transformation from 3SAT);
P. van 't Hof, D. Paulusma and G. J. Woeginger, "Partitioning graphs into connected parts",
Theoretical Computer Science 410 (2009), 4834-4843, doi:10.1016/j.tcs.2009.06.028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IntegrityPreservingCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegrityPreservingCut

/-!
# INTEGRITY PRESERVING CUT is NP-complete

INSTANCE: a graph `G = (V, E)` and disjoint subsets `U₁, U₂ ⊆ V`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that, for each
`i ∈ {1, 2}`, `Uᵢ ⊆ Vᵢ` and the subgraph of `G` induced by `Vᵢ` is connected?
(Johnson's column, problem [5], citing Luby's unpublished proof, which was not available; van 't
Hof, Paulusma and Woeginger 2009 study the same problem as 2-DISJOINT CONNECTED SUBGRAPHS and
prove it NP-complete, even when `|U₁| = 2`.)

The graph is given by its vertex count `n` and a simple edge list, as the `SimpleGraph (Fin n)`
`Cslib.Complexity.Karp.edgeGraph n es`; `U₁` and `U₂` are lists of vertices. `V₂` is the
complement of `V₁`; "connected" is Mathlib's `SimpleGraph.Connected` of the induced subgraph,
which includes being nonempty.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INTEGRITY PRESERVING CUT is NP-complete.** Source: Johnson (1982), problem [5]; van 't Hof,
Paulusma and Woeginger (2009). -/
public theorem_wanted integrityPreservingCut_npComplete :
    integrityPreservingCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integrityPreservingCutDec

end MetaMathlibExt.Complexity.NPComplete.IntegrityPreservingCut
