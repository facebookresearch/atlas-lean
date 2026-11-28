/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE of linear size (fixed fraction r) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE, comment.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CliqueFixedFractionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueFixedFraction

/-!
# CLIQUE of linear size (fixed fraction r) is NP-complete

For a fixed rational `r` with `0 < r < 1`:
INSTANCE: a graph `G = (V, E)`.
QUESTION: does `G` contain a clique of size `r|V|` or more?

The comment to CLIQUE (Garey and Johnson [GT19]) reads: "The variant in which, for a given r,
0 < r < 1, we are asked whether G contains a clique of size r|V| or more is NP-complete for any
fixed value of r." The theorem states this for every fixed `r = p / q` with natural numbers
`0 < p < q`; "size `r|V|` or more" is `p * |V| ≤ q * k` for the size `k` of the clique. A clique
of size `k` is Mathlib's `SimpleGraph.IsNClique k s` (a set `s` of `k` pairwise adjacent
vertices); a clique of size at least `r|V|` exists exactly when one of size exactly some
`k ≥ r|V|` does.

The graph is given by its vertex count `n` (vertices `0, …, n - 1`) and a simple edge list, as a
`SimpleGraph (Fin n)` through `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLIQUE of linear size is NP-complete** for every fixed fraction `r = p / q`, `0 < r < 1`.
Source: Garey and Johnson (1979), [GT19], comment. -/
public theorem_wanted cliqueFixedFraction_npComplete (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    cliqueFixedFractionDec p q ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (cliqueFixedFractionDec p q)

end MetaMathlibExt.Complexity.NPComplete.CliqueFixedFraction
