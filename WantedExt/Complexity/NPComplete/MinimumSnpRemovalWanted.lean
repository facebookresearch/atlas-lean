/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SNP REMOVAL is NP-complete

Source:
G. Lancia, V. Bafna, S. Istrail, R. Lippert, and R. Schwartz, "SNPs problems, complexity, and
algorithms", Algorithms - ESA 2001, Lecture Notes in Computer Science 2161, Springer (2001),
182-193, doi:10.1007/3-540-44676-1_15, Section 1.3 and Theorem 8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MinimumSnpRemovalDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSnpRemoval

open MinimumErrorCorrection (MinimumErrorCorrectionInstance)
open MinimumFragmentRemoval (fragmentConflictGraph)

/-!
# MINIMUM SNP REMOVAL is NP-complete

INSTANCE: an SNP matrix `M`, an `n × m` matrix over `{A, B, -}` whose rows are fragments and
whose columns are SNPs, and an integer `K`.
QUESTION: can at most `K` SNPs (columns) be removed so that the resulting matrix is feasible?

The definitions are those of Lancia, Bafna, Istrail, Lippert and Schwartz (Section 1.3), as in
`MinimumFragmentRemovalWanted`: a matrix is feasible if its fragment conflict graph `G_F` is
bipartite; MSR asks to remove the minimum number of snips (columns) so that the resulting matrix is
feasible. (The source spells the problem "Minimum Snip Removal", "snip" being its word for an SNP;
later literature writes Minimum SNP Removal.) Theorem 8 proves MSR NP-hard, already for matrices
with at most two gaps per fragment; a set of removed columns with a 2-colouring of the conflict
graph is a short certificate.

The instance, its well-formedness and the conflict graph are those of
`MinimumFragmentRemovalWanted` (entries `0` for `A`, `1` for `B`, `2` for a hole). A column is
removed by replacing its entries with holes, as the source does in its proof of Theorem 3
("deleting (i.e., replacing with gaps)"): the conflicts of the resulting matrix are exactly the
conflicts at the remaining columns. `K` uses the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MINIMUM SNP REMOVAL is NP-complete.** Source: Lancia, Bafna, Istrail, Lippert, and
Schwartz (2001), Theorem 8. -/
public theorem_wanted minimumSnpRemoval_npComplete :
    minimumSnpRemovalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumSnpRemovalDec

end MetaMathlibExt.Complexity.NPComplete.MinimumSnpRemoval
