/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DCJ MEDIAN (multichromosomal genomes) is NP-complete

Source:
E. Tannier, C. Zheng and D. Sankoff, "Multichromosomal median and halving problems under
different genomic distances", BMC Bioinformatics 10 (2009), 120, doi:10.1186/1471-2105-10-120
(Theorem 5: "The DCJ median problem for multichromosomal genomes is NP-hard, even for circular
genomes").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DCJMedianDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DCJMedian

/-!
# DCJ MEDIAN (multichromosomal genomes) is NP-complete

INSTANCE: three genomes `Π₁, Π₂, Π₃` on a common set of `n` genes, each given as a set of
adjacencies, and an integer `K`.
QUESTION: is there a genome `M` on the same genes with
`d_DCJ(Π₁, M) + d_DCJ(Π₂, M) + d_DCJ(Π₃, M) ≤ K`?

Definitions, after Tannier, Zheng and Sankoff (following Bergeron, Mixtacki and Stoye): a gene
`A` has a tail `Aᵗ` and a head `Aʰ`, its extremities. An adjacency is an unordered pair of gene
extremities, and a genome is a set of adjacencies in which each extremity is adjacent to zero or
one other extremity; an extremity in no adjacency is a telomere. Chromosomes may be linear or
circular (multichromosomal genomes, the general case of Theorem 5). A double cut and join (DCJ)
acts on two adjacencies `pq` and `rs`, where some of `p, q, r, s` may be the null symbol `∘` of a
telomere (and one adjacency may be `∘∘`), and replaces them by `pr` and `qs` (or `ps` and `qr`).
The DCJ distance `d_DCJ(Π, Γ)` is the least number of DCJs transforming `Π` into `Γ`.

Representation: the genes are `0, ..., n - 1`, with `n` given in unary as a list of `true`s (the
genes are part of the instance even when no adjacency mentions them); gene `g` has tail `2g` and
head `2g + 1`, so the extremities are `Fin (2n)`. A genome is a simple graph on the extremities
whose edges are its adjacencies and in which every vertex has at most one neighbour
(`IsGenome`). The input genomes are adjacency lists, read with `Cslib.Complexity.Karp.edgeGraph`.
Spelling out the null symbols, a DCJ (`IsDCJ`) is one of: deleting an adjacency `pq` (cutting
`pq` and `∘∘` into `p∘` and `q∘`); joining two telomeres `p` and `q` (the reverse); replacing an
adjacency `pq` and a telomere `r` by the adjacency `pr` and the telomere `q`; and replacing two
distinct adjacencies `pq`, `rs` by `pr` and `qs` (the choice `ps`, `qr` is the same move with `r`
and `s` exchanged). `DCJWithin Π Γ k` says that at most `k` DCJs transform `Π` into `Γ`, so
`d_DCJ(Π, Γ) ≤ k`; the question asks for `M` and `k₁ + k₂ + k₃ ≤ K` with `DCJWithin Πᵢ M kᵢ`,
which holds exactly when the three distances sum to at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **DCJ MEDIAN for multichromosomal genomes is NP-complete.** Source: Tannier, Zheng and
Sankoff (2009), Theorem 5. -/
public theorem_wanted dcjMedian_npComplete :
    dcjMedianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dcjMedianDec

end MetaMathlibExt.Complexity.NPComplete.DCJMedian
