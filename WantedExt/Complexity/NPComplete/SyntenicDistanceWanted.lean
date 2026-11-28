/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SYNTENIC DISTANCE is NP-complete

Source:
B. DasGupta, T. Jiang, S. Kannan, M. Li and E. Sweedyk, "On the complexity and approximation
of syntenic distance", Discrete Applied Mathematics 88 (1998), 59-82,
doi:10.1016/S0166-218X(98)00066-3; Definition 2.1 and Theorem 3.1 are numbered as in the
conference version (RECOMB 1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SyntenicDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SyntenicDistance

/-!
# SYNTENIC DISTANCE is NP-complete

INSTANCE: two genomes `G₁` and `G₂` over the same set of genes, and an integer `K`.
QUESTION: is the syntenic distance from `G₁` to `G₂` at most `K`, that is, can `G₁` be
transformed into `G₂` by at most `K` moves?

Following DasGupta, Jiang, Kannan, Li and Sweedyk (1998), Section 2 (after Ferretti, Nadeau and
Sankoff): a genome is a collection of subsets (synteny sets, or chromosomes) of a set of genes,
and the order of genes is ignored. Definition 2.1: let `S₁, S₂, T₁, T₂` be sets, at most one
of them empty, with `T₁ ∪ T₂ = S₁ ∪ S₂`; if all four are nonempty, replacing `S₁, S₂` by
`T₁, T₂` is a translocation; if `S₂` is empty, replacing `S₁` by `T₁, T₂` is a fission; if
`T₂` is empty, replacing `S₁, S₂` by `T₁` is a fusion. The syntenic distance `D(G₁, G₂)` is
the least number of moves transforming `G₁` into `G₂`; Theorem 3.1 proves that computing it is
NP-hard. Membership in NP: moves preserve the union of the chromosomes; when the unions agree
and both genomes are nonempty, fusing all chromosomes of `G₁` into one and splitting it into
those of `G₂` takes `|G₁| + |G₂| - 2` moves, so a shortest move sequence is a certificate of
polynomial size.

A genome is a nonempty multiset of nonempty finite sets of genes (`Multiset (Finset ℕ)`), so its
chromosomes are unordered and two equal chromosomes count twice (the source's compact
representation allows equal sets). The instance lists each chromosome as a list of genes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SYNTENIC DISTANCE is NP-complete.** Source: DasGupta, Jiang, Kannan, Li and Sweedyk
(1998), Theorem 3.1. -/
public theorem_wanted syntenicDistance_npComplete :
    syntenicDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L syntenicDistanceDec

end MetaMathlibExt.Complexity.NPComplete.SyntenicDistance
