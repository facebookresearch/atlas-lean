/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM COMPATIBLE CHARACTER SET for binary characters is NP-complete

Source:
W. H. E. Day and D. Sankoff, "Computational complexity of inferring phylogenies by
compatibility", Systematic Zoology 35(2) (1986), 224-229, doi:10.2307/2413432 (the four basic
variants of the compatibility problem, cladistic or qualitative and binary or unconstrained
characters, are NP-complete; this is the qualitative binary variant);
G. F. Estabrook, C. S. Johnson Jr. and F. R. McMorris, "A mathematical foundation for the
analysis of cladistic character compatibility", Mathematical Biosciences 29 (1976), 181-187,
doi:10.1016/0025-5564(76)90035-3 (binary characters fit one tree iff they are pairwise
compatible).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaximumCompatibleBinaryCharactersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumCompatibleBinaryCharacters

open Cslib.Bioinformatics.Phylogenetics.Splits (FourGametes)

/-!
# MAXIMUM COMPATIBLE CHARACTER SET for binary characters is NP-complete

INSTANCE: `n ≥ 2` species described by `m` binary (two-state, unrooted) characters, and an
integer `K`. QUESTION: is there a set of at least `K` characters that are perfectly compatible
with one phylogeny, i.e. a set admitting a perfect phylogeny?

For binary characters a set fits one phylogeny iff its members are pairwise compatible, and two
binary characters are compatible iff they do not show all four gametes `(0,0), (0,1), (1,0),
(1,1)` on the species (Estabrook, Johnson and McMorris 1976; in this repository
`Cslib.Bioinformatics.Phylogenetics.Splits.exists_perfectPhylogeny_iff`, which needs at least two
species, so `WellFormed` requires `n ≥ 2`). The question is stated with the repository's
`FourGametes`. The species are
`Fin n`, and the character matrix is given by its columns, one list of `n` states per
character, so every character is listed explicitly.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAXIMUM COMPATIBLE CHARACTER SET for binary characters is NP-complete.** Source: Day and
Sankoff (1986); Estabrook, Johnson and McMorris (1976). -/
public theorem_wanted maximumCompatibleBinaryCharacters_npComplete :
    maximumCompatibleBinaryCharactersDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumCompatibleBinaryCharactersDec

end MetaMathlibExt.Complexity.NPComplete.MaximumCompatibleBinaryCharacters
