/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete

Source:
N. A. Pierce and E. Winfree, "Protein design is NP-hard", Protein Engineering 15 (2002),
779-782, doi:10.1093/protein/15.10.779;
B. Chazelle, C. Kingsford and M. Singh, "A semidefinite programming approach to side chain
positioning with new rounding strategies", INFORMS Journal on Computing 16 (2004), 380-392,
doi:10.1287/ijoc.1040.0096.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SideChainPositioningDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SideChainPositioning

/-!
# SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete

INSTANCE: positions `1, …, p`, each with a finite set `Rᵢ` of rotamers (the sets pairwise
disjoint); an integer self energy `E(r)` for every rotamer `r`; an integer pairwise energy
`E(r, s)` for every pair of rotamers; an integer `K`.
QUESTION: is there a choice of one rotamer `rᵢ ∈ Rᵢ` at each position `i` whose total energy
`∑ᵢ E(rᵢ) + ∑ᵢ ∑_{j < i} E(rᵢ, rⱼ)` is at most `K`?

The pairwise sum is Pierce and Winfree's `E_total = ∑ᵢ ∑_{j < i} E(rᵢ, rⱼ)`, one term per
unordered pair of positions. Pierce and Winfree state the problem with pairwise terms only and
note that the rotamer self energies used in protein design fold into the pairwise terms; their
problem is the case in which every self energy is `0`. Numbers use the binary encoding.

Positions are `0, …, p - 1` and rotamers are `0, …, R - 1`. The instance lists the position of
each rotamer, so `Rᵢ` is the set of rotamers listed at position `i` and the sets are disjoint by
construction. The self energies are a list of `R` integers and the pairwise energies an `R × R`
matrix of integers, entry `(r, s)` being `E(r, s)`; an integer is a pair `(a, b)` of naturals
standing for `a - b`. Well-formed instances give every position at least one rotamer, so
`p ≤ R`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SIDE-CHAIN POSITIONING (PROTEIN DESIGN) is NP-complete.** Source: Pierce and Winfree
(2002); Chazelle, Kingsford and Singh (2004). -/
public theorem_wanted sideChainPositioning_npComplete :
    sideChainPositioningDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L sideChainPositioningDec

end MetaMathlibExt.Complexity.NPComplete.SideChainPositioning
