/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONSISTENT 2-TERM DNF is NP-complete

Source:
L. Pitt and L. G. Valiant, "Computational limitations on learning from examples", Journal of
the ACM 35(4) (1988), 965-984, doi:10.1145/48014.63140 (disjunctions of two monomials, i.e.
2-term DNF, cannot be learned by 2-term DNF hypotheses unless RP = NP; the reduction shows that
deciding whether some 2-term DNF is consistent with given examples is NP-complete);
S. Ghoshal and R. Saket, "Hardness of learning DNFs using halfspaces", arXiv:1911.06358
(Section 1: "it is NP-hard to properly learn a t-term DNF [PV88], for any t ≥ 2").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ConsistentTwoTermDNFDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConsistentTwoTermDNF

open MetaMathlibExt.Complexity.KeyTheorems.KarpLuby (dnfSat)

/-!
# CONSISTENT 2-TERM DNF is NP-complete

INSTANCE: a number `n` of Boolean variables `x₀, …, x_{n-1}`, a list of positive examples and a
list of negative examples, each a vector in `{0,1}ⁿ`. QUESTION: is there a DNF formula over
`x₀, …, x_{n-1}` with at most two terms that is true on every positive example and false on
every negative example?

A DNF formula is a list of terms, each term a list of literals `(variable, polarity)`, and is
true under an assignment iff all literals of some term hold (`dnfSat`, reused from
`WantedExt.Complexity.KeyTheorems.KarpLubyWanted`, where the same representation is used).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONSISTENT 2-TERM DNF is NP-complete.** Source: Pitt and Valiant (1988). -/
public theorem_wanted consistentTwoTermDNF_npComplete :
    consistentTwoTermDNFDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L consistentTwoTermDNFDec

end MetaMathlibExt.Complexity.NPComplete.ConsistentTwoTermDNF
