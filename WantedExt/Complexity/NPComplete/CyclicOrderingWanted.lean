/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CYCLIC ORDERING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS2] CYCLIC ORDERING;
Z. Galil and N. Megiddo, "Cyclic ordering is NP-complete", Theoretical Computer
Science 5 (1977), 179-182, doi:10.1016/0304-3975(77)90005-6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CyclicOrderingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CyclicOrdering

/-!
# CYCLIC ORDERING is NP-complete

INSTANCE: a finite set `A` and a collection `C` of ordered triples `(a, b, c)` of distinct
elements of `A`. QUESTION: is there a one-to-one function `f : A → {1, 2, ..., |A|}` such that,
for each `(a, b, c) ∈ C`, either `f(a) < f(b) < f(c)` or `f(b) < f(c) < f(a)` or
`f(c) < f(a) < f(b)`?

The set is `A = Fin n` and the target `{1, ..., n}` is `Fin n` (shifting the values by one does
not change any comparison). A one-to-one `f : Fin n → Fin n` is a bijection, i.e. a linear
order of `A`, and the condition says that `a`, `b`, `c` occur in this cyclic order around it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CYCLIC ORDERING is NP-complete.** Source: Garey and Johnson (1979), [MS2]; Galil and
Megiddo (1977). -/
public theorem_wanted cyclicOrdering_npComplete :
    cyclicOrderingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cyclicOrderingDec

end MetaMathlibExt.Complexity.NPComplete.CyclicOrdering
