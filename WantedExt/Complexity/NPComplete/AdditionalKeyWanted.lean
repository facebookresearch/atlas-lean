/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ADDITIONAL KEY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR27] ADDITIONAL KEY, p. 232
(reference [Beeri and Bernstein, 1978]; transformation from HITTING SET), with the closure
`F*` as defined in [SR26] MINIMUM CARDINALITY KEY, p. 232;
C. Beeri and P. A. Bernstein, "Computational problems related to the design of normal form
relational schemas", ACM Transactions on Database Systems 4 (1979), 30-59,
doi:10.1145/320064.320066.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AdditionalKeyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AdditionalKey

/-!
# ADDITIONAL KEY is NP-complete

INSTANCE: a set `A` of attribute names, a collection `F` of functional dependencies on `A`,
a subset `R ⊆ A`, and a set `K` of keys for the relational scheme `⟨R, F⟩`.
QUESTION: does `R` have a key not already contained in `K`, i.e., is there an `R' ⊆ R` such
that `R' ∉ K`, `(R', R) ∈ F*`, and for no `R'' ⊂ R'` is `(R'', R) ∈ F*`?

A functional dependency on `A` is an ordered pair of subsets of `A`. `(R', R) ∈ F*` is CSLibExt's
`Cslib.Databases.Derives F ⟨R', R⟩`, derivability by Armstrong's axioms (reflexivity,
augmentation, transitivity). Garey and Johnson define `F*` ([SR26]) as the least set with (1)
`F ⊆ F*`, (2) `B ⊆ C ⊆ A` implies `(C, B) ∈ F*`, (3) `(B, C), (C, D) ∈ F*` implies
`(B, D) ∈ F*`, and (4) `(B, C), (B, D) ∈ F*` implies `(B, C ∪ D) ∈ F*`; both rule sets are
sound and complete for implication of functional dependencies
(`Cslib.Databases.derives_iff_entails`), so they generate the same closure. A key for
`⟨R, F⟩` is a minimal subset `R' ⊆ R` with `(R', R) ∈ F*`: no proper subset `R'' ⊂ R'` has
`(R'', R) ∈ F*`. Garey and Johnson print the last clause with `⊆`; read literally,
`R'' = R'` would contradict `(R', R) ∈ F*`, so the clause means proper subsets, as the
definition of a key requires.

The attribute names are `0, …, n - 1`, the elements of `Fin n`; a dependency is a pair of
lists of names (`deps`), and `R` and each member of `K` are lists of names, all read as sets
(`attrs`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ADDITIONAL KEY is NP-complete.** Source: Garey and Johnson (1979), [SR27]; Beeri and
Bernstein (1979). -/
public theorem_wanted additionalKey_npComplete :
    additionalKeyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L additionalKeyDec

end MetaMathlibExt.Complexity.NPComplete.AdditionalKey
