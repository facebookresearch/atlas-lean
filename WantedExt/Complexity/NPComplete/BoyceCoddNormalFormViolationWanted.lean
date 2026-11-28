/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOYCE-CODD NORMAL FORM VIOLATION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR29] BOYCE-CODD NORMAL FORM
VIOLATION, p. 233 (references [Bernstein and Beeri, 1976], [Beeri and Bernstein, 1978];
transformation from HITTING SET);
C. Beeri and P. A. Bernstein, "Computational problems related to the design of normal form
relational schemas", ACM Transactions on Database Systems 4 (1979), 30-59,
doi:10.1145/320064.320066.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BoyceCoddNormalFormViolationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoyceCoddNormalFormViolation

open PrimeAttributeName (attrs deps)

/-!
# BOYCE-CODD NORMAL FORM VIOLATION is NP-complete

INSTANCE: a set `A` of attribute names, a collection `F` of functional dependencies on `A`, and
a subset `A' ⊆ A`.
QUESTION: does `A'` violate Boyce-Codd normal form for the relational system `⟨A, F⟩`, i.e., is
there a subset `X ⊆ A'` and two attribute names `y, z ∈ A' - X` such that `(X, {y}) ∈ F*` and
`(X, {z}) ∉ F*`, where `F*` is the closure of `F`?

The attribute names are `0, …, n - 1`, the elements of `Fin n`; a dependency is a pair of lists
of names, read as the pair of their sets, and `A'` is a list of names, read as its set. These are
`attrs` and `deps` of `PrimeAttributeNameWanted` (GJ [SR28]), whose docstring explains why
CSLibExt's `Cslib.Databases.Derives` (Armstrong's axioms) generates GJ's closure `F*`.

The question is `¬ Cslib.Databases.IsBCNF F A'`, CSLibExt's Boyce-Codd normal form of the scheme
`A'`: every dependency `X → Y` derivable from `F` with `X, Y ⊆ A'` has `Y ⊆ X` or `X → A'`
derivable. A violation in GJ's sense gives `X → {y}` with `{y} ⊈ X` and `X → A'` not derivable
(it would derive `z`). Conversely, a violating `X → Y` gives some `y ∈ Y - X` with `X → {y}`, and
some `z ∈ A'` with `X → {z}` not derivable, so `z ∉ X` by reflexivity.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOYCE-CODD NORMAL FORM VIOLATION is NP-complete.** Source: Garey and Johnson (1979),
[SR29]; Beeri and Bernstein (1979). -/
public theorem_wanted boyceCoddNormalFormViolation_npComplete :
    boyceCoddNormalFormViolationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boyceCoddNormalFormViolationDec

end MetaMathlibExt.Complexity.NPComplete.BoyceCoddNormalFormViolation
