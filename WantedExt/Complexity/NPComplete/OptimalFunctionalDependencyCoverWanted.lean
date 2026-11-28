/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES is NP-complete

Source:
D. Maier, "Minimum covers in the relational database model", Journal of the ACM 27 (1980),
664-674, doi:10.1145/322217.322223;
D. Maier, *The Theory of Relational Databases*, Computer Science Press (1983), Chapter 5,
Definition 5.1 and Section 5.7 (optimal covers; finding one is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.OptimalFunctionalDependencyCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalFunctionalDependencyCover

/-!
# OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES is NP-complete

INSTANCE: a set `U` of attributes, a set `F` of functional dependencies over `U`, and an integer
`K`.
QUESTION: is there a set `G` of functional dependencies over `U` equivalent to `F` (`F⁺ = G⁺`)
whose size, the number of attribute symbols `∑_{X → Y ∈ G} (|X| + |Y|)`, is at most `K`?

Maier (1980) calls a set of dependencies *optimal* when no equivalent set has fewer attribute
symbols, and proves that finding an optimal cover is NP-complete; his book (1983, Section 5.7)
measures `{AB → C, CD → E, AC → IJ}` as size `10`.

The attributes are `U = {0, ..., a - 1}`, as `Fin a`. Each functional dependency of `F` is a pair
of attribute lists, read as the dependency `Cslib.Databases.FD` between the two attribute sets;
`MinimumCardinalityKey.deps` turns the list into the set `F`. Two sets of dependencies are
equivalent (`Cslib.Databases.Equivalent`) when each derives every dependency of the other with
Armstrong's axioms (`Cslib.Databases.Derives`); this is `F⁺ = G⁺` (Maier's Definition 5.1), and by
Armstrong's theorem (`Cslib.Databases.derives_iff_entails`) it is the same as semantic
implication.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES is NP-complete.** Source: Maier (1980). -/
public theorem_wanted optimalFunctionalDependencyCover_npComplete :
    optimalFunctionalDependencyCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimalFunctionalDependencyCoverDec

end MetaMathlibExt.Complexity.NPComplete.OptimalFunctionalDependencyCover
