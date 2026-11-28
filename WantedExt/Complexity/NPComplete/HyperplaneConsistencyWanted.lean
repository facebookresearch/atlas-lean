/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HYPERPLANE CONSISTENCY is NP-complete

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM HYPERPLANE CONSISTENCY;
E. Amaldi and V. Kann, "The complexity and approximability of finding maximum feasible
subsystems of linear relations", Theoretical Computer Science 147 (1995), 181-210,
doi:10.1016/0304-3975(94)00254-G;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP6] OPEN HEMISPHERE;
D. S. Johnson and F. P. Preparata, "The densest hemisphere problem", Theoretical Computer
Science 6 (1978), 93-107, doi:10.1016/0304-3975(78)90006-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HyperplaneConsistencyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HyperplaneConsistency

/-!
# HYPERPLANE CONSISTENCY is NP-complete

INSTANCE: finite sets `P` and `N` of integer `n`-vectors, `n ≥ 1` (`P` the positive examples,
`N` the negative examples), and a positive integer `K ≤ |P| + |N|`.
QUESTION: is there a hyperplane, given by a normal vector `w ∈ ℚⁿ`, `w ≠ 0`, and a bias
`w₀ ∈ ℚ`, such that the number of examples consistent with it,
`|{x ∈ P : w · x > w₀}| + |{x ∈ N : w · x < w₀}|`, is at least `K`?

This is the decision version of MAXIMUM HYPERPLANE CONSISTENCY from the Crescenzi-Kann
compendium, which records it as APX-complete (Amaldi and Kann). The compendium calls
it similar to OPEN HEMISPHERE ([MP6], Garey and Johnson, stated on `main` as
`WantedExt.Complexity.NPComplete.OpenHemisphereWanted`), the homogeneous problem without a
bias and without negative examples; the bound `K ≤ |P| + |N|` follows [MP6]'s `K ≤ |X|`.

Each integer is encoded as a pair of naturals `(positive part, negative part)` representing their
difference (`intOf`), as in `WantedExt.Complexity.NPComplete.ZeroOneILPWanted`; numbers use the
canonical binary encoding. `P` and `N` are lists; since they are sets, `WellFormed` requires
the decoded integer vectors of each to be pairwise distinct, so the counts are counts of
elements of `P` and of `N`. As in the source, `P` and `N` need not be disjoint. A hyperplane
needs a nonzero normal vector, hence `w ≠ 0` and `n ≥ 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HYPERPLANE CONSISTENCY is NP-complete.** Source: Crescenzi and Kann, MAXIMUM HYPERPLANE
CONSISTENCY; Amaldi and Kann (1995). -/
public theorem_wanted hyperplaneConsistency_npComplete :
    hyperplaneConsistencyDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hyperplaneConsistencyDec

end MetaMathlibExt.Complexity.NPComplete.HyperplaneConsistency
