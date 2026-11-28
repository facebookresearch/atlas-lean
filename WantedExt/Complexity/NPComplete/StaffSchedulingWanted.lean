/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STAFF SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SS20] STAFF SCHEDULING
(reference: [Garey and Johnson, ----], unpublished; transformation from X3C), p. 243;
J. J. Bartholdi, J. B. Orlin and H. D. Ratliff, "Cyclic scheduling via integer programs with
circular ones", Operations Research 28 (1980), 1074-1085, doi:10.1287/opre.28.5.1074 (the
polynomial case of the comment).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StaffSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StaffScheduling

/-!
# STAFF SCHEDULING is NP-complete

INSTANCE: positive integers `m` and `k`, a collection `C` of `m`-tuples, each having `k` 1's and
`m - k` 0's (representing possible worker schedules), a "requirement" `m`-tuple `R` of
non-negative integers, and a number `n` of workers.
QUESTION: is there a schedule `f : C → ℤ₀⁺` such that `∑_{c ∈ C} f(c) ≤ n` and such that
`∑_{c ∈ C} f(c) · c ≥ R` (componentwise)?

Garey and Johnson record the NP-completeness as their own unpublished result, a transformation
from EXACT COVER BY 3-SETS; their comment adds that the problem is solvable in polynomial time
when every tuple of `C` has the cyclic one's property (Bartholdi, Orlin and Ratliff). The
reduction uses requirements in `{0, 1}`, so the problem is NP-complete in the strong sense.
Membership in NP: `f` is a certificate, and its values are at most `n`.

The collection `C` is a list of tuples, each a list of `m` Booleans (`true` for a 1); a tuple may
occur more than once in the collection. `k ≤ m` is stated separately, since an empty collection
would not enforce it. `R` is a list of `m` natural numbers. The schedule `f`
assigns a number of workers to each listed tuple. Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STAFF SCHEDULING is NP-complete.** Source: Garey and Johnson (1979), [SS20]
(Garey and Johnson, unpublished). -/
public theorem_wanted staffScheduling_npComplete :
    staffSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L staffSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.StaffScheduling
