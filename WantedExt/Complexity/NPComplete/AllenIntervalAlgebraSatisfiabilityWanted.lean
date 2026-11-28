/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALLEN INTERVAL ALGEBRA SATISFIABILITY is NP-complete

Source:
M. Vilain and H. Kautz, "Constraint propagation algorithms for temporal reasoning",
Proceedings of the Fifth National Conference on Artificial Intelligence (AAAI-86), 1986,
377-382, Theorem 2 ("Determining the satisfiability of a set of assertions in the interval
algebra is NP-hard", by a reduction from 3SAT); revised version: M. Vilain, H. Kautz and
P. van Beek, "Constraint propagation algorithms for temporal reasoning: a revised report", in
*Readings in Qualitative Reasoning about Physical Systems*, Morgan Kaufmann (1990), 373-381,
doi:10.1016/B978-1-4832-1447-4.50034-1. The interval algebra is that of J. F. Allen,
"Maintaining knowledge about temporal intervals", Communications of the ACM 26(11) (1983),
832-843, doi:10.1145/182.358434.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AllenIntervalAlgebraSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AllenIntervalAlgebraSatisfiability

/-!
# ALLEN INTERVAL ALGEBRA SATISFIABILITY is NP-complete

INSTANCE: interval variables `I₀, …, I_{n-1}` and a finite set of assertions `Iᵢ (R) Iⱼ`, where
each `R` is a set of Allen's thirteen simple relations, read as their disjunction.
QUESTION: is there an assignment of a real interval `[sᵢ, eᵢ]` with `sᵢ < eᵢ` to every variable
such that, for every assertion `Iᵢ (R) Iⱼ`, the intervals `Iᵢ` and `Iⱼ` stand in one of the
simple relations of `R`?

The thirteen simple relations (`simpleRel`, codes `0, …, 12`) compare the endpoints of `Iᵢ` and
`Iⱼ`, as in Allen (1983): before, after, meets, met-by, overlaps, overlapped-by, starts,
started-by, during, contains, finishes, finished-by, and equals. For intervals of positive
length exactly one of them holds. An assertion is a triple `(i, j, R)` with `R` a list of codes;
the empty list is the empty disjunction, which no assignment satisfies. Several assertions may
concern the same pair; they all have to hold. The problem is in NP: a variable that occurs in no
assertion can take any interval of positive length, and for the at most `2m` variables occurring
in the `m` assertions only the relative order of their endpoints matters, so a certificate
assigns them endpoints in `{0, …, 4m - 1}`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ALLEN INTERVAL ALGEBRA SATISFIABILITY is NP-complete.** NP-hardness: Vilain and Kautz
(1986), Theorem 2; membership in NP: the endpoint-order certificate of the module docstring. -/
public theorem_wanted allenIntervalAlgebraSatisfiability_npComplete :
    allenIntervalAlgebraSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L allenIntervalAlgebraSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.AllenIntervalAlgebraSatisfiability
