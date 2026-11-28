/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO12] INEQUIVALENCE OF PROGRAMS
WITH ASSIGNMENTS;
P. J. Downey and R. Sethi, "Assignment commands and array structures", Proceedings of the
17th Annual Symposium on Foundations of Computer Science (1976), 57-66,
doi:10.1109/SFCS.1976.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.InequivalenceProgramsAssignmentsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignments

/-!
# INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS is NP-complete

Given a finite set `X` of variables, two programs `P₁` and `P₂`, each a sequence of assignments
of the form `x₀ ← if x₁ = x₂ then x₃ else x₄` with the `xᵢ` in `X`, and a value set `V`, is
there an initial assignment of a value from `V` to each variable in `X` such that the two
programs yield different final values for some variable in `X`?

The variables are `0, …, n - 1` and every assignment names only variables (`WellFormed`). The
programs only compare and copy values, so only `|V|` matters: the value set is
`{0, …, |V| - 1}`, given by its size. A program runs its assignments left to right on a store
`ℕ → ℕ`, each assignment updating its target `x₀` from the values the store held before it.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INEQUIVALENCE OF PROGRAMS WITH ASSIGNMENTS is NP-complete.** Source: Garey and Johnson
(1979), [PO12]; Downey and Sethi (1976). -/
public theorem_wanted inequivalenceProgramsAssignments_npComplete :
    inequivalenceProgramsAssignmentsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceProgramsAssignmentsDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceProgramsAssignments
