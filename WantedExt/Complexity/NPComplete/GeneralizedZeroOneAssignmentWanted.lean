/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED 0-1 ASSIGNMENT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM GENERALIZED 0-1 ASSIGNMENT, citing S. Sahni and T. Gonzalez,
"P-complete approximation problems", Journal of the ACM 23(3) (1976), 555-565,
doi:10.1145/321958.321975;
S. Martello and P. Toth, *Knapsack Problems: Algorithms and Computer Implementations*, Wiley
(1990), Section 7.1, p. 190 (even the feasibility question of the generalized assignment problem
is NP-complete, by a reduction from PARTITION with two knapsacks).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedZeroOneAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedZeroOneAssignment

/-!
# GENERALIZED 0-1 ASSIGNMENT is NP-complete

INSTANCE: an integer `m × n` matrix `A ∈ ℤ^{m·n}`, an integer `m`-vector `b ∈ ℤ^m`, a binary
`m × n` matrix `C ∈ {0, 1}^{m·n}`, and a positive integer `K`.
QUESTION: is there a binary `m × n` matrix `X ∈ {0, 1}^{m·n}` with exactly one `1` in each
column, such that `∑_{j = 1}^{n} A_{i,j} X_{i,j} ≤ b_i` for all `i ∈ [1..m]` and
`∑_{i = 1}^{m} ∑_{j = 1}^{n} C_{i,j} X_{i,j} ≤ K`?

This is the decision version, with bound `K`, of MINIMUM GENERALIZED 0-1 ASSIGNMENT in the
Crescenzi-Kann compendium (rows are knapsacks or agents, columns are items or jobs; each column
is assigned to the row holding its `1`). Indices are `0`-based: rows `Fin m`, columns `Fin n`.

Encoding: binary encoding. Each entry of `A` and `b` is a pair of naturals `(positive part,
negative part)` standing for their difference, as in `ZeroOneILP`; `A` and `C` are lists of
`m` rows of length `n`. The instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED 0-1 ASSIGNMENT is NP-complete.** Source: Crescenzi and Kann, MINIMUM GENERALIZED
0-1 ASSIGNMENT, citing Sahni and Gonzalez (1976); Martello and Toth (1990), Section 7.1. -/
public theorem_wanted generalizedZeroOneAssignment_npComplete :
    generalizedZeroOneAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedZeroOneAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedZeroOneAssignment
