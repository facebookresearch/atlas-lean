/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM K-SATISFIABILITY is NP-complete for every fixed k ≥ 2

Source:
M. R. Garey, D. S. Johnson and L. Stockmeyer, "Some simplified NP-complete graph problems",
Theoretical Computer Science 1(3) (1976), 237-267, doi:10.1016/0304-3975(76)90059-1
(MAXIMUM 2-SATISFIABILITY);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO5] MAXIMUM 2-SATISFIABILITY;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MAXIMUM K-SATISFIABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaxSatWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumKSatisfiability

open MaxSat (MaxSatInstance MaxSatFeasible)

/-!
# MAXIMUM K-SATISFIABILITY is NP-complete for every fixed k ≥ 2

Fix a constant `k ≥ 2`.
INSTANCE: a set `U` of variables, a collection `C` of disjunctive clauses of at most `k` literals
over `U`, and a positive integer `K`.
QUESTION: is there a truth assignment for `U` that satisfies at least `K` clauses of `C`?

This is the decision version of the compendium's MAXIMUM K-SATISFIABILITY, one problem for each
constant `k`. For `k = 2` it is MAXIMUM 2-SATISFIABILITY (`MaxTwoSatWanted`, Garey and Johnson
[LO5]), proved NP-complete by Garey, Johnson and Stockmeyer. For `k ≥ 2`, a well-formed MAX
2-SAT instance with `K > 0` is a well-formed instance for `k` with the same answer. The map that
decodes its input, keeps such an instance unchanged, sends a well-formed MAX 2-SAT instance with
`K = 0` (a yes-instance) to a fixed yes-instance, and sends every other bitstring (undecodable,
malformed, or with a clause of more than two literals) to a fixed no-instance is therefore a
polynomial-time reduction from MAX 2-SAT, so every fixed `k ≥ 2` is NP-hard; membership in NP
holds for any `k` (an assignment is a certificate). For `k = 1` the problem is polynomial
(satisfy, for each variable, the more frequent of its two literals), so the theorem quantifies
over `k ≥ 2`.

The instance (variable count, CNF formula as in `Cslib.Logic.LegacyPL.CNF`, bound `K`), the variable
range condition and the question (an assignment and a sub-list of at least `K` satisfied
clauses) are those of MAXIMUM SATISFIABILITY (`MaxSatWanted`); `WellFormed k` adds that every
clause has at most `k` literals, as `MaxTwoSatWanted` does for `k = 2`, and that `K` is positive
(the source's "positive integer K").

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the constant `k`: a well-formed MAXIMUM SATISFIABILITY
instance (variables below the variable count) in which every clause has at most `k` literals,
and `0 < K`. -/
def WellFormed (k : ℕ) (i : MaxSatInstance) : Prop :=
  MaxSat.WellFormed i ∧ (∀ clause ∈ i.2.1, clause.length ≤ k) ∧ 0 < i.2.2

open Classical in
/-- MAXIMUM K-SATISFIABILITY for the constant `k` as a decision problem over bitstrings. -/
noncomputable def maximumKSatisfiabilityDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxSatInstance) x with
  | some i => decide (WellFormed k i ∧ MaxSatFeasible i)
  | none => false

/-- **MAXIMUM K-SATISFIABILITY is NP-complete for every fixed `k ≥ 2`.** Source: Garey, Johnson
and Stockmeyer (1976); Garey and Johnson (1979), [LO5]; Crescenzi and Kann, MAXIMUM
K-SATISFIABILITY. -/
public theorem_wanted maximumKSatisfiability_npComplete (k : ℕ) (hk : 2 ≤ k) :
    maximumKSatisfiabilityDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (maximumKSatisfiabilityDec k)

end MetaMathlibExt.Complexity.NPComplete.MaximumKSatisfiability
