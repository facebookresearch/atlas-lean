/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POSITIVE ONE-IN-THREE 3SAT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO4] ONE-IN-THREE 3SAT (comment:
remains NP-complete if no clause contains a negated literal);
T. J. Schaefer, "The complexity of satisfiability problems", Proc. 10th Annual ACM Symposium on
Theory of Computing (STOC 1978), 216-226, doi:10.1145/800133.804350.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OneInThreeSatWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PositiveOneInThreeSat

/-!
# POSITIVE ONE-IN-THREE 3SAT is NP-complete

INSTANCE: a set `U` of variables and a collection `C` of clauses over `U` such that each clause
has three literals and no clause contains a negated literal. QUESTION: is there a truth
assignment for `U` such that each clause in `C` has exactly one true literal?

This is the restriction of ONE-IN-THREE 3SAT ([LO4], `OneInThreeSatWanted`) to clauses without
negated literals: Schaefer's ONE-IN-THREE SATISFIABILITY, "whether an arbitrary conjunction of
clauses of the form `R(x, y, z)` is satisfiable", where `R(x, y, z)` holds iff exactly one of
`x, y, z` is true. The instance type and the question are the parent's
(`OneInThreeSat.OneInThreeSatInstance`, `OneInThreeSat.OneInThreeSatFeasible`); `WellFormed` is
the parent's plus the restriction. In `Cslib.Logic.PL.CNF` a literal `(x, b)` is true under `t`
iff `t x = b`, so a positive literal is `(x, true)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (three literals per clause, variables `< n`),
and every literal is positive. -/
def WellFormed (i : OneInThreeSat.OneInThreeSatInstance) : Prop :=
  OneInThreeSat.WellFormed i ∧ ∀ clause ∈ i.2, ∀ l ∈ clause, l.2 = true

open Classical in
/-- POSITIVE ONE-IN-THREE 3SAT as a decision problem over bitstrings. -/
noncomputable def positiveOneInThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneInThreeSat.OneInThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ OneInThreeSat.OneInThreeSatFeasible i)
  | none => false

/-- **POSITIVE ONE-IN-THREE 3SAT is NP-complete.** Source: Garey and Johnson (1979), [LO4];
Schaefer (1978). -/
public theorem_wanted positiveOneInThreeSat_npComplete :
    positiveOneInThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L positiveOneInThreeSatDec

end MetaMathlibExt.Complexity.NPComplete.PositiveOneInThreeSat
