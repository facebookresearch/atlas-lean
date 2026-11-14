/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES with two variables is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 278, problem [PO19]
NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES (reference: Constable, Hunt, and Sahni, 1974, a
Cornell technical report; comment: remains NP-complete for `|X| = 2`);
H. B. Hunt III, R. L. Constable, and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031, the
journal paper of that work.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesTwoVariables

/-!
# NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES with two variables is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a set `X` of variables
with `|X| = 2`, and a loop-free monadic program scheme `S` over `F`, `P` and `X` (a sequence
of instructions `x ← f(y)`, `if p(x) then goto I_j else goto I_k` and `halt`, with no directed
cycle in the flow graph). QUESTION: is `S` non-free, i.e., is there a directed path in the flow
graph for `S` that can never be followed in any computation, no matter what the interpretation
of the functions and predicates in `F` and `P` and the initial values for the variables in `X`?

This is the restriction of
`WantedExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesWanted` to two variables.
The instance type, the flow graph, the parent well-formedness condition and the question are
that module's (`NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesInstance`,
`NonFreedomForLoopFreeProgramSchemes.FlowArc`, `NonFreedomForLoopFreeProgramSchemes.WellFormed`,
`NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesFeasible`); there `X`
is `{0, ..., |X| - 1}` with `|X|` the third component of the instance, and `WellFormed` adds
`|X| = 2`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed NON-FREEDOM FOR LOOP-FREE PROGRAM
SCHEMES instance (well-formed instructions, acyclic flow graph) with exactly two variables. -/
def WellFormed
    (i : NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesInstance) :
    Prop :=
  NonFreedomForLoopFreeProgramSchemes.WellFormed i ∧ i.2.2.1 = 2

open Classical in
/-- NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES with two variables as a decision problem over
bitstrings. -/
noncomputable def nonFreedomForLoopFreeProgramSchemesTwoVariablesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesInstance)
      x with
  | some i =>
    decide (WellFormed i ∧
      NonFreedomForLoopFreeProgramSchemes.NonFreedomForLoopFreeProgramSchemesFeasible i)
  | none => false

/-- **NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES is NP-complete with two variables.** Source:
Garey and Johnson (1979), [PO19]; Constable, Hunt, and Sahni (1974; journal version 1980). -/
public theorem_wanted nonFreedomForLoopFreeProgramSchemesTwoVariables_npComplete :
    nonFreedomForLoopFreeProgramSchemesTwoVariablesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonFreedomForLoopFreeProgramSchemesTwoVariablesDec

end MetaMathlibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemesTwoVariables
