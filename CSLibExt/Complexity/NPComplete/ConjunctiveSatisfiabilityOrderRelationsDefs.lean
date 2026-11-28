/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES, `≤` and `>` only,: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO16] CONJUNCTIVE SATISFIABILITY
WITH FUNCTIONS AND INEQUALITIES, comment: remains NP-complete even if `=` and `≠` are not used;
V. R. Pratt, "Two easy theories whose combination is hard", technical report, Massachusetts
Institute of Technology (1977), http://boole.stanford.edu/pub/sefnp.pdf.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalitiesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOrderRelations

open MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityFunctionsInequalities

/-- The node `t` of the node list `nodes` has one of Garey and Johnson's shapes: a constant node
is `0` or `1`, and an application node has exactly one argument, which is a variable or a
constant node. -/
def IsGJTermNode (nodes : List TermNode) (t : TermNode) : Prop :=
  (t.1 = 1 → t.2.1.2 = 0 ∧ t.2.1.1 ≤ 1) ∧
    (t.1 = 2 → t.2.2.length = 1 ∧ ∀ j ∈ t.2.2, (nodes.getD j (0, (0, 0), [])).1 ≤ 1)

/-- Well-formedness of an instance: the general problem's well-formedness, every node has one of
Garey and Johnson's term shapes, and every clause uses `≤` (`0`) or `>` (`1`). -/
def WellFormed (i : ConjunctiveSatisfiabilityInstance) : Prop :=
  ConjunctiveSatisfiabilityFunctionsInequalities.WellFormed i ∧
    (∀ t ∈ i.1, IsGJTermNode i.1 t) ∧ ∀ l ∈ i.2, l.1 ≤ 1

open Classical in
/-- CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES restricted to `≤` and `>`, as a
decision problem over bitstrings. -/
noncomputable def orderRelationsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConjunctiveSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ ConjunctiveSatisfiabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOrderRelations
