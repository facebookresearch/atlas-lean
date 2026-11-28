/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE CONSTRAINED SCHEDULING with two processors, chains and a unit resource: definitions

Source:
J. Błażewicz, J. K. Lenstra and A. H. G. Rinnooy Kan, "Scheduling subject to resource constraints:
classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24,
doi:10.1016/0166-218X(83)90012-4, Theorem 7 ("P2|res111, chain, p_j = 1|C_max is NP-hard in the
strong sense", by a transformation from 3-PARTITION; read in the Mathematisch Centrum preprint
BW 127/80 of the same title);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SS10] RESOURCE CONSTRAINED SCHEDULING.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedenceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResource

open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedScheduling (bound)
open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingPrecedenceZeroOrBound
  (PrecedenceResourceSchedulingInstance PrecedenceWellFormed PrecedenceFeasible)
open MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingForestPrecedence
  (ImmediatePredecessor)

/-- The partial order is a set of chains: no task has more than one immediate successor, and no
task has more than one immediate predecessor. -/
def IsChains (i : PrecedenceResourceSchedulingInstance) : Prop :=
  (∀ t a b, ImmediatePredecessor i t a → ImmediatePredecessor i t b → a = b) ∧
    ∀ t a b, ImmediatePredecessor i a t → ImmediatePredecessor i b t → a = b

/-- Well-formedness of an instance: it is well-formed for RESOURCE CONSTRAINED SCHEDULING with a
partial order, `m = 2`, `r = 1`, the resource has size `B_1 = 1`, and the partial order is a set
of chains. -/
def WellFormed (i : PrecedenceResourceSchedulingInstance) : Prop :=
  PrecedenceWellFormed i ∧ i.1.1 = 2 ∧ i.1.2.1 = 1 ∧ bound i.1 0 = 1 ∧ IsChains i

open Classical in
/-- RESOURCE CONSTRAINED SCHEDULING with two processors, chains and a unit resource as a decision
problem over bitstrings. -/
noncomputable def resourceConstrainedSchedulingChainsUnitResourceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PrecedenceResourceSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ PrecedenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ResourceConstrainedSchedulingChainsUnitResource
