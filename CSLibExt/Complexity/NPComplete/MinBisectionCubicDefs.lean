/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BISECTION on 3-regular graphs: definitions

Source:
T. N. Bui, S. Chaudhuri, F. T. Leighton and M. Sipser, "Graph bisection algorithms with good
average case behavior", Combinatorica 7(2) (1987), 171-191, doi:10.1007/BF02579448;
L. Lichev and D. Mitsche, "On the minimum bisection of random 3-regular graphs", The Electronic
Journal of Combinatorics 30(2) (2023), doi:10.37236/11085, Section 1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND17] MINIMUM CUT INTO BOUNDED SETS.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinBisectionDefs
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinBisectionCubic

open MinBisection (MinBisectionInstance MinBisectionFeasible)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MinBisectionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: well-formed for MINIMUM BISECTION (`n` even, a simple edge
list on `0, …, n - 1`), and the graph is 3-regular. -/
def WellFormed (i : MinBisectionInstance) : Prop :=
  MinBisection.WellFormed i ∧ (Graph i).IsRegularOfDegree 3

open Classical in
/-- MINIMUM BISECTION on 3-regular graphs as a decision problem over bitstrings. -/
noncomputable def minBisectionCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinBisectionInstance) x with
  | some i => decide (WellFormed i ∧ MinBisectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinBisectionCubic
