/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UPPER DOMINATION: definitions

Source:
G. A. Cheston, G. Fricke, S. T. Hedetniemi and D. P. Jacobs, "On the computational complexity of
upper fractional domination", Discrete Applied Mathematics 27(3) (1990), 195-207,
doi:10.1016/0166-218X(90)90065-K.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import Mathlib.Order.Defs.Unbundled
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UpperDomination

open MetaMathlibExt.Complexity.NPComplete.DominatingSet (DominatingSetInstance Graph)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`DominatingSet.WellFormed`), and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some minimal dominating set has at least `K` vertices. -/
def UpperDominationFeasible (i : DominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), i.2.2 ≤ S.card ∧ Minimal (Graph i).IsDominating (S : Set (Fin i.1))

open Classical in
/-- UPPER DOMINATION as a decision problem over bitstrings. -/
noncomputable def upperDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ UpperDominationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UpperDomination
