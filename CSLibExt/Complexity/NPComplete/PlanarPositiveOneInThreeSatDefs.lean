/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR POSITIVE ONE-IN-THREE 3SAT: definitions

Source:
C. Moore and J. M. Robson, "Hard tiling problems with simple tiles", Discrete and Computational
Geometry 26 (2001), 573-590, doi:10.1007/s00454-001-0047-6 (arXiv:math/0003039), Section 3.1:
"Planar Monotone 1-in-3 SAT is NP-complete" (credited there to P. Laroche, "Planar 1-in-3
satisfiability is NP-complete", ASMICS Workshop on Tilings, ENS Lyon, 1992), and NP-complete
even when every variable occurs exactly three times.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import CSLibExt.Complexity.NPComplete.PlanarThreeSatDefs
public import CSLibExt.Complexity.NPComplete.PositiveOneInThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarPositiveOneInThreeSat

open MetaMathlibExt.Complexity.NPComplete.OneInThreeSat
  (OneInThreeSatInstance OneInThreeSatFeasible)

/-- Well-formedness of an instance: it is well-formed for POSITIVE ONE-IN-THREE 3SAT (three
literals per clause, variables `< n`, no negated literal), and the variable-clause graph is
planar. -/
def WellFormed (i : OneInThreeSatInstance) : Prop :=
  PositiveOneInThreeSat.WellFormed i ∧ (PlanarThreeSat.IncidenceGraph i).IsPlanar

open Classical in
/-- PLANAR POSITIVE ONE-IN-THREE 3SAT as a decision problem over bitstrings. -/
noncomputable def planarPositiveOneInThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneInThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ OneInThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarPositiveOneInThreeSat
