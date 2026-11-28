/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3SAT WITH VARIABLE CYCLE: definitions

Source:
D. Lichtenstein, "Planar formulae and their uses", SIAM Journal on Computing 11(2) (1982),
329-343, doi:10.1137/0211025;
A. Pilz, "Planar 3-SAT with a clause/variable cycle", Discrete Mathematics & Theoretical
Computer Science 21(3) (2019), doi:10.23638/DMTCS-21-3-18.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PlanarThreeSatDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeSatVariableCycle

/-- The incidence graph of the instance together with the variable cycle
`u₀ u₁ ⋯ u_{n-1} u₀`. -/
def VariableCycleGraph (i : PlanarThreeSat.PlanarThreeSatInstance) :
    SimpleGraph (Fin i.1 ⊕ Fin i.2.length) :=
  PlanarThreeSat.IncidenceGraph i ⊔ (SimpleGraph.cycleGraph i.1 ⊕g ⊥)

/-- Well-formedness of an instance: it is a well-formed PLANAR 3SAT instance (at most three
literals per clause, variables in range, planar incidence graph), there are at least three
variables, and the incidence graph together with the variable cycle is planar. -/
def WellFormed (i : PlanarThreeSat.PlanarThreeSatInstance) : Prop :=
  PlanarThreeSat.WellFormed i ∧ 3 ≤ i.1 ∧ (VariableCycleGraph i).IsPlanar

open Classical in
/-- PLANAR 3SAT WITH VARIABLE CYCLE as a decision problem over bitstrings. -/
noncomputable def planarThreeSatVariableCycleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarThreeSat.PlanarThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ PlanarThreeSat.PlanarThreeSatFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeSatVariableCycle
