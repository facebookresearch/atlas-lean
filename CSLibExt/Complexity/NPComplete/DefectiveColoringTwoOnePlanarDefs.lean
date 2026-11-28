/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# (2,1)-DEFECTIVE COLORING of planar graphs: definitions

Source:
L. J. Cowen, W. Goddard and C. E. Jesurum, "Defective coloring revisited", Journal of Graph
Theory 24(3) (1997), 205-219, doi:10.1002/(SICI)1097-0118(199703)24:3<205::AID-JGT2>3.0.CO;2-T
(abstract: "the (2, 1)-coloring and the (3, 1)-coloring problems are NP-complete even for
planar graphs").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DefectiveColoringTwoOnePlanar

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev DefectiveColoringTwoOnePlanarInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : DefectiveColoringTwoOnePlanarInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, and the
graph is planar. -/
def WellFormed (i : DefectiveColoringTwoOnePlanarInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsPlanar

open Classical in
/-- The graph is `(2, 1)`-colorable: some coloring `c` with `2` colors gives every vertex at
most `1` neighbor of its own color. -/
def DefectiveColoringTwoOnePlanarFeasible (i : DefectiveColoringTwoOnePlanarInstance) : Prop :=
  ∃ c : Fin i.1 → Fin 2, ∀ v : Fin i.1,
    (((Graph i).neighborFinset v).filter fun u => c u = c v).card ≤ 1

open Classical in
/-- (2,1)-DEFECTIVE COLORING of planar graphs as a decision problem over bitstrings. -/
noncomputable def defectiveColoringTwoOnePlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DefectiveColoringTwoOnePlanarInstance) x with
  | some i => decide (WellFormed i ∧ DefectiveColoringTwoOnePlanarFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DefectiveColoringTwoOnePlanar
