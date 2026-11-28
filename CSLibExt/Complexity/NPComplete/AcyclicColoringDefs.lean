/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACYCLIC COLORING: definitions

Source:
T. F. Coleman and J.-Y. Cai, "The cyclic coloring problem and estimation of sparse Hessian
matrices", SIAM Journal on Algebraic and Discrete Methods 7(2) (1986), 221-235,
doi:10.1137/0607026, Theorem 3.1;
A. V. Kostochka, *Upper bounds of chromatic functions of graphs* (in Russian), doctoral thesis,
Novosibirsk (1978);
Shalu M. A. and C. Antony, "Hardness transitions and uniqueness of acyclic colouring", Discrete
Applied Mathematics 345 (2024), 77-98, doi:10.1016/j.dam.2023.11.030, Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AcyclicColoring

open GraphColoring (GraphColoringInstance Graph)
open MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted (IsAcyclicColoring)

/-- Well-formedness of an instance: well-formed for GRAPH COLORING (the edge list describes a
simple graph on `Fin n`), and `0 < K`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2

/-- The graph has an acyclic coloring with `K` colors: a proper coloring by `Fin K` in which
every two color classes induce a forest. -/
def AcyclicColoringFeasible (i : GraphColoringInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.2, IsAcyclicColoring (Graph i) f

open Classical in
/-- ACYCLIC COLORING as a decision problem over bitstrings. -/
noncomputable def acyclicColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ AcyclicColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AcyclicColoring
