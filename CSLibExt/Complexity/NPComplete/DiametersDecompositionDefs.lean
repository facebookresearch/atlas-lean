/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIAMETERS DECOMPOSITION: definitions

Source:
J. Plesník, "Complexity of decomposing graphs into factors with given diameters or radii",
Mathematica Slovaca 32 (1982), 379-388, Theorem 1 and Section 5 (concluding remarks);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
MINIMUM DIAMETERS DECOMPOSITION (citing Plesník).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DiametersDecomposition

open GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: well-formed for GRAPH COLORING (the edge list describes a
simple graph on `Fin n`), `n ≥ 1`, and `0 < K`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.1 ∧ 0 < i.2.2

/-- The graph decomposes into two edge-disjoint factors `F₁`, `F₂` with equal diameters, the
diameter of `F₁` being at most `K`. -/
def DiametersDecompositionFeasible (i : GraphColoringInstance) : Prop :=
  ∃ F₁ F₂ : SimpleGraph (Fin i.1), F₁ ⊔ F₂ = Graph i ∧ Disjoint F₁ F₂ ∧
    F₁.ediam = F₂.ediam ∧ F₁.ediam ≤ (i.2.2 : ℕ∞)

open Classical in
/-- DIAMETERS DECOMPOSITION as a decision problem over bitstrings. -/
noncomputable def diametersDecompositionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ DiametersDecompositionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DiametersDecomposition
