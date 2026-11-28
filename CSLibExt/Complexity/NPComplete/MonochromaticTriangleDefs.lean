/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOCHROMATIC TRIANGLE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT6] MONOCHROMATIC
TRIANGLE (credited there to S. A. Burr, 1976, unpublished);
M. Schaefer, "Graph Ramsey theory and the polynomial hierarchy", Journal of
Computer and System Sciences 62 (2001), 290-322, doi:10.1006/jcss.2000.1729
(pp. 291-292: Burr's result for `G = H = K₃`, as recorded in [GT6]).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonochromaticTriangle

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev MonochromaticTriangleInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MonochromaticTriangleInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : MonochromaticTriangleInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The edges split into two triangle-free parts: a subgraph `G₁ ≤ G` such that neither `G₁`
nor its complement `G \ G₁` in `G` contains a triangle. -/
def MonochromaticTriangleFeasible (i : MonochromaticTriangleInstance) : Prop :=
  ∃ G₁ : SimpleGraph (Fin i.1), G₁ ≤ Graph i ∧ G₁.CliqueFree 3 ∧ (Graph i \ G₁).CliqueFree 3

open Classical in
/-- MONOCHROMATIC TRIANGLE as a decision problem over bitstrings. -/
noncomputable def monochromaticTriangleDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MonochromaticTriangleInstance) x with
  | some i => decide (WellFormed i ∧ MonochromaticTriangleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MonochromaticTriangle
