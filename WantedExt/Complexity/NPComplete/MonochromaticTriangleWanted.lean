/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MONOCHROMATIC TRIANGLE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT6] MONOCHROMATIC
TRIANGLE (credited there to S. A. Burr, 1976, unpublished);
M. Schaefer, "Graph Ramsey theory and the polynomial hierarchy", Journal of
Computer and System Sciences 62 (2001), 290-322, doi:10.1006/jcss.2000.1729
(pp. 291-292: Burr's result for `G = H = K₃`, as recorded in [GT6]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MonochromaticTriangle

/-!
# MONOCHROMATIC TRIANGLE is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is there a partition of `E` into two disjoint sets
`E₁, E₂` such that neither `G₁ = (V, E₁)` nor `G₂ = (V, E₂)` contains a triangle?

The partition is given by the subgraph `G₁ ≤ G` with edge set `E₁`; then `G₂ = G \ G₁` has edge
set `E₂ = E \ E₁`. "Contains no triangle" is Mathlib's `CliqueFree 3`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MONOCHROMATIC TRIANGLE is NP-complete.** Source: Garey and Johnson (1979), [GT6]
(S. A. Burr, 1976). -/
public theorem_wanted monochromaticTriangle_npComplete :
    monochromaticTriangleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L monochromaticTriangleDec

end MetaMathlibExt.Complexity.NPComplete.MonochromaticTriangle
