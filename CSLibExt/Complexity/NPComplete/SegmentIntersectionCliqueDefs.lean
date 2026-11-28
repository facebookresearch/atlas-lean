/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE in segment intersection graphs (SEG): definitions

Source:
S. Cabello, J. Cardinal and S. Langerman, "The clique problem in ray intersection graphs",
Discrete & Computational Geometry 50 (2013), 771-783, doi:10.1007/s00454-013-9538-5
(arXiv:1111.5986);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE;
ISGCI (https://www.graphclasses.org/classes/gc_862.html), problem "Clique" on SEG graphs:
NP-complete, with the attribution to Cabello, Cardinal and Langerman.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import CSLibExt.Complexity.NPComplete.RayIntersectionCliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SegmentIntersectionClique

open RayIntersectionClique (toInt)

/-- A point with integer coordinates `(x, y)`, each encoded as a pair of naturals. -/
abbrev IntPoint := (ℕ × ℕ) × (ℕ × ℕ)

/-- A segment, given by its two endpoints. -/
abbrev Seg := IntPoint × IntPoint

/-- An instance: the segments and the bound `K`. -/
abbrev SegmentIntersectionCliqueInstance := List Seg × ℕ

/-- The point of the real plane with the encoded integer coordinates. -/
def toPoint (p : IntPoint) : ℝ × ℝ := ((toInt p.1 : ℝ), (toInt p.2 : ℝ))

/-- The point set of a segment: the closed segment between its endpoints. -/
def segPoints (σ : Seg) : Set (ℝ × ℝ) :=
  SimpleGraph.Segment (toPoint σ.1) (toPoint σ.2)

/-- The intersection graph of the segments: one vertex per list entry, two distinct entries
adjacent when their segments share a point. -/
def Graph (i : SegmentIntersectionCliqueInstance) : SimpleGraph (Fin i.1.length) :=
  SimpleGraph.fromRel fun a b => (segPoints (i.1.get a) ∩ segPoints (i.1.get b)).Nonempty

/-- Well-formedness of an instance: every segment has distinct endpoints, the segments are
pairwise distinct as point sets (a set of segments), and `0 < K ≤` the number of segments. -/
def WellFormed (i : SegmentIntersectionCliqueInstance) : Prop :=
  (∀ σ ∈ i.1, toPoint σ.1 ≠ toPoint σ.2) ∧ (i.1.map segPoints).Nodup ∧ 0 < i.2 ∧
    i.2 ≤ i.1.length

/-- The intersection graph has a clique of size `K` or more. -/
def SegmentIntersectionCliqueFeasible (i : SegmentIntersectionCliqueInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (Graph i).IsClique (S : Set (Fin i.1.length))

open Classical in
/-- CLIQUE in segment intersection graphs as a decision problem over bitstrings. -/
noncomputable def segmentIntersectionCliqueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SegmentIntersectionCliqueInstance) x with
  | some i => decide (WellFormed i ∧ SegmentIntersectionCliqueFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SegmentIntersectionClique
