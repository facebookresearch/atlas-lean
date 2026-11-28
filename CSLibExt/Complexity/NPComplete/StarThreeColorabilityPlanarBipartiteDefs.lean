/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STAR 3-COLORABILITY OF PLANAR BIPARTITE GRAPHS: definitions

Source:
M. O. Albertson, G. G. Chappell, H. A. Kierstead, A. Kündgen and R. Ramamurthi, "Coloring with
no 2-colored `P₄`'s", Electronic Journal of Combinatorics 11(1) (2004), #R26,
doi:10.37236/1779 (Definition 2.1; Theorem 7.2).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StarThreeColorabilityPlanarBipartite

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev StarThreeColorabilityPlanarBipartiteInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : StarThreeColorabilityPlanarBipartiteInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- A proper coloring `C` is a star coloring: no path `w ~ x ~ y ~ z` on four distinct vertices
is 2-colored, i.e. has `C w = C y` and `C x = C z`. -/
def IsStarColoring {V α : Type*} {G : SimpleGraph V} (C : G.Coloring α) : Prop :=
  ∀ ⦃w x y z : V⦄, G.Adj w x → G.Adj x y → G.Adj y z → w ≠ y → w ≠ z → x ≠ z →
    ¬ (C w = C y ∧ C x = C z)

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges in
either orientation, no self-loops, endpoints in range), and the graph is bipartite and
planar. -/
def WellFormed (i : StarThreeColorabilityPlanarBipartiteInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsBipartite ∧ (Graph i).IsPlanar

/-- The graph has a star coloring with at most 3 colors. -/
def StarThreeColorabilityPlanarBipartiteFeasible
    (i : StarThreeColorabilityPlanarBipartiteInstance) : Prop :=
  ∃ C : (Graph i).Coloring (Fin 3), IsStarColoring C

open Classical in
/-- STAR 3-COLORABILITY OF PLANAR BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def starThreeColorabilityPlanarBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StarThreeColorabilityPlanarBipartiteInstance) x with
  | some i => decide (WellFormed i ∧ StarThreeColorabilityPlanarBipartiteFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StarThreeColorabilityPlanarBipartite
