/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STAR 3-COLORABILITY OF PLANAR BIPARTITE GRAPHS is NP-complete

Source:
M. O. Albertson, G. G. Chappell, H. A. Kierstead, A. Kündgen and R. Ramamurthi, "Coloring with
no 2-colored `P₄`'s", Electronic Journal of Combinatorics 11(1) (2004), #R26,
doi:10.37236/1779 (Definition 2.1; Theorem 7.2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StarThreeColorabilityPlanarBipartite

/-!
# STAR 3-COLORABILITY OF PLANAR BIPARTITE GRAPHS is NP-complete

INSTANCE: a planar bipartite graph `G = (V, E)` (finite, simple, undirected).
QUESTION: does `G` have a star coloring with at most 3 colors, that is, a proper coloring with
3 colors in which no path on 4 vertices is 2-colored?

Albertson, Chappell, Kierstead, Kündgen and Ramamurthi, Definition 2.1: "An `r`-coloring of `G`
is called a star coloring if there are no 2-colored paths on 4 vertices" (their colorings are
proper, Section 1, and a 2-colored path is a subgraph, not necessarily induced, Section 2).
Theorem 7.2: "The problem of deciding if a planar bipartite graph has a star coloring with at
most 3 colors is NP-complete", by a reduction from PLANAR 3-COLORABILITY that replaces every
edge `uv` by a copy of `K_{2,3}` with `u`, `v` as its part of size 2.

A coloring with at most 3 colors is a proper coloring `C : G.Coloring (Fin 3)` (Mathlib's
`SimpleGraph.Coloring`). A path on 4 vertices is four distinct vertices `w, x, y, z` with `w ~ x`,
`x ~ y`, `y ~ z` (adjacency gives `w ≠ x`, `x ≠ y`, `y ≠ z`; the other three inequalities are
hypotheses). Consecutive vertices of the path get different colors, so the path uses only two
colors exactly when `C w = C y` and `C x = C z`; `IsStarColoring` forbids that. Bipartiteness
is Mathlib's `SimpleGraph.IsBipartite` (`Colorable 2`), and planarity is MathlibExt's
`SimpleGraph.IsPlanar`: a crossing-free straight-line drawing in the real plane, which by
Fáry's theorem exists exactly for the planar graphs.

The graph is given by an edge list on `Fin n`. Isolated vertices do not change the answer, so
the binary vertex count does not make the problem succinct.

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

/-- **STAR 3-COLORABILITY OF PLANAR BIPARTITE GRAPHS is NP-complete.** Source: Albertson,
Chappell, Kierstead, Kündgen and Ramamurthi (2004), Theorem 7.2. -/
public theorem_wanted starThreeColorabilityPlanarBipartite_npComplete :
    starThreeColorabilityPlanarBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L starThreeColorabilityPlanarBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.StarThreeColorabilityPlanarBipartite
