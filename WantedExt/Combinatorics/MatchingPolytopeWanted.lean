/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.Sym
public import Mathlib.Basic.Real.Basic

/-!
# Edmonds' matching polytope theorems (wanted)

For a finite graph `G = (V, E)`, the perfect matching polytope is the convex hull in `ℝ^E` of the
incidence vectors of the perfect matchings, and the matching polytope that of all matchings.
Edmonds (1965) described both by linear inequalities: nonnegativity, degree constraints, and one
odd-set constraint for every odd vertex set. Matchings are Mathlib's `Subgraph.IsMatching`,
perfect matchings `Subgraph.IsPerfectMatching`.

Source: A. Schrijver, *A Course in Combinatorial Optimization* (CWI lecture notes), §5.4,
Corollary 5.6a (constraints (27) and (28)) and Corollary 5.6b (constraints (30));
J. Edmonds, "Maximum matching and a polyhedron with 0,1-vertices", J. Res. Nat. Bur. Standards
69B (1965), 125-130.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MatchingPolytopeWanted

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

open Classical in
/-- **Incidence vector of a subgraph's edges.** The vector in `ℝ^E` (indexed by the edges of `G`)
that is `1` on the edges of `M` and `0` elsewhere (Schrijver, *A Course in Combinatorial
Optimization*, §5.4, footnote 18). -/
noncomputable def edgeIncidence (M : G.Subgraph) : G.edgeSet → ℝ :=
  fun e => if (e : Sym2 V) ∈ M.edgeSet then 1 else 0

/-- **Matching polytope.** The convex hull in `ℝ^E` of the incidence vectors of the matchings of
`G` (Schrijver, *A Course in Combinatorial Optimization*, §5.4, eq. (29)). -/
def matchingPolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsMatching ∧ x = edgeIncidence G M}

/-- **Perfect matching polytope.** The convex hull in `ℝ^E` of the incidence vectors of the perfect
matchings of `G` (Schrijver, *A Course in Combinatorial Optimization*, §5.4, eq. (26)). -/
def perfectMatchingPolytope : Set (G.edgeSet → ℝ) :=
  convexHull ℝ {x | ∃ M : G.Subgraph, M.IsPerfectMatching ∧ x = edgeIncidence G M}

/-- **Edmonds' perfect matching polytope theorem.** The perfect matching polytope of a finite graph
is the set of `x ∈ ℝ^E` with `x ≥ 0`, `x(δ(v)) = 1` for every vertex `v`, and `x(δ(U)) ≥ 1` for
every vertex set `U` of odd size, where `δ(U)` is the set of edges with exactly one end in `U`
(Schrijver, *A Course in Combinatorial Optimization*, §5.4, Corollary 5.6a). -/
theorem_wanted perfectMatchingPolytope_eq :
    perfectMatchingPolytope G =
      {x | (∀ e, 0 ≤ x e) ∧
        (∀ v : V, ∑ e ∈ univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)), x e = 1) ∧
        ∀ U : Finset V, Odd U.card →
          1 ≤ ∑ e ∈ univ.filter (fun e : G.edgeSet =>
            (e : Sym2 V) ∉ U.sym2 ∧ (e : Sym2 V) ∉ (univ \ U).sym2), x e}

/-- **Edmonds' matching polytope theorem.** The matching polytope of a finite graph is the set of
`x ∈ ℝ^E` with `x ≥ 0`, `x(δ(v)) ≤ 1` for every vertex `v`, and `x(E[U]) ≤ ⌊|U| / 2⌋` for every
vertex set `U` of odd size, where `E[U]` is the set of edges with both ends in `U` (Schrijver,
*A Course in Combinatorial Optimization*, §5.4, Corollary 5.6b, constraints (30)). -/
theorem_wanted matchingPolytope_eq :
    matchingPolytope G =
      {x | (∀ e, 0 ≤ x e) ∧
        (∀ v : V, ∑ e ∈ univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V)), x e ≤ 1) ∧
        ∀ U : Finset V, Odd U.card →
          ∑ e ∈ univ.filter (fun e : G.edgeSet => (e : Sym2 V) ∈ U.sym2), x e ≤
            ((U.card / 2 : ℕ) : ℝ)}

end MathlibExt.Combinatorics.MatchingPolytopeWanted
