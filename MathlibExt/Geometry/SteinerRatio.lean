/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MathlibExt.Geometry.SteinerRatio

open SimpleGraph

/-!
# The Steiner ratio in the Euclidean plane

For a finite set of points in the plane, the Steiner ratio compares the
shortest interconnecting network (auxiliary Steiner points allowed) with
the minimum spanning tree. Lengths are modeled with `SimpleGraph` trees
on finsets of points; `totalLength` sums Euclidean edge lengths.

Source: Optimization Problems, record 43a, "Gilbert-Pollak conjecture
(Steiner ratio)", frozen at teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; `constants/43a.md` SHA-256
`f1e25800b1b0a198331b777e966dbb8d0ff9851b516e46c3b991c1c9d6750432`.

The source states that a shortest network is necessarily a tree, so the
Steiner length is modeled directly as an infimum over trees on finite
supersets; no separate network-to-tree reduction is formalized.
-/

/-- **The Euclidean plane of the Steiner ratio problem.** The space $\mathbb{R}^2$ with the
Euclidean distance, in which the point sets of the Steiner ratio problem lie. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Length of an edge.** For points $x$ and $y$ of the Euclidean plane, the length of the
unordered pair $\{x, y\}$ is the Euclidean distance between $x$ and $y$. -/
noncomputable def edgeLength (e : Sym2 Plane) : ℝ :=
  Sym2.lift (⟨fun x y : Plane => dist x y, fun x y : Plane => dist_comm x y⟩ :
    { f : Plane → Plane → ℝ // ∀ a b, f a b = f b a }) e

@[simp]
theorem edgeLength_mk (x y : Plane) : edgeLength s(x, y) = dist x y :=
  rfl

theorem edgeLength_nonneg (e : Sym2 Plane) : 0 ≤ edgeLength e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    rw [edgeLength_mk]
    exact dist_nonneg

/-- **Total length of a graph on points of the plane.** For a finite set $V$ of points in the
Euclidean plane and a simple graph $G$ with vertex set $V$, the total length of $G$ is the sum,
over all edges $\{x, y\}$ of $G$, of the Euclidean distance between $x$ and $y$. -/
noncomputable def totalLength {V : Finset Plane} (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset, edgeLength (Sym2.map Subtype.val e)

theorem totalLength_nonneg {V : Finset Plane} (G : SimpleGraph V) :
    0 ≤ totalLength G := by
  classical
  exact Finset.sum_nonneg fun e _ => edgeLength_nonneg _

/-- **Lengths of spanning trees.** For a finite set $V$ of points in the Euclidean plane, this is
the set of real numbers $\ell$ such that some tree with vertex set $V$ has total length $\ell$,
the total length being the sum of the Euclidean lengths of its edges. -/
def spanningTreeLengths (V : Finset Plane) : Set ℝ :=
  { l | ∃ G : SimpleGraph V, G.IsTree ∧ totalLength G = l }

/-- **Lengths of Steiner trees.** For a finite set $V$ of points in the Euclidean plane, this is
the set of real numbers $\ell$ such that, for some finite set $W$ of points of the plane
containing $V$, some tree with vertex set $W$ has total length $\ell$. The points of $W$
outside $V$ are the Steiner points. -/
def steinerTreeLengths (V : Finset Plane) : Set ℝ :=
  { l | ∃ W : Finset Plane, V ⊆ W ∧
      ∃ G : SimpleGraph W, G.IsTree ∧ totalLength G = l }

/-- **Minimum spanning tree length.** For a finite set $V$ of points in the Euclidean plane, the
minimum spanning tree length of $V$ is the infimum of the total lengths of the trees with
vertex set $V$. For nonempty $V$ this set of lengths is finite and nonempty, so the infimum
is a minimum; for empty $V$ the value is $0$ by convention. -/
noncomputable def mstLength (V : Finset Plane) : ℝ :=
  sInf (spanningTreeLengths V)

/-- **Steiner minimal tree length.** For a finite set $V$ of points in the Euclidean plane, the
Steiner length of $V$ is the infimum of the total lengths of the trees whose vertex set is a
finite set of points of the plane containing $V$. This set of lengths is nonempty and bounded
below by $0$, so the infimum exists. -/
noncomputable def steinerLength (V : Finset Plane) : ℝ :=
  sInf (steinerTreeLengths V)

theorem spanningTreeLengths_nonempty {V : Finset Plane} (hV : V.Nonempty) :
    (spanningTreeLengths V).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨T, -, hT⟩ := SimpleGraph.Connected.exists_isTree_le
    (G := completeGraph V) SimpleGraph.connected_top
  exact ⟨totalLength T, T, hT, rfl⟩

theorem spanningTreeLengths_subset_steinerTreeLengths (V : Finset Plane) :
    spanningTreeLengths V ⊆ steinerTreeLengths V := by
  rintro l ⟨G, hG, hl⟩
  exact ⟨V, subset_rfl, G, hG, hl⟩

theorem steinerTreeLengths_bddBelow (V : Finset Plane) :
    BddBelow (steinerTreeLengths V) := by
  refine ⟨0, ?_⟩
  rintro l ⟨W, -, G, -, rfl⟩
  exact totalLength_nonneg G

/-- **The Steiner length is at most the minimum spanning tree length.** For every nonempty
finite set $V$ of points in the Euclidean plane, the Steiner minimal tree length of $V$ is at
most the minimum spanning tree length of $V$: allowing Steiner points never increases the
optimal length. -/
theorem steinerLength_le_mstLength {V : Finset Plane} (hV : V.Nonempty) :
    steinerLength V ≤ mstLength V :=
  csInf_le_csInf (steinerTreeLengths_bddBelow V)
    (spanningTreeLengths_nonempty hV)
    (spanningTreeLengths_subset_steinerTreeLengths V)

theorem steinerTreeLengths_nonempty {V : Finset Plane} (hV : V.Nonempty) :
    (steinerTreeLengths V).Nonempty :=
  (spanningTreeLengths_nonempty hV).mono
    (spanningTreeLengths_subset_steinerTreeLengths V)

theorem steinerLength_nonneg {V : Finset Plane} (hV : V.Nonempty) :
    0 ≤ steinerLength V :=
  le_csInf (steinerTreeLengths_nonempty hV) (by
    rintro l ⟨W, -, G, -, rfl⟩
    exact totalLength_nonneg G)

/-- **The Steiner ratio of the Euclidean plane.** The Steiner ratio constant is the infimum,
over all finite sets $V$ of at least two points in the Euclidean plane $\mathbb{R}^2$, of the
ratio of the Steiner minimal tree length of $V$ to the minimum spanning tree length of $V$. -/
noncomputable def steinerRatioConstant : ℝ :=
  sInf { r | ∃ V : Finset Plane, 2 ≤ V.card ∧
    r = steinerLength V / mstLength V }

/-- **Gilbert–Pollak conjecture.** The Steiner ratio of the Euclidean plane, that is, the
infimum of the ratio of the Steiner minimal tree length to the minimum spanning tree length
over all finite sets of at least two points in the plane, equals $\sqrt{3}/2$.

The vertices of an equilateral triangle have ratio exactly $\sqrt{3}/2$, so the conjecture
says that no finite set of at least two points in the plane has a smaller ratio. -/
def GilbertPollakConjecture : Prop :=
  steinerRatioConstant = Real.sqrt 3 / 2

end MathlibExt.Geometry.SteinerRatio
