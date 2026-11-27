/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Star

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

namespace MathlibExt.Geometry.SteinerRatioWanted

open MathlibExt.Geometry.SteinerRatio
open SimpleGraph (mem_edgeFinset starGraph isTree_starGraph starGraph_adj)

private noncomputable def planePoint (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

private theorem dist_planePoint (x y u v : ℝ) :
    dist (planePoint x y) (planePoint u v) = Real.sqrt ((x - u) ^ 2 + (y - v) ^ 2) := by
  simp [EuclideanSpace.dist_eq, Fin.sum_univ_two, planePoint, Real.dist_eq, sq_abs]

private noncomputable def triangleA : Plane := planePoint 1 0
private noncomputable def triangleB : Plane := planePoint (-(1 / 2)) (Real.sqrt 3 / 2)
private noncomputable def triangleC : Plane := planePoint (-(1 / 2)) (-(Real.sqrt 3 / 2))
private noncomputable def triangleCenter : Plane := planePoint 0 0

private theorem dist_triangleAB : dist triangleA triangleB = Real.sqrt 3 := by
  rw [triangleA, triangleB, dist_planePoint]
  congr 1
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem dist_triangleAC : dist triangleA triangleC = Real.sqrt 3 := by
  rw [triangleA, triangleC, dist_planePoint]
  congr 1
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem dist_triangleBC : dist triangleB triangleC = Real.sqrt 3 := by
  rw [triangleB, triangleC, dist_planePoint]
  congr 1
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private noncomputable def triangleVertices : Finset Plane := by
  classical
  exact {triangleA, triangleB, triangleC}

private theorem card_triangleVertices : triangleVertices.card = 3 := by
  classical
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have ne_of_chord {x y : Plane} (h : dist x y = Real.sqrt 3) : x ≠ y := by
    intro heq
    subst y
    exact hs (by simpa using h.symm)
  have hab := ne_of_chord dist_triangleAB
  have hac := ne_of_chord dist_triangleAC
  have hbc := ne_of_chord dist_triangleBC
  rw [triangleVertices, Finset.card_insert_of_notMem, Finset.card_pair hbc]
  simp [hab, hac]

private theorem dist_of_mem_triangleVertices {x y : Plane} (hx : x ∈ triangleVertices)
    (hy : y ∈ triangleVertices) (hne : x ≠ y) : dist x y = Real.sqrt 3 := by
  classical
  simp only [triangleVertices, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    first
    | exact (hne rfl).elim
    | exact dist_triangleAB
    | exact dist_triangleAC
    | exact dist_triangleBC
    | rw [dist_comm]; first | exact dist_triangleAB | exact dist_triangleAC | exact dist_triangleBC

private theorem dist_center_of_mem_triangleVertices {x : Plane} (hx : x ∈ triangleVertices) :
    dist triangleCenter x = 1 := by
  classical
  simp only [triangleVertices, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> rw [triangleCenter, ← Real.sqrt_one]
  · norm_num [triangleA, dist_planePoint]
  · rw [triangleB, dist_planePoint]
    congr 1
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · rw [triangleC, dist_planePoint]
    congr 1
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem totalLength_eq_card_sub_one_mul {V : Finset Plane} {G : SimpleGraph V}
    (hG : G.IsTree) (l : ℝ) (h : ∀ ⦃x y : V⦄, G.Adj x y → dist (x : Plane) (y : Plane) = l) :
    totalLength G = ((V.card - 1 : ℕ) : ℝ) * l := by
  classical
  have hcard := hG.card_edgeFinset
  rw [Fintype.card_coe] at hcard
  have hedge : G.edgeFinset.card = V.card - 1 := by omega
  unfold totalLength
  calc
    _ = ∑ _e ∈ G.edgeFinset, l := by
      apply Finset.sum_congr rfl
      intro e
      induction e using Sym2.inductionOn with
      | _ x y =>
        intro he
        exact h (mem_edgeFinset.mp he)
    _ = _ := by simp [hedge]

private theorem mstLength_triangleVertices : mstLength triangleVertices = 2 * Real.sqrt 3 := by
  have hV : triangleVertices.Nonempty := Finset.card_pos.mp (by simp [card_triangleVertices])
  have hlength (l : ℝ) (hl : l ∈ spanningTreeLengths triangleVertices) : l = 2 * Real.sqrt 3 := by
    obtain ⟨G, hG, rfl⟩ := hl
    rw [totalLength_eq_card_sub_one_mul hG (Real.sqrt 3), card_triangleVertices]
    · norm_num
    · intro x y hxy
      exact dist_of_mem_triangleVertices x.property y.property
        (fun h => hxy.ne (Subtype.ext h))
  have hbounded : BddBelow (spanningTreeLengths triangleVertices) :=
    (steinerTreeLengths_bddBelow _).mono (spanningTreeLengths_subset_steinerTreeLengths _)
  obtain ⟨l, hl⟩ := spanningTreeLengths_nonempty hV
  exact le_antisymm (csInf_le hbounded (hlength l hl ▸ hl))
    (le_csInf ⟨l, hl⟩ fun a ha => (hlength a ha).ge)

private theorem steinerLength_triangleVertices_le : steinerLength triangleVertices ≤ 3 := by
  classical
  have hcenter : triangleCenter ∉ triangleVertices := by
    intro h
    have hd := dist_center_of_mem_triangleVertices h
    simp at hd
  let W := insert triangleCenter triangleVertices
  let c : W := ⟨triangleCenter, Finset.mem_insert_self _ _⟩
  have hcard : W.card = 4 := by
    simp [W, Finset.card_insert_of_notMem hcenter, card_triangleVertices]
  have hunit (x : W) (hx : x ≠ c) : dist (c : Plane) (x : Plane) = 1 := by
    apply dist_center_of_mem_triangleVertices
    exact (Finset.mem_insert.mp x.property).resolve_left (fun h => hx (Subtype.ext h))
  refine csInf_le (steinerTreeLengths_bddBelow _) ⟨W, Finset.subset_insert _ _, starGraph c,
    isTree_starGraph c, ?_⟩
  rw [totalLength_eq_card_sub_one_mul (isTree_starGraph c) 1, hcard]
  · norm_num
  · intro x y hxy
    obtain ⟨hne, rfl | rfl⟩ := starGraph_adj.mp hxy
    · exact hunit y hne.symm
    · rw [dist_comm]
      exact hunit x hne

/-- **Gilbert–Pollak upper bound for the Steiner ratio.** The Steiner ratio constant, the infimum
over finite sets $V$ of at least two points in the Euclidean plane of the length of a Steiner
minimal tree for $V$ divided by the length of a minimum spanning tree of $V$, is at most
$\sqrt{3}/2$.

Source: Gilbert and Pollak, *Steiner minimal trees* (1968): the
equilateral triangle gives the upper bound `√3 / 2`. Known literature
result; the triangle computation is not supplied here. -/
theorem gilbertPollakUpperBound_wanted : steinerRatioConstant ≤ Real.sqrt 3 / 2 := by
  have hbounded : BddBelow {r : ℝ | ∃ V : Finset Plane, 2 ≤ V.card ∧
      r = steinerLength V / mstLength V} := by
    refine ⟨0, ?_⟩
    rintro r ⟨V, hV, rfl⟩
    have hne : V.Nonempty := Finset.card_pos.mp (by omega)
    exact div_nonneg (steinerLength_nonneg hne)
      ((steinerLength_nonneg hne).trans (steinerLength_le_mstLength hne))
  calc
    steinerRatioConstant ≤ steinerLength triangleVertices / mstLength triangleVertices :=
      csInf_le hbounded ⟨triangleVertices, by simp [card_triangleVertices], rfl⟩
    _ ≤ 3 / (2 * Real.sqrt 3) := by
      rw [mstLength_triangleVertices]
      exact div_le_div_of_nonneg_right steinerLength_triangleVertices_le (by positivity)
    _ = Real.sqrt 3 / 2 := by
      apply (div_eq_iff (by positivity : (2 * Real.sqrt (3 : ℝ)) ≠ 0)).mpr
      calc
        (3 : ℝ) = (Real.sqrt 3) ^ 2 := (Real.sq_sqrt (by norm_num)).symm
        _ = Real.sqrt 3 / 2 * (2 * Real.sqrt 3) := by ring

end MathlibExt.Geometry.SteinerRatioWanted
