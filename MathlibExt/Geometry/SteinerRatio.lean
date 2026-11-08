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

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Euclidean length of an unordered pair of points. -/
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

/-- Total Euclidean length of a finite graph on a finset of points. -/
noncomputable def totalLength {V : Finset Plane} (G : SimpleGraph V) : ℝ := by
  classical
  exact ∑ e ∈ G.edgeFinset, edgeLength (Sym2.map Subtype.val e)

theorem totalLength_nonneg {V : Finset Plane} (G : SimpleGraph V) :
    0 ≤ totalLength G := by
  classical
  exact Finset.sum_nonneg fun e _ => edgeLength_nonneg _

/-- Lengths of spanning trees of `V`. -/
def spanningTreeLengths (V : Finset Plane) : Set ℝ :=
  { l | ∃ G : SimpleGraph V, G.IsTree ∧ totalLength G = l }

/-- Lengths of Steiner trees for `V`: trees on finite supersets of `V`
(the extra vertices are Steiner points). -/
def steinerTreeLengths (V : Finset Plane) : Set ℝ :=
  { l | ∃ W : Finset Plane, V ⊆ W ∧
      ∃ G : SimpleGraph W, G.IsTree ∧ totalLength G = l }

/-- Minimum spanning tree length, totalized by `sInf` (the length set is
finite and, for nonempty `V`, nonempty). -/
noncomputable def mstLength (V : Finset Plane) : ℝ :=
  sInf (spanningTreeLengths V)

/-- Steiner minimal tree length, totalized by `sInf`. The Steiner length
set is bounded below by `0`. -/
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

/-- Allowing Steiner points never increases the optimal length. -/
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

/-- The Steiner ratio constant: infimum of Steiner-to-MST length ratios
over finite planar point sets with at least two points. -/
noncomputable def steinerRatioConstant : ℝ :=
  sInf { r | ∃ V : Finset Plane, 2 ≤ V.card ∧
    r = steinerLength V / mstLength V }

/-- The Gilbert--Pollak conjecture: the Steiner ratio equals `√3 / 2`,
attained as a bound by the equilateral triangle. Stated as a
proposition only. -/
def GilbertPollakConjecture : Prop :=
  steinerRatioConstant = Real.sqrt 3 / 2

end MathlibExt.Geometry.SteinerRatio
