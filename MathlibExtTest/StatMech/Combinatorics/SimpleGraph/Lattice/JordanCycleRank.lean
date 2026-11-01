/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleRank

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleRank`

`regionGraph (imageGraph P)` is the lattice `ℤ²` with the quarter turn `crossEdge e` of every edge
`e` of `P` removed. For a graph without edges it is the whole lattice, with one component
(`jcr_regionComponents_card_one_of_bot`), which these tests check for the one-point graph at the
origin.

The last section shows why the region graph does not count faces: for the unit square the four
removed edges are the quarter turn of the square about the origin, which does not separate `ℤ²`,
so the region graph is connected while `faceCount = 2`. The faithful count of bounded faces for
all finite subgraphs is `jed_faithfulDiscreteJordan`, tested in `JordanEnclosureDuality`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanCycleRank

open _root_.StatMech _root_.StatMech.Lattice _root_.SimpleGraph

/-- The one-point graph at the origin. -/
def point : PlanarZ2Subgraph where
  V := Fin 1
  finV := inferInstance
  decV := inferInstance
  G := ⊥
  emb := ⟨fun _ => ![0, 0], fun a b _ => Subsingleton.elim a b⟩
  isSub := by intro x y h; exact absurd h (by simp)

theorem faceCount_point : faceCount point.G = 1 := by
  change nullity (⊥ : SimpleGraph (Fin 1)) + 1 = 1
  unfold nullity
  simp

-- For the one-point graph the region graph has `faceCount = 1` component.
example : Nat.card (regionGraph (imageGraph point)).ConnectedComponent = 1 :=
  jcr_regionComponents_card_one_of_bot rfl

example : Nat.card (regionGraph (imageGraph point)).ConnectedComponent = faceCount point.G := by
  rw [jcr_regionComponents_card_one_of_bot rfl, faceCount_point]

/-! ### The region graph of the unit square is connected -/

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
abbrev cyc4 : SimpleGraph (Fin 4) where
  Adj i j := ((j = i + 1) || (i = j + 1)) = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

/-- The corners of the unit square, in cyclic order. -/
def sqEmb : Fin 4 → Site 2 := ![![0, 0], ![1, 0], ![1, 1], ![0, 1]]

/-- The unit square of `ℤ²` as a planar subgraph. -/
def unitSquare : PlanarZ2Subgraph where
  V := Fin 4
  finV := inferInstance
  decV := inferInstance
  G := cyc4
  emb := ⟨sqEmb, by decide +kernel⟩
  isSub := by
    intro i j h
    change ((j = i + 1) || (i = j + 1)) = true at h
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    revert h; fin_cases i <;> fin_cases j <;> simp [sqEmb]

theorem rot90Fun_rot90Inv (z : Site 2) : rot90Fun (rot90Inv z) = z := by
  funext i; fin_cases i <;> simp [rot90Fun, rot90Inv]

theorem crossEdge_symm_mk (x y : Site 2) :
    crossEdge.symm s(x, y) = s(rot90Inv x, rot90Inv y) := by
  rw [Equiv.symm_apply_eq, crossEdge_mk, rot90Fun_rot90Inv, rot90Fun_rot90Inv]

/-- A lattice edge with an endpoint whose inverse rotation is not a corner of the square survives
in the region graph of the unit square. -/
theorem regionGraph_adj_of_outer {f g : Site 2} (hadj : (hypercubicLattice 2).Adj f g)
    (hf : ∀ x, rot90Inv f ≠ sqEmb x) : (regionGraph (imageGraph unitSquare)).Adj f g := by
  refine ⟨hadj, fun hmem => ?_⟩
  rw [crossEdge_symm_mk, mem_edgeSet, imageGraph_adj] at hmem
  obtain ⟨x, _, _, hx, _⟩ := hmem
  exact hf x hx.symm

theorem reach_of_outer {f g : Site 2} (hadj : (hypercubicLattice 2).Adj f g)
    (h : (∀ x, rot90Inv f ≠ sqEmb x) ∨ ∀ x, rot90Inv g ≠ sqEmb x) :
    (regionGraph (imageGraph unitSquare)).Reachable f g := by
  rcases h with h | h
  · exact (regionGraph_adj_of_outer hadj h).reachable
  · exact (regionGraph_adj_of_outer hadj.symm h).reachable.symm

/-- The path `a - b - c - d` survives when `b` and `c` are outer sites. -/
theorem reach_detour (a b c d : Site 2) (h1 : (hypercubicLattice 2).Adj a b)
    (h2 : (hypercubicLattice 2).Adj b c) (h3 : (hypercubicLattice 2).Adj c d)
    (hb : ∀ x, rot90Inv b ≠ sqEmb x) (hc : ∀ x, rot90Inv c ≠ sqEmb x) :
    (regionGraph (imageGraph unitSquare)).Reachable a d :=
  ((reach_of_outer h1 (.inr hb)).trans (reach_of_outer h2 (.inl hb))).trans
    (reach_of_outer h3 (.inl hc))

theorem ladj {a b : Site 2} (h : (∑ i, (a i - b i).natAbs) = 1) :
    (hypercubicLattice 2).Adj a b := h

-- The four removed dual edges are the sides of the square with corners `(0,0)`, `(0,1)`,
-- `(-1,1)`, `(-1,0)` (the quarter turn of the unit square); each has a detour around it.
theorem reach01 : (regionGraph (imageGraph unitSquare)).Reachable
    (rot90Fun (sqEmb 0)) (rot90Fun (sqEmb 1)) := by
  simp only [sqEmb]
  refine reach_detour _ ![1, 0] ![1, 1] _ (ladj ?_) (ladj ?_) (ladj ?_) ?_ ?_ <;>
    first | (simp [Fin.sum_univ_two]; done) | (intro x; fin_cases x <;> simp [sqEmb, funext_iff])

theorem reach12 : (regionGraph (imageGraph unitSquare)).Reachable
    (rot90Fun (sqEmb 1)) (rot90Fun (sqEmb 2)) := by
  simp only [sqEmb]
  refine reach_detour _ ![0, 2] ![-1, 2] _ (ladj ?_) (ladj ?_) (ladj ?_) ?_ ?_ <;>
    first | (simp [Fin.sum_univ_two]; done) | (intro x; fin_cases x <;> simp [sqEmb, funext_iff])

theorem reach23 : (regionGraph (imageGraph unitSquare)).Reachable
    (rot90Fun (sqEmb 2)) (rot90Fun (sqEmb 3)) := by
  simp only [sqEmb]
  refine reach_detour _ ![-2, 1] ![-2, 0] _ (ladj ?_) (ladj ?_) (ladj ?_) ?_ ?_ <;>
    first | (simp [Fin.sum_univ_two]; done) | (intro x; fin_cases x <;> simp [sqEmb, funext_iff])

theorem reach30 : (regionGraph (imageGraph unitSquare)).Reachable
    (rot90Fun (sqEmb 3)) (rot90Fun (sqEmb 0)) := by
  simp only [sqEmb]
  refine reach_detour _ ![-1, -1] ![0, -1] _ (ladj ?_) (ladj ?_) (ladj ?_) ?_ ?_ <;>
    first | (simp [Fin.sum_univ_two]; done) | (intro x; fin_cases x <;> simp [sqEmb, funext_iff])

theorem rgReach_adj {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    (regionGraph (imageGraph unitSquare)).Reachable f g := by
  by_cases hf : ∀ x, rot90Inv f ≠ sqEmb x
  · exact reach_of_outer h (.inl hf)
  by_cases hg : ∀ x, rot90Inv g ≠ sqEmb x
  · exact reach_of_outer h (.inr hg)
  push Not at hf hg
  obtain ⟨x, hx⟩ := hf
  obtain ⟨y, hy⟩ := hg
  have hfx : f = rot90Fun (sqEmb x) := by rw [← hx, rot90Fun_rot90Inv]
  have hgy : g = rot90Fun (sqEmb y) := by rw [← hy, rot90Fun_rot90Inv]
  subst hfx hgy
  fin_cases x <;> fin_cases y
  all_goals first
    | (exfalso; simp [sqEmb, Fin.sum_univ_two] at h; done)
    | first
      | exact reach01 | exact reach01.symm | exact reach12 | exact reach12.symm
      | exact reach23 | exact reach23.symm | exact reach30 | exact reach30.symm

/-- The region graph of the unit square is connected: the four dual edges it removes form a
unit square of their own, which does not separate `ℤ²`. -/
theorem regionGraph_unitSquare_reachable (f g : Site 2) :
    (regionGraph (imageGraph unitSquare)).Reachable f g := by
  obtain ⟨w⟩ := hypercubicLattice_two_reachable f g
  induction w with
  | nil => rfl
  | cons h _ ih => exact (rgReach_adj h).trans ih

theorem faceCount_unitSquare : faceCount unitSquare.G = 2 := by
  change nullity cyc4 + 1 = 2
  have hc : cyc4.Connected := by
    have a : ∀ i : Fin 4, cyc4.Adj i (i + 1) := by decide
    refine (connected_iff_exists_forall_reachable _).mpr ⟨0, fun i => ?_⟩
    fin_cases i
    exacts [Reachable.refl _, (a 0).reachable, (a 0).reachable.trans (a 1).reachable,
      (a 3).symm.reachable]
  have := hc.preconnected.subsingleton_connectedComponent
  have hcc : Nat.card cyc4.ConnectedComponent = 1 :=
    Nat.card_of_subsingleton (cyc4.connectedComponentMk 0)
  have he : cyc4.edgeSet.ncard = 4 := by rw [Set.ncard_eq_toFinset_card']; decide
  unfold nullity
  rw [he, hcc]
  simp

-- The region graph of the unit square has one component, while `faceCount = 2`.
example : Nat.card (regionGraph (imageGraph unitSquare)).ConnectedComponent = 1 ∧
    faceCount unitSquare.G = 2 := by
  refine ⟨?_, faceCount_unitSquare⟩
  have hsub : Subsingleton (regionGraph (imageGraph unitSquare)).ConnectedComponent :=
    ⟨ConnectedComponent.ind₂ fun a b => ConnectedComponent.sound
      (regionGraph_unitSquare_reachable a b)⟩
  exact Nat.card_eq_one_iff_unique.mpr
    ⟨hsub, ⟨(regionGraph (imageGraph unitSquare)).connectedComponentMk ![0, 0]⟩⟩

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanCycleRank
