/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosureDuality
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanFaithfulCount
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.ShiftSquareCycle
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.CrossEdgeMatchingForms
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.DualWalkToPrimalWalk

/-!
# Face-region form of the inside of a closed lattice walk

The inside of a closed walk of `ℤ²` as a set of faces (unit squares), and the theorem that the
edges of a walk without repeated edges are exactly the primal edges separating inside from
outside faces.

## i. Overview

A face `f` (the unit square with lower-left corner `f`) is inside the closed walk `Vc` when the
ray count of its upper-right corner `f + (1, 1)` is odd (`fwr_faceInside`). For adjacent faces
`c, d` the shared primal edge `sharedPrimalEdge c d` is exactly the crossing edge `rpc_crossEdge`
of the corresponding pair of corners. So the parity flip `rpc_crossFlip` becomes: `c` and `d` lie
on different sides iff `Vc` traverses their shared edge an odd number of times (`fwr_faceCutFlip`).
For walks without repeated edges, the edges of `Vc` are exactly the primal edges between inside
and outside faces (`fwr_primalWalkBoundsFaceRegion`).

With the site-based inside region instead, the matching fails even for a unit square
(`fwr_primalWalkBoundsRegion_false`, using the loop `ceo_shiftSquare`).

Headline fidelity:
- `fwr_faceCutFlip` is unconditional.
- `fwr_primalWalkBoundsFaceRegion` is unconditional (for every walk without repeated edges).
- `fwr_primalWalkBoundsRegion_false` is an unconditional refutation of `PrimalWalkBoundsRegion`.

## ii. Key results

- `StatMech.Walls.fwr_faceInside` : faces inside a closed walk
- `StatMech.Walls.fwr_faceCutFlip` : adjacent faces separate iff their shared edge is traversed
  an odd number of times
- `StatMech.Walls.fwr_primalWalkBoundsFaceRegion` : edges of a walk without repeated edges are the
  face-region boundary
- `StatMech.Walls.fwr_primalWalkBoundsRegion_false` : the site-region form is false

## iii. Table of contents

- A. Shared edges and crossing edges
- B. The face-region parity flip
- C. Walks without repeated edges
- D. The unit-square counterexample to the site-region form

## iv. References

- H. A. Kramers, G. H. Wannier, "Statistics of the two-dimensional ferromagnet. Part I",
  Phys. Rev. 60 (1941) 252–262
-/

@[expose] public section

open Set SimpleGraph
open scoped BigOperators

namespace StatMech
namespace Walls
open StatMech.Lattice

/-! ## A. Shared edges and crossing edges -/

/-- The edge shared by horizontally adjacent faces is the crossing edge of their upper-right
corners. -/
lemma fwr_sharedEdge_eq_crossEdge_horiz (x y : ℤ) :
    sharedPrimalEdge (![x, y] : Site 2) (![x + 1, y] : Site 2)
      = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
  rw [sharedPrimalEdge_right]
  unfold faceCorner10 faceCorner11 rpc_crossEdge
  rw [ite_eq_left (by simp only [Matrix.cons_val_zero]; omega)]
  unfold rpc_hCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr 2
  funext i; fin_cases i
  simp only [Matrix.cons_val_fin_one]; omega

/-- The edge shared by vertically adjacent faces is the crossing edge of their upper-right corners.
-/
lemma fwr_sharedEdge_eq_crossEdge_vert (x y : ℤ) :
    sharedPrimalEdge (![x, y] : Site 2) (![x, y + 1] : Site 2)
      = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 1, y + 2] : Site 2) := by
  rw [sharedPrimalEdge_top]
  unfold faceCorner01 faceCorner11 rpc_crossEdge
  rw [ite_eq_right (by simp only [Matrix.cons_val_zero]; omega),
      ite_eq_right (by simp only [Matrix.cons_val_zero]; omega),
      ite_eq_left (by simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
  unfold rpc_vCrossEdge
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [show (x + 1 - 1 : ℤ) = x by ring]

/-! ## B. The face-region parity flip -/

/-- The face with lower-left corner `f` is inside `Vc`: the ray count of `f + (1, 1)` is odd. -/
def fwr_faceInside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : Site 2 → Prop :=
  fun f => ¬ Even (jec_rayCount (![f 0 + 1, f 1 + 1] : Site 2) Vc)

/-- `fwr_faceInside` at the face `(x, y)`. -/
lemma fwr_faceInside_mk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (x y : ℤ) :
    fwr_faceInside Vc (![x, y] : Site 2)
      ↔ ¬ Even (jec_rayCount (![x + 1, y + 1] : Site 2) Vc) := by
  unfold fwr_faceInside
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- `(¬P ↔ ¬¬Q) ↔ (P ↔ ¬Q)`. -/
lemma fwr_paritySwap (P Q : Prop) :
    ((¬ P) ↔ ¬ ¬ Q) ↔ ((¬ Q) ↔ ¬ ¬ P) := by
  constructor <;> intro h <;>
    · by_cases hp : P <;> by_cases hq : Q <;> simp_all

/-- Ray-count parity flip across a lattice edge, written with double negation. -/
lemma fwr_faceCutFlip_aux_h {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c' d' : Site 2} (hcd : (hypercubicLattice 2).Adj c' d') :
    ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc))
      ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) := by
  have h := rpc_crossFlip Vc hcd
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion] at h
  exact h

/-- Adjacent faces lie on different sides of `Vc` iff `Vc` traverses their shared primal edge an odd
number of times. -/
theorem fwr_faceCutFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d)
      ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)) := by
  classical
  set x := c 0 with hx
  set y := c 1 with hy
  have hc : c = ![x, y] := by funext i; fin_cases i <;> rfl
  have hcd' := hcd
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcd'
  by_cases h0 : d 0 = c 0 + 1
  · have hd0 : d 0 = x + 1 := by rw [hx]; omega
    have hd1 : d 1 = y := by rw [hy]; omega
    have hd : d = ![x + 1, y] := by
      funext i; fin_cases i
      · simpa using hd0
      · simpa using hd1
    have hc1 : (hypercubicLattice 2).Adj (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
      simp [hypercubicLattice_adj, Fin.sum_univ_two]
    rw [hc, hd, fwr_faceInside_mk, fwr_faceInside_mk, fwr_sharedEdge_eq_crossEdge_horiz]
    rw [show (x + 1 + 1 : ℤ) = x + 2 by ring]
    rw [← fwr_faceCutFlip_aux_h Vc hc1]
  · by_cases h0' : c 0 = d 0 + 1
    · have hd0 : d 0 = x - 1 := by rw [hx]; omega
      have hd1 : d 1 = y := by rw [hy]; omega
      have hd : d = ![x - 1, y] := by
        funext i; fin_cases i
        · simpa using hd0
        · simpa using hd1
      have hc1 : (hypercubicLattice 2).Adj (![(x - 1) + 1, y + 1] : Site 2)
          (![(x - 1) + 2, y + 1] : Site 2) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
      have hshare : sharedPrimalEdge c d = sharedPrimalEdge (![x - 1, y] : Site 2)
          (![(x - 1) + 1, y] : Site 2) := by
        rw [hc, hd, sharedPrimalEdge_comm_of_adj (by
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
        congr 2; omega
      rw [hshare, fwr_sharedEdge_eq_crossEdge_horiz, hc, hd,
        fwr_faceInside_mk, fwr_faceInside_mk]
      have := fwr_faceCutFlip_aux_h Vc hc1
      rw [show ((x - 1) + 1 : ℤ) = x by ring, show ((x - 1) + 2 : ℤ) = x + 1 by ring] at this ⊢
      rw [← this]
      exact fwr_paritySwap _ _
    · have hveq0 : d 0 = c 0 := by omega
      by_cases h1 : d 1 = c 1 + 1
      · have hd0 : d 0 = x := by rw [hx]; exact hveq0
        have hd1 : d 1 = y + 1 := by rw [hy]; omega
        have hd : d = ![x, y + 1] := by
          funext i; fin_cases i
          · simpa using hd0
          · simpa using hd1
        have hc1 : (hypercubicLattice 2).Adj (![x + 1, y + 1] : Site 2)
            (![x + 1, y + 2] : Site 2) := by
          simp [hypercubicLattice_adj, Fin.sum_univ_two]
        rw [hc, hd, fwr_faceInside_mk, fwr_faceInside_mk, fwr_sharedEdge_eq_crossEdge_vert]
        rw [show (y + 1 + 1 : ℤ) = y + 2 by ring]
        rw [← fwr_faceCutFlip_aux_h Vc hc1]
      · have hd0 : d 0 = x := by rw [hx]; exact hveq0
        have hd1 : d 1 = y - 1 := by rw [hy]; omega
        have hd : d = ![x, y - 1] := by
          funext i; fin_cases i
          · simpa using hd0
          · simpa using hd1
        have hc1 : (hypercubicLattice 2).Adj (![x + 1, (y - 1) + 1] : Site 2)
            (![x + 1, (y - 1) + 2] : Site 2) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        have hshare : sharedPrimalEdge c d = sharedPrimalEdge (![x, y - 1] : Site 2)
            (![x, (y - 1) + 1] : Site 2) := by
          rw [hc, hd, sharedPrimalEdge_comm_of_adj (by
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
          congr 2
          funext i; fin_cases i
          simp only [Matrix.cons_val_fin_one]; omega
        rw [hshare, fwr_sharedEdge_eq_crossEdge_vert, hc, hd,
          fwr_faceInside_mk, fwr_faceInside_mk]
        have := fwr_faceCutFlip_aux_h Vc hc1
        rw [show ((y - 1) + 1 : ℤ) = y by ring, show ((y - 1) + 2 : ℤ) = y + 1 by ring] at this ⊢
        rw [← this]
        exact fwr_paritySwap _ _

/-! ## C. Walks without repeated edges -/

/-- For a walk without repeated edges, adjacent faces lie on different sides iff their shared edge
is an edge of the walk. -/
lemma fwr_faceCutMatch_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
  rw [fwr_faceCutFlip Vc hcd]
  exact dow_odd_count_iff_mem_of_nodup hnd _

/-- For a walk without repeated edges, the dual edge between adjacent faces lies in the cut of the
inside faces iff the shared primal edge is an edge of the walk. -/
lemma fwr_jedCutSet_match_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    sharedPrimalEdge c d ∈ jed_cutSet (fwr_faceInside Vc) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
  rw [jed_mem_cutSet_iff (fwr_faceInside Vc) hcd]
  exact fwr_faceCutMatch_of_nodup Vc hnd hcd

/-- For a walk without repeated edges, a lattice edge is an edge of the walk iff it lies in the cut
set of the inside faces. -/
lemma fwr_primalWalkBoundsFaceRegion_of_nodup {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hnd : Vc.edges.Nodup)
    {u v : Site 2} (huv : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc) := by
  obtain ⟨f0, g0, hfg, hshared⟩ := jfc_flankingFaces huv
  rw [← hshared]
  exact (fwr_jedCutSet_match_of_nodup Vc hnd hfg).symm

/-- For every closed lattice walk without repeated edges, its edges are exactly the edges of the cut
set of its inside faces. -/
def fwr_PrimalWalkBoundsFaceRegion : Prop :=
  ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup →
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc))

/-- Every closed lattice walk without repeated edges bounds its face region. -/
theorem fwr_primalWalkBoundsFaceRegion : fwr_PrimalWalkBoundsFaceRegion := by
  intro a Vc hnd u v huv
  exact fwr_primalWalkBoundsFaceRegion_of_nodup Vc hnd huv

/-! ## D. The unit-square counterexample to the site-region form -/

/-- The faces `(0, 0)` and `(0, 1)` are adjacent. -/
lemma fwr_shiftSquare_faces_adj :
    (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

/-- The faces `(0, 0)` and `(0, 1)` share the edge `(0, 1)`–`(1, 1)`. -/
lemma fwr_shiftSquare_shared :
    sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2)
      = s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  rw [show (![0, 1] : Site 2) = ![(0 : ℤ), 0 + 1] by norm_num, sharedPrimalEdge_top]
  unfold faceCorner01 faceCorner11; norm_num

/-- For `ceo_shiftSquare`, the face-region matching holds at the faces `(0, 0)`, `(0, 1)`. -/
lemma fwr_shiftSquare_faceCut_works :
    (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2)
      ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2)) := by
  have hd : (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2)
      ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2))
      ↔ sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2) ∈ ceo_shiftSquare.edges :=
    fwr_faceCutMatch_of_nodup ceo_shiftSquare ceo_shiftSquare_edges_nodup fwr_shiftSquare_faces_adj
  rw [hd, fwr_shiftSquare_shared]
  exact ceo_shiftSquare_edge_mem

/-- Ray counts of `(1, 1)` and `(1, 2)` for `ceo_shiftSquare`. -/
lemma fwr_shiftSquare_rayCounts :
    jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0
      ∧ jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 :=
  ⟨(ceo_shiftSquare_rayCount_endpoints).2, ceo_shiftSquare_inside_odd⟩

/-- The edge `(0, 0)`–`(0, 1)` is not an edge of `ceo_shiftSquare`. -/
lemma fwr_shiftSquare_nonedge_left :
    s((![0, 0] : Site 2), (![0, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

/-- The edge `(0, 0)`–`(1, 0)` is not an edge of `ceo_shiftSquare`. -/
lemma fwr_shiftSquare_nonedge_bottom :
    s((![0, 0] : Site 2), (![1, 0] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

/-- The edge `(1, 0)`–`(1, 1)` is not an edge of `ceo_shiftSquare`. -/
lemma fwr_shiftSquare_nonedge_right :
    s((![1, 0] : Site 2), (![1, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

/-- `PrimalWalkBoundsRegion` is false: no set of sites has the edges of `ceo_shiftSquare` as its
boundary-edge set. -/
theorem fwr_primalWalkBoundsRegion_false : ¬ PrimalWalkBoundsRegion := by
  intro h
  obtain ⟨S, hS⟩ := h ceo_shiftSquare
  have hadj_ab : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := ceo_uv_adj
  have hadj_a0 : (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hadj_01 : (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![1, 0] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hadj_1b : (hypercubicLattice 2).Adj (![1, 0] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hab : bdEdge S s((![0, 1] : Site 2), (![1, 1] : Site 2)) :=
    (hS hadj_ab).mp (List.mem_toFinset.mpr ceo_shiftSquare_edge_mem)
  have ha0 : ¬ bdEdge S s((![0, 0] : Site 2), (![0, 1] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_left (List.mem_toFinset.mp ((hS hadj_a0).mpr hbd))
  have h01 : ¬ bdEdge S s((![0, 0] : Site 2), (![1, 0] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_bottom (List.mem_toFinset.mp ((hS hadj_01).mpr hbd))
  have h1b : ¬ bdEdge S s((![1, 0] : Site 2), (![1, 1] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_right (List.mem_toFinset.mp ((hS hadj_1b).mpr hbd))
  rw [bdEdge_mk] at hab ha0 h01 h1b
  by_cases m01 : (![0, 1] : Site 2) ∈ S <;> by_cases m11 : (![1, 1] : Site 2) ∈ S <;>
    by_cases m00 : (![0, 0] : Site 2) ∈ S <;> by_cases m10 : (![1, 0] : Site 2) ∈ S <;>
    simp_all

/-- The face-region matching for the trivial walk. -/
lemma fwr_faceCutMatch_nil {a : Site 2} {c d : Site 2}
    (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) c
      ↔ ¬ fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) d)
      ↔ sharedPrimalEdge c d ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges :=
  fwr_faceCutMatch_of_nodup _ (by simp) hcd

/-- Summary: the parity flip for every closed walk, and the matching for walks without repeated
edges. -/
lemma fwr_scope {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d)
      ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)))
    ∧ (Vc.edges.Nodup →
      ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges)) :=
  ⟨fwr_faceCutFlip Vc hcd, fun hnd => fwr_faceCutMatch_of_nodup Vc hnd hcd⟩

end Walls
end StatMech
