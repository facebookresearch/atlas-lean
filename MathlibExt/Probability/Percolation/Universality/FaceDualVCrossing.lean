/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.Universality.DualCrossingFrameCounterexample
public import MathlibExt.Probability.Percolation.Universality.FrameChangeIso

/-!
# Face-dual vertical crossings and the left-cluster boundary graph

Faces of `ℤ²` are indexed by their lower-left corner: `![a, b]` is the unit square
`[a, a + 1] × [b, b + 1]`. Two lattice-adjacent faces share one primal edge
(`sharedPrimalEdge`). In the face-dual graph `fci_faceOpenDual ω` two adjacent faces are joined
when their shared primal edge is closed; this is the usual dual lattice with dual-open edges.

For the box `[0, n]²`, the standard crossing-duality lemma says: there is no open left–right
crossing iff there is a dual-open path of faces from the row of faces just below the box to the
row just above it, through faces of columns `0, …, n - 1`. This file defines that target event
and the graph through which the subsequent files try to produce it:

* `pmd_FaceDualVCrossing ω n`: a path in `fci_faceOpenDual ω` from some face `![a₀, -1]` to some
  face `![a₁, n]` with `0 ≤ a₀, a₁ ≤ n - 1`. The path itself is *not* required to stay inside the
  dual box, so this event is weaker than the textbook dual crossing and is not disjoint from
  `HorizontalCrossing ω 0 n 0 n` (closed edges outside the box can carry the path).
* `pmd_boxFaceBarrier ω n`: the subgraph of the face boundary graph of the left cluster
  `bcd_leftReach ω n` whose shared primal edges have both endpoints in the box. It is a subgraph
  of `fci_faceOpenDual ω` (`pmd_boxFaceBarrier_le_faceOpenDual`) because boundary edges of the
  left cluster inside the box are closed.
* `pmd_BarrierConnectsRows ω n`: `pmd_boxFaceBarrier ω n` joins the row below the box to the row
  above it. This is the residual hypothesis of the reduction; no file proves it for general `ω`.

## Main results

* `pmd_faceDualVCrossing_of_residue`: `pmd_BarrierConnectsRows ω n → pmd_FaceDualVCrossing ω n`.
* `pmd_wall_barrierConnectsRows`, `pmd_wall_faceDualVCrossing`: on the wall configuration
  `bcc_wallCfg` (no horizontal crossing of `[0, 2]²`) both hold, so the residual hypothesis is
  satisfiable.
* `pmd_wall_only_face_frame_works`: on `bcc_wallCfg` the face-dual crossing holds while the two
  vertex-frame candidates of `DualCrossingFrameCounterexample` fail.

## References

* B. Bollobás and O. Riordan, *Percolation*, Cambridge University Press, 2006 (planar duality of
  crossings of rectangles).
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box

namespace StatMech

namespace Universality

/-- A closed top edge of face `![a, b]` makes it face-dual adjacent to the face above it. -/
theorem pmd_faceVAdj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ)
    (hcl : ω s(![a, b + 1], ![a + 1, b + 1]) = false) :
    (fci_faceOpenDual ω).Adj ![a, b] ![a, b + 1] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; exact hcl

/-- A closed right edge of face `![a, b]` makes it face-dual adjacent to the face on its right. -/
theorem pmd_faceHAdj_of_closed (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ)
    (hcl : ω s(![a + 1, b], ![a + 1, b + 1]) = false) :
    (fci_faceOpenDual ω).Adj ![a, b] ![a + 1, b] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11; exact hcl

/-- Face-dual vertical crossing of the box `[0, n]²`: a dual-open path of faces from a face
`![a₀, -1]` below the box to a face `![a₁, n]` above it, with `0 ≤ a₀, a₁ ≤ n - 1`. Only the
endpoints are constrained; the path may leave the dual box. -/
def pmd_FaceDualVCrossing (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
    (fci_faceOpenDual ω).Reachable ![a₀, -1] ![a₁, n]

/-- A closed face-dual walk visiting a face below the box and a face above it gives a face-dual
vertical crossing. -/
theorem pmd_faceDualVCrossing_of_spanningContour (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {u : Site 2} (c : (fci_faceOpenDual ω).Walk u u)
    {a₀ a₁ : ℤ} (ha0 : 0 ≤ a₀) (ha0' : a₀ ≤ n - 1) (ha1 : 0 ≤ a₁) (ha1' : a₁ ≤ n - 1)
    (hbot : (![a₀, -1] : Site 2) ∈ c.support) (htop : (![a₁, n] : Site 2) ∈ c.support) :
    pmd_FaceDualVCrossing ω n := by
  classical
  refine ⟨a₀, a₁, ha0, ha0', ha1, ha1', ?_⟩
  exact (Reachable.symm ⟨c.takeUntil _ hbot⟩).trans ⟨c.takeUntil _ htop⟩

/-- A face-dual vertical crossing joins some face of row `-1` to some face of row `n` (the column
bounds are forgotten). -/
theorem pmd_faceDualV_implies_spanningReach (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pmd_FaceDualVCrossing ω n) :
    ∃ (a₀ a₁ : ℤ), (fci_faceOpenDual ω).Reachable ![a₀, -1] ![a₁, n] := by
  obtain ⟨a₀, a₁, _, _, _, _, hreach⟩ := h
  exact ⟨a₀, a₁, hreach⟩

/-- The box part of the face boundary graph of the left cluster `bcd_leftReach ω n`: adjacent
faces whose shared primal edge is a boundary edge of the left cluster with both endpoints in the
box `[0, n]²`. See also `fci_faceOpenDual` (it is a subgraph, `pmd_boxFaceBarrier_le_faceOpenDual`)
and `faceBoundaryGraph` (`cac_boxFaceBarrier_le_faceBoundaryGraph`). -/
def pmd_boxFaceBarrier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧
    ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧
      bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n
  symm := by
    refine ⟨?_⟩
    rintro f g ⟨hadj, p, q, hpq, hbd, hp, hq⟩
    refine ⟨hadj.symm, q, p, ?_, ?_, hq, hp⟩
    · rw [← sharedPrimalEdge_comm_of_adj hadj, hpq, Sym2.eq_swap]
    · rwa [Sym2.eq_swap]
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem pmd_boxFaceBarrier_adj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (f g : Site 2) :
    (pmd_boxFaceBarrier ω n).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧
        ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧
          bdEdge (bcd_leftReach ω n) s(p, q) ∧ p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n := Iff.rfl

/-- Boundary edges of the left cluster inside the box are closed, so the box face barrier is a
subgraph of the face-dual graph. -/
theorem pmd_boxFaceBarrier_le_faceOpenDual (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pmd_boxFaceBarrier ω n ≤ fci_faceOpenDual ω := by
  rintro f g ⟨hadj, p, q, hpq, hbd, hp, hq⟩
  refine ⟨hadj, ?_⟩
  have hpadj : (hypercubicLattice 2).Adj p q := by
    obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hadj
    rw [hpq'] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> subst e1 <;> subst e2
    · exact hadj'
    · exact hadj'.symm
  rw [bdEdge_mk] at hbd
  rw [hpq]
  by_cases hpL : p ∈ bcd_leftReach ω n
  · exact bcd_leftReach_boundary_closed ω n hpL hq hpadj (hbd.mp hpL)
  · have hqL : q ∈ bcd_leftReach ω n := by by_contra hqn; exact hpL (hbd.mpr hqn)
    rw [Sym2.eq_swap]
    exact bcd_leftReach_boundary_closed ω n hqL hp hpadj.symm hpL

/-- The box face barrier joins a face `![a₀, -1]` below the box to a face `![a₁, n]` above it,
`0 ≤ a₀, a₁ ≤ n - 1`. Under `¬ HorizontalCrossing ω 0 n 0 n` this is the content of the planar
crossing-duality lemma; it is a hypothesis here, not proved for general `ω`. -/
def pmd_BarrierConnectsRows (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) : Prop :=
  ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
    (pmd_boxFaceBarrier ω n).Reachable ![a₀, -1] ![a₁, n]

/-- If the box face barrier joins the rows below and above the box, there is a face-dual
vertical crossing. -/
theorem pmd_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pmd_BarrierConnectsRows ω n) : pmd_FaceDualVCrossing ω n := by
  obtain ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach⟩ := h
  exact ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach.mono (pmd_boxFaceBarrier_le_faceOpenDual ω n)⟩

/-- Dichotomy form of `pmd_faceDualVCrossing_of_residue`: under `pmd_BarrierConnectsRows ω n`,
either there is a horizontal crossing or a face-dual vertical crossing. The hypothesis
`¬ HorizontalCrossing ω 0 n 0 n` is unused (the right disjunct always holds). -/
theorem pmd_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : pmd_BarrierConnectsRows ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (pmd_faceDualVCrossing_of_residue ω n h)

/-- In the wall configuration the faces of column `0` are face-dual adjacent vertically from
row `-1` to row `2`. -/
theorem pmd_wall_faceVAdj {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (fci_faceOpenDual bcc_wallCfg).Adj ![0, b] ![0, b + 1] := by
  apply pmd_faceVAdj_of_closed
  simp only [bcc_wallCfg]
  rcases hb with rfl | rfl | rfl <;> decide

/-- The wall configuration has a face-dual vertical crossing of `[0, 2]²`. -/
theorem pmd_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 := by
  refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 := (pmd_wall_faceVAdj (b := -1) (by tauto)).reachable
  have h2 := (pmd_wall_faceVAdj (b := 0) (by tauto)).reachable
  have h3 := (pmd_wall_faceVAdj (b := 1) (by tauto)).reachable
  norm_num at h1 h2 h3 ⊢
  exact (h1.trans h2).trans h3

/-- In the wall configuration the faces of column `0` are adjacent in the box face barrier
vertically from row `-1` to row `2`. -/
theorem pmd_wall_barrierVAdj {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, b] ![0, b + 1] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![0, b + 1], ![1, b + 1],
    ?_, ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; rfl
  · rw [bdEdge_mk]
    constructor
    · intro _
      exact fun hc => by
        have := rdv_leftReach_wall_x0 hc; simp at this
    · intro hno
      exact dcw_leftSide_in_L bcc_wallCfg 2
        ⟨by rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp, by simp⟩
  · rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp
  · rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp

/-- The residual hypothesis `pmd_BarrierConnectsRows` holds for the wall configuration. -/
theorem pmd_wall_barrierConnectsRows : pmd_BarrierConnectsRows bcc_wallCfg 2 := by
  refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 := (pmd_wall_barrierVAdj (b := -1) (by tauto)).reachable
  have h2 := (pmd_wall_barrierVAdj (b := 0) (by tauto)).reachable
  have h3 := (pmd_wall_barrierVAdj (b := 1) (by tauto)).reachable
  norm_num at h1 h2 h3 ⊢
  exact (h1.trans h2).trans h3

/-- The wall configuration has no horizontal crossing of `[0, 2]²` but has a face-dual vertical
crossing. -/
theorem pmd_wall_noH_yet_faceDualV :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, pmd_wall_faceDualVCrossing⟩

/-- On the wall configuration there is no horizontal crossing of `[0, 2]²`, the two vertex-frame
dual events `DualVerticalCrossing ω 0 2 0 2` and `dcp_DualCutConnectsRot ω 2` fail, and the
face-dual vertical crossing holds. -/
theorem pmd_wall_only_face_frame_works :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ DualVerticalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 ∧
      pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall, rdv_rotResidue_false_on_noH, pmd_wall_faceDualVCrossing⟩

end Universality

end StatMech
