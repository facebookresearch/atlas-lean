/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.FrontierD.FKQgt4SquareFiniteDuality
import Code.Lattice.EulerFaces

open Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section


def fkSquareInteriorFace (n : Nat) (f : Site 2) : Prop :=
  -(n : Int) <= f 0 ∧ f 0 < n ∧ -(n : Int) <= f 1 ∧ f 1 < n

theorem fkSquareInteriorFace_corners_mem_box {n : Nat} {a b : Int}
    (hf : fkSquareInteriorFace n ![a, b]) :
    faceCorner00 a b ∈ box 2 n ∧ faceCorner10 a b ∈ box 2 n ∧
      faceCorner11 a b ∈ box 2 n ∧ faceCorner01 a b ∈ box 2 n := by
  unfold fkSquareInteriorFace at hf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
  repeat' apply And.intro
  all_goals
    rw [mem_box2']
    simp only [faceCorner00, faceCorner10, faceCorner11, faceCorner01,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> omega



theorem fkSquareBox_imageGraph_edge_mem (n : Nat) {x y : Site 2}
    (hx : x ∈ box 2 n) (hy : y ∈ box 2 n)
    (hxy : (hypercubicLattice 2).Adj x y) :
    s(x, y) ∈ (imageGraph (fkSquareBoxPlanar n)).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_, rfl, rfl⟩
  exact hxy



theorem fkSquareInteriorFace_sharedPrimalEdge_mem {n : Nat} {f g : Site 2}
    (hf : fkSquareInteriorFace n f)
    (hfg : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge f g ∈
      (imageGraph (fkSquareBoxPlanar n)).edgeSet := by
  have ff : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> rfl
  have fg : g = ![g 0, g 1] := by
    funext i
    fin_cases i <;> rfl
  have hadj := hfg
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hcases :
      (g 0 = f 0 + 1 ∧ g 1 = f 1) ∨
      (g 0 = f 0 - 1 ∧ g 1 = f 1) ∨
      (g 0 = f 0 ∧ g 1 = f 1 + 1) ∨
      (g 0 = f 0 ∧ g 1 = f 1 - 1) := by
    omega
  have hf' : fkSquareInteriorFace n ![f 0, f 1] := by
    rw [← ff]
    exact hf
  obtain ⟨h00, h10, h11, h01⟩ :=
    fkSquareInteriorFace_corners_mem_box (n := n) (a := f 0) (b := f 1)
      hf'
  rcases hcases with hright | hleft | htop | hbottom
  · rw [ff, fg, hright.1, hright.2, sharedPrimalEdge_right]
    exact fkSquareBox_imageGraph_edge_mem n h10 h11 (by
      simp [faceCorner10, faceCorner11, hypercubicLattice_adj,
        Fin.sum_univ_two])
  · rw [ff, fg, hleft.1, hleft.2, sharedPrimalEdge_left]
    exact fkSquareBox_imageGraph_edge_mem n h00 h01 (by
      simp [faceCorner00, faceCorner01, hypercubicLattice_adj,
        Fin.sum_univ_two])
  · rw [ff, fg, htop.1, htop.2, sharedPrimalEdge_top]
    exact fkSquareBox_imageGraph_edge_mem n h01 h11 (by
      simp [faceCorner01, faceCorner11, hypercubicLattice_adj,
        Fin.sum_univ_two])
  · rw [ff, fg, hbottom.1, hbottom.2, sharedPrimalEdge_bottom]
    exact fkSquareBox_imageGraph_edge_mem n h00 h10 (by
      simp [faceCorner00, faceCorner10, hypercubicLattice_adj,
        Fin.sum_univ_two])



theorem fkSquareInteriorFace_isolated {n : Nat} {f : Site 2}
    (hf : fkSquareInteriorFace n f) (g : Site 2) :
    ¬ (whb_faceRegion (imageGraph (fkSquareBoxPlanar n))).Adj f g := by
  rintro ⟨hfg, hmissing⟩
  exact hmissing (fkSquareInteriorFace_sharedPrimalEdge_mem hf hfg)


theorem fkSquareInteriorFace_component_supp {n : Nat} {f : Site 2}
    (hf : fkSquareInteriorFace n f) :
    ((whb_faceRegion (imageGraph (fkSquareBoxPlanar n))).connectedComponentMk f).supp =
      {f} := by
  ext x
  rw [ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rw [ConnectedComponent.eq] at h
    obtain ⟨w⟩ := h.symm
    cases w with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (fkSquareInteriorFace_isolated hf _)
  · rintro rfl
    rfl


theorem pfdFace_injective_on_fkSquareInteriorFace (n : Nat) {f g : Site 2}
    (hf : fkSquareInteriorFace n f)
    (hfg : pfdFace (fkSquareBoxPlanar n) f =
      pfdFace (fkSquareBoxPlanar n) g) :
    f = g := by
  have hmem : g ∈
      ((whb_faceRegion (imageGraph (fkSquareBoxPlanar n))).connectedComponentMk f).supp := by
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact ConnectedComponent.eq.mp hfg.symm
  rw [fkSquareInteriorFace_component_supp hf, Set.mem_singleton_iff] at hmem
  exact hmem.symm

end

end StatMech.FrontierD
