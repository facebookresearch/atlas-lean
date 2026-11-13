/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Percolation.GridBoxConnected
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.HrouteHighDim

open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}
















noncomputable def bc6_closeBoxExcept (N : ℕ) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) : ConfigSpace (Sym2 (Site d)) :=
  fun e => if e ∈ G then true else if e ∈ boxEdges d N then false else ω e

@[simp] lemma bc6_closeBoxExcept_of_mem_G {N : ℕ} {G : Finset (Sym2 (Site d))}
    {e : Sym2 (Site d)} (h : e ∈ G) (ω : ConfigSpace (Sym2 (Site d))) :
    bc6_closeBoxExcept N G ω e = true := by
  simp [bc6_closeBoxExcept, h]

@[simp] lemma bc6_closeBoxExcept_of_mem_box {N : ℕ} {G : Finset (Sym2 (Site d))}
    {e : Sym2 (Site d)} (hG : e ∉ G) (hbox : e ∈ boxEdges d N)
    (ω : ConfigSpace (Sym2 (Site d))) :
    bc6_closeBoxExcept N G ω e = false := by
  simp [bc6_closeBoxExcept, hG, hbox]

@[simp] lemma bc6_closeBoxExcept_of_outside {N : ℕ} {G : Finset (Sym2 (Site d))}
    {e : Sym2 (Site d)} (hG : e ∉ G) (hbox : e ∉ boxEdges d N)
    (ω : ConfigSpace (Sym2 (Site d))) :
    bc6_closeBoxExcept N G ω e = ω e := by
  simp [bc6_closeBoxExcept, hG, hbox]












theorem bc6_closeBoxExcept_le {N : ℕ} (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) {e : Sym2 (Site d)}
    (h : bc6_closeBoxExcept N G ω e = true) (hG : e ∉ G) :
    e ∉ boxEdges d N ∧ ω e = true := by
  by_cases hbox : e ∈ boxEdges d N
  · 
    rw [bc6_closeBoxExcept_of_mem_box hG hbox] at h
    exact absurd h (by simp)
  · 
    refine ⟨hbox, ?_⟩
    rwa [bc6_closeBoxExcept_of_outside hG hbox] at h





















theorem bc6_closeBoxExceptEdge_cases (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (h : removeSite 0 (bc6_closeBoxExcept N G ω) e = true) :
    (0 : Site d) ∉ e ∧ (e ∈ G ∨ (ω e = true ∧ e ∉ boxEdges d N)) := by
  
  have hno0 : (0 : Site d) ∉ e := by
    intro hmem
    rw [removeSite_apply_of_mem hmem] at h
    exact Bool.false_ne_true h
  refine ⟨hno0, ?_⟩
  
  rw [removeSite_apply_of_notMem hno0] at h
  by_cases hG : e ∈ G
  · exact Or.inl hG
  · 
    obtain ⟨hbox, hω⟩ := bc6_closeBoxExcept_le G ω h hG
    exact Or.inr ⟨hω, hbox⟩






theorem bc6_origin_notMem (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (h : removeSite 0 (bc6_closeBoxExcept N G ω) e = true) :
    (0 : Site d) ∉ e :=
  (bc6_closeBoxExceptEdge_cases ω N G h).1




theorem bc6_endpoints_ne_zero (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (h : removeSite 0 (bc6_closeBoxExcept N G ω) s(x, y) = true) :
    x ≠ (0 : Site d) ∧ y ≠ (0 : Site d) := by
  have hno0 : (0 : Site d) ∉ s(x, y) := bc6_origin_notMem ω N G h
  rw [Sym2.mem_iff] at hno0
  push Not at hno0
  exact ⟨fun hx => hno0.1 hx.symm, fun hy => hno0.2 hy.symm⟩







theorem bc6_corridor_or_outsideBox (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (h : removeSite 0 (bc6_closeBoxExcept N G ω) e = true) :
    e ∈ G ∨ (ω e = true ∧ e ∉ boxEdges d N) :=
  (bc6_closeBoxExceptEdge_cases ω N G h).2
















theorem bc6_endpoint_outside_box_of_not_boxEdge {N : ℕ} {x y : Site d}
    (hadj : (hypercubicLattice d).Adj x y) (hnb : s(x, y) ∉ boxEdges d N) :
    x ∉ box d N ∨ y ∉ box d N := by
  by_contra hcon
  push Not at hcon
  exact hnb (mk_mem_boxEdges hcon.1 hcon.2 hadj)















theorem bc6_isOpenEdge_dichotomy (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) x y) :
    (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧
      (s(x, y) ∈ G ∨ (ω s(x, y) = true ∧ s(x, y) ∉ boxEdges d N)) := by
  obtain ⟨hadj, hopen⟩ := h
  obtain ⟨hno0, hcase⟩ := bc6_closeBoxExceptEdge_cases ω N G hopen
  exact ⟨hadj, hno0, hcase⟩












theorem bc6_edgeDichotomy (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {u v : Site d}
    (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v) :
    (hypercubicLattice d).Adj u v ∧ (0 : Site d) ∉ s(u, v) ∧
      (s(u, v) ∈ G ∨ (ω s(u, v) = true ∧ (u ∉ box d N ∨ v ∉ box d N))) := by
  obtain ⟨hadj, hno0, hcase⟩ := bc6_isOpenEdge_dichotomy ω N G h
  refine ⟨hadj, hno0, ?_⟩
  rcases hcase with hG | ⟨hω, hnb⟩
  · exact Or.inl hG
  · exact Or.inr ⟨hω, bc6_endpoint_outside_box_of_not_boxEdge hadj hnb⟩







theorem bc6_openSubgraph_le_lattice (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) :
    openSubgraph d (removeSite 0 (bc6_closeBoxExcept N G ω)) ≤ hypercubicLattice d :=
  openSubgraph_le _














theorem bc6_edgeSet_cases (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (h : e ∈ (openSubgraph d (removeSite 0 (bc6_closeBoxExcept N G ω))).edgeSet) :
    e ∈ (hypercubicLattice d).edgeSet ∧ (0 : Site d) ∉ e ∧
      (e ∈ G ∨ (ω e = true ∧ e ∉ boxEdges d N)) := by
  refine ⟨SimpleGraph.edgeSet_subset_edgeSet.mpr (openSubgraph_le _) h, ?_⟩
  induction e with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet, openSubgraph_adj] at h
    exact bc6_closeBoxExceptEdge_cases ω N G h.2














theorem bc6_isOpenEdge_dichotomy_corridor (ω : ConfigSpace (Sym2 (Site d)))
    (N : ℕ) (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) {x y : Site d}
    (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N
          (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
            hrHD_corridorEdges j₃ (L₃ + 1)) ω)) x y) :
    (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧
      (s(x, y) ∈ hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
          hrHD_corridorEdges j₃ (L₃ + 1) ∨
        (ω s(x, y) = true ∧ s(x, y) ∉ boxEdges d N)) :=
  bc6_isOpenEdge_dichotomy ω N
    (hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
      hrHD_corridorEdges j₃ (L₃ + 1)) h










theorem bc6_edgedichotomy (ω : ConfigSpace (Sym2 (Site d))) (N : ℕ)
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (h : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) x y) :
    (hypercubicLattice d).Adj x y ∧ (0 : Site d) ∉ s(x, y) ∧
      (s(x, y) ∈ G ∨ (ω s(x, y) = true ∧ s(x, y) ∉ boxEdges d N)) :=
  bc6_isOpenEdge_dichotomy ω N G h

end Walls

end StatMech
