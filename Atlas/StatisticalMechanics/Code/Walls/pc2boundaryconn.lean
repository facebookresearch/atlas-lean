/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.PeierlsSingleCircuit
import Code.Lattice.PeierlsBoundaryConnected

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable





theorem pc2_box_faceBoundaryConnected (m n : ℕ) :
    FaceBoundaryConnected (↑(boxCluster m n)) (boxFrame m n) :=
  boxCluster_faceBoundaryConnected m n















theorem pc2_faceBoundaryConnected_of_anchor {K : Set (Site 2)} {T : Finset (Site 2)}
    {a₀ : Site 2} (ha₀ : a₀ ∈ T)
    (hwalk : ∀ f ∈ T, ∃ p : (faceBoundaryGraph K).Walk a₀ f, ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T := by
  apply faceBoundaryConnected_of_walks ⟨a₀, ha₀⟩
  intro f hf g hg
  obtain ⟨pf, hpf⟩ := hwalk f hf
  obtain ⟨pg, hpg⟩ := hwalk g hg
  refine ⟨pf.reverse.append pg, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append] at hw
  rcases List.mem_append.mp hw with hwf | hwg
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hwf
    exact hpf w hwf
  · exact hpg w (List.mem_of_mem_tail hwg)





theorem pc2_box_faceBoundaryConnected_via_anchor (m n : ℕ) :
    FaceBoundaryConnected (↑(boxCluster m n)) (boxFrame m n) :=
  pc2_faceBoundaryConnected_of_anchor (mem_boxFrame_corner m n)
    (fun _ hf => boxFrame_walk_from_corner m n hf)













def pc2_HoleFree (K : Set (Site 2)) : Prop :=
  ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected








def pc2_BoundaryConnGivenHoleFree : Prop :=
  ∀ (K : Finset (Site 2)), IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) →
    ∀ (hfin : (↑K : Set (Site 2)).Finite),
      FaceBoundaryConnected (↑K : Set (Site 2)) (boundarySupport hfin)






theorem pc2_single_dualCircuit_of_residue (h : pc2_BoundaryConnGivenHoleFree)
    (K : Finset (Site 2)) (hconn : IsConnectedCluster K)
    (hhf : pc2_HoleFree (↑K : Set (Site 2))) (hfin : (↑K : Set (Site 2)).Finite)
    {f₀ : Site 2} (hf₀ : f₀ ∈ (boundarySupport hfin : Set (Site 2))) :
    ∃ c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f₀ f₀,
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges :=
  exists_single_dualCircuit_of_connected hfin (h K hconn hhf hfin) hf₀










noncomputable def pc2_tromino : Finset (Site 2) :=
  {![(0:ℤ), 0], ![(1:ℤ), 0], ![(0:ℤ), 1]}


theorem pc2_mem_tromino (p q : ℤ) :
    (![p, q] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) ↔
      (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by
  unfold pc2_tromino
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  rw [site2_eq, site2_eq, site2_eq]


theorem pc2_origin_mem_tromino : origin 2 ∈ pc2_tromino := by
  unfold pc2_tromino; rw [origin_eq_zerozero]; simp



theorem pc2_tromino_isConnectedCluster : IsConnectedCluster pc2_tromino := by
  refine ⟨pc2_origin_mem_tromino, ?_⟩
  intro x hx
  have hm : (![x 0, x 1] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [show (![x 0, x 1] : Site 2) = x from by funext i; fin_cases i <;> rfl, Finset.mem_coe]
    exact hx
  have h00 : origin 2 ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [Finset.mem_coe]; exact pc2_origin_mem_tromino
  rw [origin_eq_zerozero]
  rw [show x = ![x 0, x 1] from by funext i; fin_cases i <;> rfl]
  rw [pc2_mem_tromino] at hm
  
  have h00' : (![(0:ℤ), 0] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [pc2_mem_tromino]; tauto
  have m10 : (![(1:ℤ), 0] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [pc2_mem_tromino]; tauto
  have m01 : (![(0:ℤ), 1] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [pc2_mem_tromino]; tauto
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    refine SimpleGraph.Adj.reachable ⟨?_, h00', m10⟩
    have := latAdj_right 0 0; rwa [show (0:ℤ) + 1 = 1 from by ring] at this
  · rw [h1, h2]
    refine SimpleGraph.Adj.reachable ⟨?_, h00', m01⟩
    have := latAdj_top 0 0; rwa [show (0:ℤ) + 1 = 1 from by ring] at this














noncomputable def pc2_tromFrame : Finset (Site 2) :=
  {![(-1:ℤ), -1], ![(0:ℤ), -1], ![(1:ℤ), -1], ![(1:ℤ), 0],
   ![(0:ℤ), 0], ![(0:ℤ), 1], ![(-1:ℤ), 1], ![(-1:ℤ), 0]}




theorem pc2_bdEdge_trom {p q : Site 2} (hp : p ∈ (↑pc2_tromino : Set (Site 2)))
    (hq : q ∉ (↑pc2_tromino : Set (Site 2))) : bdEdge (↑pc2_tromino : Set (Site 2)) s(p, q) := by
  rw [bdEdge_mk]; exact ⟨fun _ => hq, fun _ => hp⟩


theorem pc2_trom_adj_1 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), -1] ![(0:ℤ), -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_right (-1) (-1); rwa [show (-1:ℤ) + 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_right (-1) (-1)
    rw [show (-1:ℤ) + 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner10 faceCorner11; rw [show (-1:ℤ) + 1 = 0 from by ring]
    
    rw [show s((![(0:ℤ), -1] : Site 2), (![(0:ℤ), 0] : Site 2))
      = s((![(0:ℤ), 0] : Site 2), (![(0:ℤ), -1] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_2 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), -1] ![(1:ℤ), -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_right (0) (-1); rwa [show (0:ℤ) + 1 = 1 from by ring] at this
  · have h := sharedPrimalEdge_right (0) (-1)
    rw [show (0:ℤ) + 1 = 1 from by ring] at h
    rw [h]; unfold faceCorner10 faceCorner11; rw [show (0:ℤ) + 1 = 1 from by ring,
      show (-1:ℤ) + 1 = 0 from by ring]
    rw [show s((![(1:ℤ), -1] : Site 2), (![(1:ℤ), 0] : Site 2))
      = s((![(1:ℤ), 0] : Site 2), (![(1:ℤ), -1] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_3 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(1:ℤ), -1] ![(1:ℤ), 0] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_top (1) (-1); rwa [show (-1:ℤ) + 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_top (1) (-1)
    rw [show (-1:ℤ) + 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner01 faceCorner11; rw [show (-1:ℤ) + 1 = 0 from by ring,
      show (1:ℤ) + 1 = 2 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_4 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(1:ℤ), 0] ![(0:ℤ), 0] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_left (1) (0); rwa [show (1:ℤ) - 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_left (1) (0)
    rw [show (1:ℤ) - 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner01; rw [show (0:ℤ) + 1 = 1 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_5 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), 0] ![(0:ℤ), 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_top (0) (0); rwa [show (0:ℤ) + 1 = 1 from by ring] at this
  · have h := sharedPrimalEdge_top (0) (0)
    rw [show (0:ℤ) + 1 = 1 from by ring] at h
    rw [h]; unfold faceCorner01 faceCorner11; rw [show (0:ℤ) + 1 = 1 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_6 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), 1] ![(-1:ℤ), 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_left (0) (1); rwa [show (0:ℤ) - 1 = -1 from by ring] at this
  · have h := sharedPrimalEdge_left (0) (1)
    rw [show (0:ℤ) - 1 = -1 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner01; rw [show (1:ℤ) + 1 = 2 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_7 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), 1] ![(-1:ℤ), 0] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_bottom (-1) (1); rwa [show (1:ℤ) - 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_bottom (-1) (1)
    rw [show (1:ℤ) - 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner10; rw [show (-1:ℤ) + 1 = 0 from by ring]
    
    rw [show s((![(-1:ℤ), 1] : Site 2), (![(0:ℤ), 1] : Site 2))
      = s((![(0:ℤ), 1] : Site 2), (![(-1:ℤ), 1] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_8 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), 0] ![(-1:ℤ), -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_bottom (-1) (0); rwa [show (0:ℤ) - 1 = -1 from by ring] at this
  · have h := sharedPrimalEdge_bottom (-1) (0)
    rw [show (0:ℤ) - 1 = -1 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner10; rw [show (-1:ℤ) + 1 = 0 from by ring]
    
    rw [show s((![(-1:ℤ), 0] : Site 2), (![(0:ℤ), 0] : Site 2))
      = s((![(0:ℤ), 0] : Site 2), (![(-1:ℤ), 0] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)




theorem pc2_mem_tromFrame_corner : (![(-1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by
  unfold pc2_tromFrame; simp


theorem pc2_tromFrame_cases {v : Site 2} (hv : v ∈ pc2_tromFrame) :
    v = ![(-1:ℤ), -1] ∨ v = ![(0:ℤ), -1] ∨ v = ![(1:ℤ), -1] ∨ v = ![(1:ℤ), 0] ∨
      v = ![(0:ℤ), 0] ∨ v = ![(0:ℤ), 1] ∨ v = ![(-1:ℤ), 1] ∨ v = ![(-1:ℤ), 0] := by
  unfold pc2_tromFrame at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  tauto




theorem pc2_tromFrame_walk_from_corner {v : Site 2} (hv : v ∈ pc2_tromFrame) :
    ∃ p : (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Walk ![(-1:ℤ), -1] v,
      ∀ w ∈ p.support, w ∈ pc2_tromFrame := by
  have mc : (![(-1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := pc2_mem_tromFrame_corner
  have m1 : (![(0:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m2 : (![(1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m3 : (![(1:ℤ), 0] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m4 : (![(0:ℤ), 0] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m5 : (![(0:ℤ), 1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m6 : (![(-1:ℤ), 1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m7 : (![(-1:ℤ), 0] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  
  rcases pc2_tromFrame_cases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact mc
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 SimpleGraph.Walk.nil, ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl; exacts [mc, m1]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1
      (SimpleGraph.Walk.cons pc2_trom_adj_2 SimpleGraph.Walk.nil), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl; exacts [mc, m1, m2]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 (SimpleGraph.Walk.cons pc2_trom_adj_2
      (SimpleGraph.Walk.cons pc2_trom_adj_3 SimpleGraph.Walk.nil)), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl; exacts [mc, m1, m2, m3]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 (SimpleGraph.Walk.cons pc2_trom_adj_2
      (SimpleGraph.Walk.cons pc2_trom_adj_3 (SimpleGraph.Walk.cons pc2_trom_adj_4
        SimpleGraph.Walk.nil))), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl; exacts [mc, m1, m2, m3, m4]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 (SimpleGraph.Walk.cons pc2_trom_adj_2
      (SimpleGraph.Walk.cons pc2_trom_adj_3 (SimpleGraph.Walk.cons pc2_trom_adj_4
        (SimpleGraph.Walk.cons pc2_trom_adj_5 SimpleGraph.Walk.nil)))), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl; exacts [mc, m1, m2, m3, m4, m5]
  · 
    refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_8.symm
      (SimpleGraph.Walk.cons pc2_trom_adj_7.symm SimpleGraph.Walk.nil), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl; exacts [mc, m7, m6]
  · 
    refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_8.symm SimpleGraph.Walk.nil, ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl; exacts [mc, m7]





theorem pc2_tromino_faceBoundaryConnected :
    FaceBoundaryConnected (↑pc2_tromino : Set (Site 2)) pc2_tromFrame :=
  pc2_faceBoundaryConnected_of_anchor pc2_mem_tromFrame_corner
    (fun _ hf => pc2_tromFrame_walk_from_corner hf)


































end Lattice

end StatMech

