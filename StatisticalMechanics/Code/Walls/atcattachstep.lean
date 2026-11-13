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
import Code.Lattice.EarExistence
import Code.Walls.pc2boundaryconn
import Code.Walls.fbcconnected

open Finset Set SimpleGraph

namespace StatMech

namespace Walls

open StatMech.Lattice
open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable










theorem atc_exists_extremeCell_finset (K : Finset (Site 2)) (hne : K.Nonempty) :
    ∃ c ∈ K, IsExtremeCell (↑K : Set (Site 2)) c := by
  obtain ⟨c, hc⟩ := exists_extremeCell (↑K : Set (Site 2)) K.finite_toSet (by
    rwa [Finset.coe_nonempty])
  exact ⟨c, hc.mem, hc⟩













theorem atc_induce_insert_reachable_from_anchor {V : Type*} (G : SimpleGraph V) (S : Set V)
    (w : V) (hwS : w ∉ S) {s₀ n : V} (hs₀ : s₀ ∈ S) (hn : n ∈ S) (hadj : G.Adj w n)
    (hreach : ∀ v : S, (G.induce S).Reachable ⟨s₀, hs₀⟩ v) :
    ∀ v : (insert w S : Set V),
      (G.induce (insert w S : Set V)).Reachable ⟨s₀, Set.mem_insert_of_mem w hs₀⟩ v := by
  classical
  
  have hsub : S ≤ (insert w S : Set V) := Set.subset_insert w S
  set ι := SimpleGraph.induceHomOfLE G hsub with hι
  
  have key : ∀ (v : V) (hv : v ∈ S),
      (G.induce (insert w S : Set V)).Reachable
        ⟨s₀, Set.mem_insert_of_mem w hs₀⟩ ⟨v, Set.mem_insert_of_mem w hv⟩ := by
    intro v hv
    have hr := hreach ⟨v, hv⟩
    
    obtain ⟨p⟩ := hr
    refine ⟨(p.map ι.toHom).copy rfl rfl⟩
  intro v
  obtain ⟨v, hv⟩ := v
  rcases hv with hvw | hvS
  · 
    have hstep : (G.induce (insert w S : Set V)).Adj
        ⟨n, Set.mem_insert_of_mem w hn⟩ ⟨w, Set.mem_insert w S⟩ := by
      rw [SimpleGraph.induce_adj]; exact hadj.symm
    have : (G.induce (insert w S : Set V)).Reachable
        ⟨s₀, Set.mem_insert_of_mem w hs₀⟩ ⟨w, Set.mem_insert w S⟩ :=
      (key n hn).trans hstep.reachable
    
    subst hvw
    exact this
  · exact key v hvS









theorem atc_compl_erase {K : Finset (Site 2)} {c : Site 2} (hc : c ∈ K) :
    ((↑(K.erase c) : Set (Site 2))ᶜ) = insert c ((↑K : Set (Site 2))ᶜ) := by
  ext x
  simp only [Finset.coe_erase, Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_insert_iff, Finset.mem_coe]
  by_cases hx : x = c
  · subst hx; simp
  · simp [hx]




theorem atc_holeFree_erase {K : Finset (Site 2)} {c : Site 2} (hc : c ∈ K)
    (hhf : pc2_HoleFree (↑K : Set (Site 2)))
    {n : Site 2} (hn : n ∉ K) (hadj : (hypercubicLattice 2).Adj c n) :
    pc2_HoleFree (↑(K.erase c) : Set (Site 2)) := by
  classical
  unfold pc2_HoleFree at hhf ⊢
  rw [atc_compl_erase hc]
  
  have hnc : n ∈ ((↑K : Set (Site 2))ᶜ) := by
    simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hn
  have hcnc : c ∉ ((↑K : Set (Site 2))ᶜ) := by
    simp only [Set.mem_compl_iff, Finset.mem_coe, not_not]; exact hc
  have hforall := atc_induce_insert_reachable_from_anchor (hypercubicLattice 2)
    ((↑K : Set (Site 2))ᶜ) c hcnc hnc hnc hadj
    (fun x => hhf.preconnected ⟨n, hnc⟩ x)
  haveI : Nonempty ↥(insert c ((↑K : Set (Site 2))ᶜ)) :=
    ⟨⟨n, Set.mem_insert_of_mem c hnc⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro u v
  exact (hforall u).symm.trans (hforall v)









theorem atc_latAdj_top' (c : Site 2) : (hypercubicLattice 2).Adj c ![c 0, c 1 + 1] := by
  have h := latAdj_top (c 0) (c 1)
  rwa [show (![c 0, c 1] : Site 2) = c from by funext i; fin_cases i <;> rfl] at h




theorem atc_extremeCell_top_nmem {K : Finset (Site 2)} {c : Site 2}
    (hc : IsExtremeCell (↑K : Set (Site 2)) c) : (![c 0, c 1 + 1] : Site 2) ∉ K := by
  intro hmem
  have hnmem := extremeCell_not_mem_of_higher (↑K : Set (Site 2)) c ![c 0, c 1 + 1] hc
    (by have : (![c 0, c 1 + 1] : Site 2) 1 = c 1 + 1 := rfl
        rw [this]; omega)
  exact hnmem (Finset.mem_coe.mpr hmem)



theorem atc_holeFree_erase_extremeCell {K : Finset (Site 2)} {c : Site 2}
    (hcK : c ∈ K) (hc : IsExtremeCell (↑K : Set (Site 2)) c)
    (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
    pc2_HoleFree (↑(K.erase c) : Set (Site 2)) :=
  atc_holeFree_erase hcK hhf (atc_extremeCell_top_nmem hc) (atc_latAdj_top' c)













def atc_HasRemovableConnCell : Prop :=
  ∀ (K : Finset (Site 2)), 2 ≤ K.card → IsConnectedCluster K →
    ∃ c ∈ K, c ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj c n) ∧
      IsConnectedCluster (K.erase c)





theorem atc_hasRemovableCell_of_conn (h : atc_HasRemovableConnCell) : fbc_HasRemovableCell := by
  intro K hcard hconn hhf
  obtain ⟨c, hcK, hcorigin, ⟨n, hn, hadj⟩, hconn'⟩ := h K hcard hconn
  exact ⟨c, hcK, hcorigin, hconn', atc_holeFree_erase hcK hhf hn hadj⟩

end Walls

end StatMech
