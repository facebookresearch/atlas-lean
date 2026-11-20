/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Mathlib
import Code.Walls.bc103contractdeg

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}















theorem bc105_boxes_overlap_of_close_centres {L : ℕ} {y z : Site d}
    (hyz : (y - z) ∈ box d L) :
    z ∈ bc61_boxAround d L y ∧ z ∈ bc61_boxAround d L z := by
  constructor
  · rw [bc61_mem_boxAround]
    
    rw [mem_box] at hyz ⊢
    intro i
    have hi := hyz i
    have hneg : (z - y) i = -((y - z) i) := by
      simp only [Pi.sub_apply]; ring
    rw [hneg, Int.natAbs_neg]; exact hi
  · rw [bc61_mem_boxAround]
    simp only [sub_self]
    rw [mem_box]; intro i; simp




theorem bc105_centre_mem_own_box (L : ℕ) (z : Site d) : z ∈ bc61_boxAround d L z := by
  rw [bc61_mem_boxAround]; simp only [sub_self]; rw [mem_box]; intro i; simp







theorem bc105_boxes_overlap_of_adjacent_centres {L : ℕ} (hL : 1 ≤ L) (hd : 1 ≤ d) (z : Site d) :
    ∃ y : Site d, y ≠ z ∧ z ∈ bc61_boxAround d L y ∧ z ∈ bc61_boxAround d L z ∧
      y ∈ bc61_boxAround d L y ∧ y ∈ bc61_boxAround d L z := by
  classical
  
  refine ⟨Function.update z ⟨0, hd⟩ (z ⟨0, hd⟩ + 1), ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro h
    have := congrArg (fun f => f ⟨0, hd⟩) h
    simp only [Function.update_self] at this
    omega
  · 
    rw [bc61_mem_boxAround, mem_box]; intro i
    by_cases hi : i = ⟨0, hd⟩
    · subst hi
      have : (z - Function.update z ⟨0, hd⟩ (z ⟨0, hd⟩ + 1)) ⟨0, hd⟩ = -1 := by
        simp [Pi.sub_apply, Function.update_self]
      rw [this]; simpa using hL
    · have : (z - Function.update z ⟨0, hd⟩ (z ⟨0, hd⟩ + 1)) i = 0 := by
        simp [Pi.sub_apply, Function.update_of_ne hi]
      rw [this]; simp
  · exact bc105_centre_mem_own_box L z
  · exact bc105_centre_mem_own_box L _
  · 
    rw [bc61_mem_boxAround, mem_box]; intro i
    by_cases hi : i = ⟨0, hd⟩
    · subst hi
      have : (Function.update z ⟨0, hd⟩ (z ⟨0, hd⟩ + 1) - z) ⟨0, hd⟩ = 1 := by
        simp [Pi.sub_apply, Function.update_self]
      rw [this]; simpa using hL
    · have : (Function.update z ⟨0, hd⟩ (z ⟨0, hd⟩ + 1) - z) i = 0 := by
        simp [Pi.sub_apply, Function.update_of_ne hi]
      rw [this]; simp










open Classical in







theorem bc105_contractedTrifGraph_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc103_ContractedTrifGraph ω L R := by
  classical
  set S : Set (Site d) := {z₀, z₁} with hS
  have hz₀S : z₀ ∈ S := by rw [hS]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hS]; right; rfl
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  set a : (↑S : Type) := ⟨z₀, hz₀S⟩ with ha
  set b : (↑S : Type) := ⟨z₁, hz₁S⟩ with hb
  have hab : a ≠ b := by intro h; exact hzne (congrArg Subtype.val h)
  let G : SimpleGraph (↑S : Type) := SimpleGraph.fromEdgeSet {s(a, b)}
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  have hGac : G.IsAcyclic := bc69_single_edge_acyclic a b hab
  haveI hFdec : DecidableRel (osf_spanForest G).Adj := Classical.decRel _
  have hVall : ∀ v : (↑S : Type), v = a ∨ v = b := by
    intro v; obtain ⟨x, hx⟩ := v
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  
  have hFa : (osf_spanForest G).degree a = 1 := by
    rw [osf_spanForest_degree_of_acyclic G hGac a]; exact bc69_single_edge_degree a b hab
  have hFb : (osf_spanForest G).degree b = 1 := by
    rw [osf_spanForest_degree_of_acyclic G hGac b]; exact bc69_single_edge_degree_b a b hab
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, hFdec, (fun _ => a), ?_, ?_, ?_, ?_⟩
  · 
    intro y hybox htri; exact absurd htri (hno y hybox)
  · 
    intro v; rcases hVall v with rfl | rfl
    · rw [hFa]
    · rw [hFb]
  · 
    intro y hybox htri; exact absurd htri (hno y hybox)
  · 
    intro v _; rcases hVall v with rfl | rfl
    · exact hz₀
    · exact hz₁






theorem bc105_count_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc103_count_of_contractedGraph ω L R
    (bc105_contractedTrifGraph_of_noTrif ω L R hz₀ hz₁ hzne hno)














theorem bc105_adversary_has_trif {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc67_upperLines_is_G_n_trifurcation hL







theorem bc105_adversary_box_overlap {L : ℕ} {z : Site 2} (hz : (z : Site 2) ∈ box 2 L) :
    (0 : Site 2) ∈ bc61_boxAround 2 L 0 ∧ z ∈ bc61_boxAround 2 L 0 ∧ z ∈ bc61_boxAround 2 L z := by
  refine ⟨bc105_centre_mem_own_box L 0, ?_, ?_⟩
  · rw [bc61_mem_boxAround]; simpa using hz
  · exact bc105_centre_mem_own_box L z
































theorem bc105_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) →
      bc103_ContractedTrifGraph ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) →
      bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (L : ℕ) (y z : Site d), (y - z) ∈ box d L →
      z ∈ bc61_boxAround d L y ∧ z ∈ bc61_boxAround d L z) ∧
    
    (∀ {L : ℕ}, 3 ≤ L → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno
    exact bc105_contractedTrifGraph_of_noTrif ω L R hz₀ hz₁ hzne hno
  · intro ω L R z₀ z₁ hz₀ hz₁ hzne hno
    exact bc105_count_of_noTrif ω L R hz₀ hz₁ hzne hno
  · intro L y z hyz
    exact bc105_boxes_overlap_of_close_centres hyz
  · intro L hL
    exact bc105_adversary_has_trif hL

end StatMech.Walls
