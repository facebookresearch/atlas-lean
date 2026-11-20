/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Walls.bxpxpos
import Code.Inequalities.DisjointOccurrence
import Code.Inequalities.ReimerCompression

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000







def bpt2_closeI (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ I then false else ω e


theorem bpt2_closeI_le (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) :
    bpt2_closeI I ω ≤ ω := by
  intro e; unfold bpt2_closeI; by_cases h : e ∈ I <;> simp [h]


theorem bpt2_removeSite_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (z : Site 2) : removeSite z ω ≤ removeSite z ω' := by
  intro e
  by_cases hz : z ∈ e
  · simp [removeSite, hz]
  · simp only [removeSite, hz, if_false]; exact h e



theorem bpt2_closeI_forceOpen (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) :
    bpt2_closeI I (forceOpenFinset I ω) = bpt2_closeI I ω := by
  funext e
  unfold bpt2_closeI
  by_cases h : e ∈ I
  · simp [h]
  · simp [h]











theorem bpt2_openEdge_data (ω : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (h : IsOpenEdge 2 (removeSite 0 ω) u v) :
    (0 : Site 2) ∉ s(u, v) ∧ (hypercubicLattice 2).Adj u v ∧ ω s(u, v) = true := by
  obtain ⟨hadj, hval⟩ := h
  by_cases h0 : (0 : Site 2) ∈ s(u, v)
  · rw [removeSite_apply_of_mem h0] at hval; exact absurd hval (by simp)
  · rw [removeSite_apply_of_notMem h0] at hval; exact ⟨h0, hadj, hval⟩



theorem bpt2_closed_combined (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2)))
    {S : Set (Site 2)}
    (hIresp : ∀ u v : Site 2, s(u, v) ∈ I → u ∈ S → v ∈ S)
    (hSclosed : ∀ u v : Site 2, u ∈ S →
      IsOpenEdge 2 (removeSite 0 (bpt2_closeI I ω)) u v → v ∈ S) :
    ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 (removeSite 0 ω) x y → y ∈ S := by
  intro x y hx hop
  obtain ⟨h0, hadj, hval⟩ := bpt2_openEdge_data ω hop
  by_cases hI : s(x, y) ∈ I
  · exact hIresp x y hI hx
  · refine hSclosed x y hx ⟨hadj, ?_⟩
    rw [removeSite_apply_of_notMem h0]
    unfold bpt2_closeI
    rw [if_neg hI]; exact hval


theorem bpt2_walk_invariant (ω : ConfigSpace (Sym2 (Site 2))) {S : Set (Site 2)}
    (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 (removeSite 0 ω) x y → y ∈ S)
    {x y : Site 2} (w : (openSubgraph 2 (removeSite 0 ω)).Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih => exact ih (hclosed a b hx hab)




theorem bpt2_cluster_confined (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2)))
    {a : Site 2} {S : Set (Site 2)} (ha : a ∈ S)
    (hIresp : ∀ u v : Site 2, s(u, v) ∈ I → u ∈ S → v ∈ S)
    (hSclosed : ∀ u v : Site 2, u ∈ S →
      IsOpenEdge 2 (removeSite 0 (bpt2_closeI I ω)) u v → v ∈ S) :
    cluster 2 (removeSite 0 ω) a ⊆ S := by
  intro y hy
  obtain ⟨w⟩ := (hy : (openSubgraph 2 (removeSite 0 ω)).Reachable a y)
  exact bpt2_walk_invariant ω (bpt2_closed_combined I ω hIresp hSclosed) w ha








def bpt2_ExtPred (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2)
    (ρ : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∃ S₁ S₂ S₃ : Set (Site 2),
    (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧
    (x₁ ∈ S₁ ∧ x₂ ∈ S₂ ∧ x₃ ∈ S₃) ∧
    (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) ∧
    ((∀ u v : Site 2, s(u, v) ∈ I → u ∈ S₁ → v ∈ S₁) ∧
      (∀ u v : Site 2, s(u, v) ∈ I → u ∈ S₂ → v ∈ S₂) ∧
      (∀ u v : Site 2, s(u, v) ∈ I → u ∈ S₃ → v ∈ S₃)) ∧
    ((∀ u v : Site 2, u ∈ S₁ → IsOpenEdge 2 ρ u v → v ∈ S₁) ∧
      (∀ u v : Site 2, u ∈ S₂ → IsOpenEdge 2 ρ u v → v ∈ S₂) ∧
      (∀ u v : Site 2, u ∈ S₃ → IsOpenEdge 2 ρ u v → v ∈ S₃)) ∧
    ((cluster 2 ρ x₁).Infinite ∧ (cluster 2 ρ x₂).Infinite ∧ (cluster 2 ρ x₃).Infinite)




def bpt2_Ext (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | bpt2_ExtPred I a₁ a₂ a₃ x₁ x₂ x₃ (removeSite 0 (bpt2_closeI I ω))}



theorem bpt2_removeSite_closeI_congr (I : Finset (Sym2 (Site 2)))
    {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (hag : agreeOn ((↑I : Set (Sym2 (Site 2)))ᶜ) ω ω') :
    removeSite 0 (bpt2_closeI I ω) = removeSite 0 (bpt2_closeI I ω') := by
  funext e
  by_cases h0 : (0 : Site 2) ∈ e
  · simp [removeSite, h0]
  · simp only [removeSite, h0, if_false]
    unfold bpt2_closeI
    by_cases hI : e ∈ I
    · simp [hI]
    · simp only [hI, if_false]
      exact (hag e (by simp only [Set.mem_compl_iff, Finset.mem_coe]; exact hI)).symm






theorem bpt2_Ext_dependsOn (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) :
    DependsOn (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) := by
  intro ω ω' hag
  change bpt2_ExtPred I a₁ a₂ a₃ x₁ x₂ x₃ (removeSite 0 (bpt2_closeI I ω))
      ↔ bpt2_ExtPred I a₁ a₂ a₃ x₁ x₂ x₃ (removeSite 0 (bpt2_closeI I ω'))
  rw [bpt2_removeSite_closeI_congr I hag]
















theorem bpt2_hgeo (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2)
    (η₀ : ConfigSpace ↥I)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
      Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃) :
    cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃
      ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
  rintro ω ⟨hcyl, S₁, S₂, S₃, ⟨ha1, ha2, ha3⟩, ⟨hx1, hx2, hx3⟩, ⟨hd12, hd13, hd23⟩,
    ⟨hIr1, hIr2, hIr3⟩, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩⟩
  obtain ⟨conn1, conn2, conn3⟩ := hcorr ω hcyl
  have hsub1 : cluster 2 (removeSite 0 ω) a₁ ⊆ S₁ := bpt2_cluster_confined I ω ha1 hIr1 hc1
  have hsub2 : cluster 2 (removeSite 0 ω) a₂ ⊆ S₂ := bpt2_cluster_confined I ω ha2 hIr2 hc2
  have hsub3 : cluster 2 (removeSite 0 ω) a₃ ⊆ S₃ := bpt2_cluster_confined I ω ha3 hIr3 hc3
  have hle : removeSite 0 (bpt2_closeI I ω) ≤ removeSite 0 ω :=
    bpt2_removeSite_mono (bpt2_closeI_le I ω) 0
  refine ⟨hne, hadj, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [cluster_eq_of_connected conn1]; exact hi1.mono (cluster_mono hle x₁)
    · rw [cluster_eq_of_connected conn2]; exact hi2.mono (cluster_mono hle x₂)
    · rw [cluster_eq_of_connected conn3]; exact hi3.mono (cluster_mono hle x₃)
  · refine ⟨?_, ?_, ?_⟩
    · intro hconn; exact (Set.disjoint_left.mp hd12) (hsub1 (mem_cluster.mpr hconn)) ha2
    · intro hconn; exact (Set.disjoint_left.mp hd13) (hsub1 (mem_cluster.mpr hconn)) ha3
    · intro hconn; exact (Set.disjoint_left.mp hd23) (hsub2 (mem_cluster.mpr hconn)) ha3








theorem bpt2_precursorPos_of_residues
    (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (I : Finset (Sym2 (Site 2))) (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (η₀ : ConfigSpace ↥I)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧
      (hypercubicLattice 2).Adj 0 a₃)
    (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)),
      Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧
        Connected 2 (removeSite 0 ω) a₃ x₃)
    (hindep : bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)
        = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (cylinder I ({η₀} : Set (ConfigSpace ↥I)))
          * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
              (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃))
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (NeighborTrifPrecursor 2 a₁ a₂ a₃) :=
  bdec_precursorPos_of_decoupled p hp1 hp0 hplt a₁ a₂ a₃ I η₀
    (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) hindep hXpos
    (bpt2_hgeo I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr)












def bpt2_S₁ : Set (Site 2) := {v | v 1 = 0 ∧ 1 ≤ v 0}

def bpt2_S₂ : Set (Site 2) := {v | v 0 = 0 ∧ 1 ≤ v 1}

def bpt2_S₃ : Set (Site 2) := {v | v 1 = 0 ∧ v 0 ≤ -1}



theorem bpt2_a₁_mem_S₁ : bmf_a₁ ∈ bpt2_S₁ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_a₁]
theorem bpt2_x₁_mem_S₁ : bmf_b₁ ∈ bpt2_S₁ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_b₁]
theorem bpt2_a₂_mem_S₂ : bmf_a₂ ∈ bpt2_S₂ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_a₂]
theorem bpt2_x₂_mem_S₂ : bmf_b₂ ∈ bpt2_S₂ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_b₂]
theorem bpt2_a₃_mem_S₃ : bmf_a₃ ∈ bpt2_S₃ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_a₃]
theorem bpt2_x₃_mem_S₃ : bmf_b₃ ∈ bpt2_S₃ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_b₃]



theorem bpt2_R₁_subset_S₁ {v : Site 2} (h : v ∈ bmf_R₁) : v ∈ bpt2_S₁ :=
  ⟨h.1, by have := h.2; omega⟩
theorem bpt2_R₂_subset_S₂ {v : Site 2} (h : v ∈ bmf_R₂) : v ∈ bpt2_S₂ :=
  ⟨h.1, by have := h.2; omega⟩
theorem bpt2_R₃_subset_S₃ {v : Site 2} (h : v ∈ bmf_R₃) : v ∈ bpt2_S₃ :=
  ⟨h.1, by have := h.2; omega⟩

theorem bpt2_S₁_notMem_S₂ {v : Site 2} (h : v ∈ bpt2_S₁) : v ∉ bpt2_S₂ := by
  rintro ⟨h0, _⟩; have := h.2; rw [h0] at this; omega
theorem bpt2_S₁_notMem_S₃ {v : Site 2} (h : v ∈ bpt2_S₁) : v ∉ bpt2_S₃ := by
  rintro ⟨_, h0⟩; have := h.2; omega
theorem bpt2_S₂_notMem_S₁ {v : Site 2} (h : v ∈ bpt2_S₂) : v ∉ bpt2_S₁ := by
  rintro ⟨_, h1⟩; have := h.1; rw [h.1] at h1; omega
theorem bpt2_S₂_notMem_S₃ {v : Site 2} (h : v ∈ bpt2_S₂) : v ∉ bpt2_S₃ := by
  rintro ⟨h0, _⟩; have := h.2; rw [h0] at this; omega
theorem bpt2_S₃_notMem_S₁ {v : Site 2} (h : v ∈ bpt2_S₃) : v ∉ bpt2_S₁ := by
  rintro ⟨_, h1⟩; have := h.2; omega
theorem bpt2_S₃_notMem_S₂ {v : Site 2} (h : v ∈ bpt2_S₃) : v ∉ bpt2_S₂ := by
  rintro ⟨h0, _⟩; have := h.2; rw [h0] at this; omega

theorem bpt2_disjoint_S₁_S₂ : Disjoint bpt2_S₁ bpt2_S₂ :=
  Set.disjoint_left.mpr fun _ ha hb => bpt2_S₁_notMem_S₂ ha hb
theorem bpt2_disjoint_S₁_S₃ : Disjoint bpt2_S₁ bpt2_S₃ :=
  Set.disjoint_left.mpr fun _ ha hb => bpt2_S₁_notMem_S₃ ha hb
theorem bpt2_disjoint_S₂_S₃ : Disjoint bpt2_S₂ bpt2_S₃ :=
  Set.disjoint_left.mpr fun _ ha hb => bpt2_S₂_notMem_S₃ ha hb



theorem bpt2_a₂_notMem_S₁ : bmf_a₂ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
theorem bpt2_b₂_notMem_S₁ : bmf_b₂ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₂] at h0 h1
theorem bpt2_a₃_notMem_S₁ : bmf_a₃ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1
theorem bpt2_b₃_notMem_S₁ : bmf_b₃ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₃] at h0 h1

theorem bpt2_a₁_notMem_S₂ : bmf_a₁ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
theorem bpt2_b₁_notMem_S₂ : bmf_b₁ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₁] at h0 h1
theorem bpt2_a₃_notMem_S₂ : bmf_a₃ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1
theorem bpt2_b₃_notMem_S₂ : bmf_b₃ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₃] at h0 h1

theorem bpt2_a₁_notMem_S₃ : bmf_a₁ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
theorem bpt2_b₁_notMem_S₃ : bmf_b₁ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₁] at h0 h1
theorem bpt2_a₂_notMem_S₃ : bmf_a₂ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
theorem bpt2_b₂_notMem_S₃ : bmf_b₂ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₂] at h0 h1





theorem bpt2_I_respects_S₁ (u v : Site 2) (hmem : s(u, v) ∈ bmf_I) (hu : u ∈ bpt2_S₁) :
    v ∈ bpt2_S₁ := by
  simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ <;>
    subst hu' <;> subst hv'
  · exact bpt2_x₁_mem_S₁
  · exact bpt2_a₁_mem_S₁
  · exact absurd hu bpt2_a₂_notMem_S₁
  · exact absurd hu bpt2_b₂_notMem_S₁
  · exact absurd hu bpt2_a₃_notMem_S₁
  · exact absurd hu bpt2_b₃_notMem_S₁

theorem bpt2_I_respects_S₂ (u v : Site 2) (hmem : s(u, v) ∈ bmf_I) (hu : u ∈ bpt2_S₂) :
    v ∈ bpt2_S₂ := by
  simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ <;>
    subst hu' <;> subst hv'
  · exact absurd hu bpt2_a₁_notMem_S₂
  · exact absurd hu bpt2_b₁_notMem_S₂
  · exact bpt2_x₂_mem_S₂
  · exact bpt2_a₂_mem_S₂
  · exact absurd hu bpt2_a₃_notMem_S₂
  · exact absurd hu bpt2_b₃_notMem_S₂

theorem bpt2_I_respects_S₃ (u v : Site 2) (hmem : s(u, v) ∈ bmf_I) (hu : u ∈ bpt2_S₃) :
    v ∈ bpt2_S₃ := by
  simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ <;>
    subst hu' <;> subst hv'
  · exact absurd hu bpt2_a₁_notMem_S₃
  · exact absurd hu bpt2_b₁_notMem_S₃
  · exact absurd hu bpt2_a₂_notMem_S₃
  · exact absurd hu bpt2_b₂_notMem_S₃
  · exact bpt2_x₃_mem_S₃
  · exact bpt2_a₃_mem_S₃




theorem bpt2_a₁_notMem_rays :
    bmf_a₁ ∉ bmf_R₁ ∧ bmf_a₁ ∉ bmf_R₂ ∧ bmf_a₁ ∉ bmf_R₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
theorem bpt2_a₂_notMem_rays :
    bmf_a₂ ∉ bmf_R₁ ∧ bmf_a₂ ∉ bmf_R₂ ∧ bmf_a₂ ∉ bmf_R₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
theorem bpt2_a₃_notMem_rays :
    bmf_a₃ ∉ bmf_R₁ ∧ bmf_a₃ ∉ bmf_R₂ ∧ bmf_a₃ ∉ bmf_R₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1


theorem bpt2_notOnRay_of_endpoint {e : Sym2 (Site 2)} {a : Site 2} (hae : a ∈ e)
    (hR : a ∉ bmf_R₁ ∧ a ∉ bmf_R₂ ∧ a ∉ bmf_R₃) : ¬ bmf_OnRay e := by
  rintro ⟨x, y, heq, hcases⟩
  subst heq
  rw [Sym2.mem_iff] at hae
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hae with rfl | rfl
  · exact hR.1 h1
  · exact hR.1 h2
  · exact hR.2.1 h1
  · exact hR.2.1 h2
  · exact hR.2.2 h1
  · exact hR.2.2 h2



theorem bpt2_closeI_omegaTri : bpt2_closeI bmf_I bmf_omegaTri = bmf_omegaTri := by
  funext e
  unfold bpt2_closeI
  by_cases h : e ∈ bmf_I
  · rw [if_pos h]
    symm
    rw [← Bool.not_eq_true, bmf_omegaTri_true]
    simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact bpt2_notOnRay_of_endpoint (by simp) bpt2_a₁_notMem_rays
    · exact bpt2_notOnRay_of_endpoint (by simp) bpt2_a₂_notMem_rays
    · exact bpt2_notOnRay_of_endpoint (by simp) bpt2_a₃_notMem_rays
  · rw [if_neg h]



theorem bpt2_S₁_closed (u v : Site 2) (hu : u ∈ bpt2_S₁)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) : v ∈ bpt2_S₁ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(u, v) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨_, hy'⟩ | ⟨hx', _⟩ | ⟨hx', _⟩
    · exact bpt2_R₁_subset_S₁ hy'
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₁_notMem_S₂ hu)
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₁_notMem_S₃ hu)
  · subst hxy; subst hyx
    rcases hcases with ⟨hy', _⟩ | ⟨_, hx'⟩ | ⟨_, hx'⟩
    · exact bpt2_R₁_subset_S₁ hy'
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₁_notMem_S₂ hu)
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₁_notMem_S₃ hu)

theorem bpt2_S₂_closed (u v : Site 2) (hu : u ∈ bpt2_S₂)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) : v ∈ bpt2_S₂ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(u, v) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨_, hy'⟩ | ⟨hx', _⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₂_notMem_S₁ hu)
    · exact bpt2_R₂_subset_S₂ hy'
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₂_notMem_S₃ hu)
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨hy', _⟩ | ⟨_, hx'⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₂_notMem_S₁ hu)
    · exact bpt2_R₂_subset_S₂ hy'
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₂_notMem_S₃ hu)

theorem bpt2_S₃_closed (u v : Site 2) (hu : u ∈ bpt2_S₃)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) : v ∈ bpt2_S₃ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(u, v) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨hx', _⟩ | ⟨_, hy'⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₃_notMem_S₁ hu)
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₃_notMem_S₂ hu)
    · exact bpt2_R₃_subset_S₃ hy'
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨_, hx'⟩ | ⟨hy', _⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₃_notMem_S₁ hu)
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₃_notMem_S₂ hu)
    · exact bpt2_R₃_subset_S₃ hy'




noncomputable def bpt2_omega : ConfigSpace (Sym2 (Site 2)) :=
  forceOpenFinset bmf_I bmf_omegaTri



theorem bpt2_removeSite_closeI_omega :
    removeSite 0 (bpt2_closeI bmf_I bpt2_omega) = removeSite 0 bmf_omegaTri := by
  unfold bpt2_omega
  rw [bpt2_closeI_forceOpen, bpt2_closeI_omegaTri]


theorem bpt2_omega_mem_cylinder :
    bpt2_omega ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) := by
  rw [MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
  funext e
  simp only [Finset.restrict, bpt2_omega, bmf_η₀, forceOpenFinset_of_mem e.2]



theorem bpt2_omega_mem_Ext :
    bpt2_omega ∈ bpt2_Ext bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃ := by
  change bpt2_ExtPred bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃
    (removeSite 0 (bpt2_closeI bmf_I bpt2_omega))
  rw [bpt2_removeSite_closeI_omega]
  refine ⟨bpt2_S₁, bpt2_S₂, bpt2_S₃,
    ⟨bpt2_a₁_mem_S₁, bpt2_a₂_mem_S₂, bpt2_a₃_mem_S₃⟩,
    ⟨bpt2_x₁_mem_S₁, bpt2_x₂_mem_S₂, bpt2_x₃_mem_S₃⟩,
    ⟨bpt2_disjoint_S₁_S₂, bpt2_disjoint_S₁_S₃, bpt2_disjoint_S₂_S₃⟩,
    ⟨bpt2_I_respects_S₁, bpt2_I_respects_S₂, bpt2_I_respects_S₃⟩,
    ⟨bpt2_S₁_closed, bpt2_S₂_closed, bpt2_S₃_closed⟩,
    ⟨bmf_b₁_cluster_infinite, bmf_b₂_cluster_infinite, bmf_b₃_cluster_infinite⟩⟩






theorem bpt2_omega_mem_precursor :
    bpt2_omega ∈ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ :=
  bpt2_hgeo bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃ bmf_η₀
    ⟨bmf_a₁_ne_a₂, bmf_a₁_ne_a₃, bmf_a₂_ne_a₃⟩
    ⟨bmf_adj_o_a₁, bmf_adj_o_a₂, bmf_adj_o_a₃⟩
    (fun ω hω => ⟨bmf_conn_a₁_b₁ ω hω, bmf_conn_a₂_b₂ ω hω, bmf_conn_a₃_b₃ ω hω⟩)
    ⟨bpt2_omega_mem_cylinder, bpt2_omega_mem_Ext⟩


theorem bpt2_Ext_nonempty :
    (bpt2_Ext bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃).Nonempty :=
  ⟨bpt2_omega, bpt2_omega_mem_Ext⟩

end StatMech.Walls
