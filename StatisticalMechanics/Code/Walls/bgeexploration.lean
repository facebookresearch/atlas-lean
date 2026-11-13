/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.bfggenuinecarrier
import Code.Walls.bc64coarseembed

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}










theorem bge_cluster_disjoint_of_notConnected {ω' : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : ¬ Connected d ω' a b) : Disjoint (cluster d ω' a) (cluster d ω' b) := by
  rw [Set.disjoint_left]
  intro p hpa hpb
  rw [mem_cluster] at hpa hpb
  exact h (hpa.trans hpb.symm)













theorem bge_singleGenuineTrif_arms_disjoint {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y : Site d}
    {a₁ a₂ a₃ : Site d}
    (hsep : ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
            ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
            ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) :
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₂) ∧
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₃) ∧
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₂)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₃) :=
  ⟨bge_cluster_disjoint_of_notConnected hsep.1,
   bge_cluster_disjoint_of_notConnected hsep.2.1,
   bge_cluster_disjoint_of_notConnected hsep.2.2⟩

open Classical in








theorem bge_exploration_of_singleGenuineTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d)
    (hy : btr_IsGenuineCoarseTrif ω L y)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y)
    (hbdry : ∀ a : Site d,
      (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) →
      Connected d ω y a →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) :
    bfg_GenuineExploration ω L R := by
  classical
  obtain ⟨a₁, a₂, a₃, ⟨b₁, hb1m, hb1a⟩, ⟨b₂, hb2m, hb2a⟩, ⟨b₃, hb3m, hb3a⟩,
    ⟨hcy1, hcy2, hcy3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := hy
  set ω' := removeSites (bc61_boxAround d L y) ω with hω'
  
  set C₁ := cluster d ω' a₁ with hC1
  set C₂ := cluster d ω' a₂ with hC2
  set C₃ := cluster d ω' a₃ with hC3
  obtain ⟨hd12, hd13, hd23⟩ := bge_singleGenuineTrif_arms_disjoint (ω := ω) (L := L) (y := y) hsep
  refine ⟨Fin 4, inferInstance, inferInstance, inferInstance, bc64_starG, inferInstance,
    (fun _ => (0 : Fin 4)),
    (fun v => if v = 1 then C₁ else if v = 2 then C₂ else if v = 3 then C₃ else (∅ : Set (Site d))),
    bc64_starG_isTree.isAcyclic, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro v; fin_cases v <;> decide
  · 
    intro z _ _; exact bc64_starG_centre_deg.ge
  · 
    intro z hzbox hzgen z' hz'box hz'gen _
    rw [huniq z hzbox hzgen, huniq z' hz'box hz'gen]
  · 
    intro v hv
    fin_cases v <;>
      first
        | exact absurd hv (by decide)
        | exact hbdry a₁ ⟨b₁, hb1m, hb1a⟩ hcy1 hi1
        | exact hbdry a₂ ⟨b₂, hb2m, hb2a⟩ hcy2 hi2
        | exact hbdry a₃ ⟨b₃, hb3m, hb3a⟩ hcy3 hi3
  · 
    intro u hu v hv huv
    fin_cases u <;> fin_cases v <;>
      first
        | exact absurd hu (by decide)
        | exact absurd hv (by decide)
        | exact absurd rfl huv
        | exact hd12
        | exact hd12.symm
        | exact hd13
        | exact hd13.symm
        | exact hd23
        | exact hd23.symm


















def bge_ArmComponents (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ comp : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4 → Set (Site d),
    (∀ p : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4, p.2 ≠ 0 →
      (comp p ∩ vertexBoundary d R).Nonempty) ∧
    (∀ p : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4, p.2 ≠ 0 →
      ∀ q : (↑(btr_genuineTrifFinset ω L R) : Type) × Fin 4, q.2 ≠ 0 → p ≠ q →
      Disjoint (comp p) (comp q))

open Classical in







theorem bge_exploration_of_armComponents (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (h : bge_ArmComponents ω L R) :
    bfg_GenuineExploration ω L R := by
  classical
  set Tf := btr_genuineTrifFinset ω L R with hTf
  rcases Finset.eq_empty_or_nonempty Tf with hemp | hne
  · 
    apply bfg_exploration_of_noTrif ω L R hz₀ hz₁ hzne
    intro y hybox hgen
    have : y ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hybox, hgen⟩
    rw [hemp] at this; exact absurd this (Finset.notMem_empty y)
  · 
    obtain ⟨comp, hcompB, hcompD⟩ := h
    have hTfne : Nonempty (↑Tf : Type) := hne.to_subtype
    obtain ⟨t0, ht0⟩ := hne
    let W := (↑Tf : Type) × Fin 4
    let ιT : Site d → W := fun y => if hy : y ∈ Tf then (⟨y, hy⟩, 0) else (⟨t0, ht0⟩, 0)
    refine ⟨W, inferInstance, ⟨(⟨t0, ht0⟩, 0)⟩, inferInstance, bc64_starForest (↑Tf : Type),
      inferInstance, ιT, comp, bc64_starForest_acyclic _, ?_, ?_, ?_, ?_, ?_⟩
    · 
      intro v; obtain ⟨t, i⟩ := v; exact bc64_starForest_min_degree (t, i)
    · 
      intro y hybox hgen
      have hy : y ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hybox, hgen⟩
      have hιT : ιT y = (⟨y, hy⟩, (0 : Fin 4)) := dif_pos hy
      rw [hιT, bc64_starForest_degree, bc64_starG_centre_deg]
    · 
      intro y hybox hgen z hzbox hgenz hyz
      have hy : y ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hybox, hgen⟩
      have hz : z ∈ Tf := by rw [hTf, bgt_mem_genuineTrifFinset]; exact ⟨hzbox, hgenz⟩
      simp only [ιT, dif_pos hy, dif_pos hz] at hyz
      exact Subtype.ext_iff.mp (Prod.ext_iff.mp hyz).1
    · 
      intro v hv; obtain ⟨t, i⟩ := v
      rw [bc64_starForest_deg1_iff] at hv
      exact hcompB (t, i) hv
    · 
      intro u hu v hv huv
      obtain ⟨t1, i1⟩ := u; obtain ⟨t2, i2⟩ := v
      rw [bc64_starForest_deg1_iff] at hu hv
      exact hcompD (t1, i1) hu (t2, i2) hv huv





theorem bge_exploration_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁) (hno : ∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) :
    bfg_GenuineExploration ω L R :=
  bfg_exploration_of_noTrif ω L R hz₀ hz₁ hzne hno



theorem bge_bc60_exploration (L R : ℕ)
    {z₀ z₁ : Site 2} (hz₀ : z₀ ∈ vertexBoundary 2 R) (hz₁ : z₁ ∈ vertexBoundary 2 R)
    (hzne : z₀ ≠ z₁) :
    bfg_GenuineExploration bc60_upperLines L R :=
  bfg_bc60_exploration L R hz₀ hz₁ hzne






























theorem bge_status :
    
    (∀ {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y a₁ a₂ a₃ : Site d},
      (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
       ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) →
      Disjoint (cluster d (removeSites (bc61_boxAround d L y) ω) a₁)
        (cluster d (removeSites (bc61_boxAround d L y) ω) a₂)) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d),
      btr_IsGenuineCoarseTrif ω L y →
      (∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y) →
      (∀ a : Site d,
        (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) →
        Connected d ω y a →
        (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
        (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) →
      bfg_GenuineExploration ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      bge_ArmComponents ω L R → bfg_GenuineExploration ω L R) := by
  refine ⟨fun hsep => bge_cluster_disjoint_of_notConnected hsep.1,
    fun ω L R y hy huniq hbdry => bge_exploration_of_singleGenuineTrif ω L R y hy huniq hbdry,
    ?_⟩
  intro ω L R z₀ z₁ hz₀ hz₁ hzne h
  exact bge_exploration_of_armComponents ω L R hz₀ hz₁ hzne h

end StatMech.Walls
