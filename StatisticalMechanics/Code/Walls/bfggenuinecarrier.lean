/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Walls.bgtgenuineforest

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









open Classical in



noncomputable def bfg_leafSel {W : Type*} (comp : W → Set (Site d)) (R : ℕ) (v : W) : Site d :=
  if h : (comp v ∩ vertexBoundary d R).Nonempty then h.choose else default


theorem bfg_leafSel_mem {W : Type*} (comp : W → Set (Site d)) (R : ℕ) {v : W}
    (h : (comp v ∩ vertexBoundary d R).Nonempty) :
    bfg_leafSel comp R v ∈ comp v ∩ vertexBoundary d R := by
  classical
  rw [bfg_leafSel, dif_pos h]; exact h.choose_spec







theorem bfg_leafSel_injOn {W : Type*} {S : Set W} (comp : W → Set (Site d)) (R : ℕ)
    (hne : ∀ v ∈ S, (comp v ∩ vertexBoundary d R).Nonempty)
    (hdisj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (comp u) (comp v)) :
    Set.InjOn (bfg_leafSel comp R) S := by
  classical
  intro u hu v hv huv
  by_contra hne'
  have hmu : bfg_leafSel comp R u ∈ comp u := (bfg_leafSel_mem comp R (hne u hu)).1
  have hmv : bfg_leafSel comp R v ∈ comp v := (bfg_leafSel_mem comp R (hne v hv)).1
  rw [huv] at hmu
  exact Set.disjoint_left.mp (hdisj u hu v hv hne') hmu hmv
















def bfg_GenuineExploration (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : Nonempty W) (_ : DecidableEq W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj) (ιT : Site d → W) (comp : W → Set (Site d)),
    G.IsAcyclic ∧ (∀ v, 1 ≤ G.degree v) ∧
    (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → 3 ≤ G.degree (ιT y)) ∧
    (∀ y, y ∈ box d R → btr_IsGenuineCoarseTrif ω L y → ∀ z, z ∈ box d R →
      btr_IsGenuineCoarseTrif ω L z → ιT y = ιT z → y = z) ∧
    (∀ v, G.degree v = 1 → (comp v ∩ vertexBoundary d R).Nonempty) ∧
    (∀ u, G.degree u = 1 → ∀ v, G.degree v = 1 → u ≠ v → Disjoint (comp u) (comp v))







theorem bfg_genuineForest_of_exploration (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bfg_GenuineExploration ω L R) :
    bgt_GenuineForest ω L R := by
  classical
  obtain ⟨W, hWf, hWne, hWde, G, hGdr, ιT, comp, hacyc, hmin, hdeg3, hιinj, hbnd, hdisj⟩ := h
  refine ⟨W, hWf, hWne, hWde, G, hGdr, ιT, bfg_leafSel comp R,
    hacyc, hmin, hdeg3, hιinj, ?_, ?_⟩
  · intro v hv; exact (bfg_leafSel_mem comp R (hbnd v hv)).2
  · apply bfg_leafSel_injOn comp R
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      exact hbnd v hv.2
    · intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_filter] at hu hv
      exact hdisj u hu.2 v hv.2 huv




theorem bfg_genuineTcount_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bfg_GenuineExploration ω L R) :
    (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R :=
  bgt_genuineTcount_le_boundary ω L R (bfg_genuineForest_of_exploration ω L R h)








open Classical in



theorem bfg_exploration_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R)
    (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) :
    bfg_GenuineExploration ω L R := by
  classical
  refine ⟨Fin 2, inferInstance, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun _ => (0 : Fin 2)), (fun v => if v = 0 then ({z₀} : Set (Site d)) else {z₁}),
    Flc2Witness.pathG_isTree.isAcyclic, (fun v => (Flc2Witness.pathG_deg v).ge), ?_, ?_, ?_, ?_⟩
  · intro y hybox hgen; exact absurd hgen (hno y hybox)
  · intro y hybox hgen; exact absurd hgen (hno y hybox)
  · intro v _
    fin_cases v
    · exact ⟨z₀, by simp, by simpa using hz₀⟩
    · exact ⟨z₁, by simp, by simpa using hz₁⟩
  · intro u _ v _ huv
    fin_cases u <;> fin_cases v
    · exact absurd rfl huv
    · simpa [Set.disjoint_singleton] using hzne
    · simpa [Set.disjoint_singleton] using hzne.symm
    · exact absurd rfl huv





theorem bfg_bc60_exploration (L R : ℕ)
    {z₀ z₁ : Site 2} (hz₀ : z₀ ∈ vertexBoundary 2 R) (hz₁ : z₁ ∈ vertexBoundary 2 R)
    (hzne : z₀ ≠ z₁) :
    bfg_GenuineExploration bc60_upperLines L R :=
  bfg_exploration_of_noTrif bc60_upperLines L R hz₀ hz₁ hzne
    (fun y _ => btr_bc60_not_genuineTrif L y)





theorem bfg_bc60_genuineForest (L R : ℕ)
    {z₀ z₁ : Site 2} (hz₀ : z₀ ∈ vertexBoundary 2 R) (hz₁ : z₁ ∈ vertexBoundary 2 R)
    (hzne : z₀ ≠ z₁) :
    bgt_GenuineForest bc60_upperLines L R :=
  bfg_genuineForest_of_exploration bc60_upperLines L R (bfg_bc60_exploration L R hz₀ hz₁ hzne)

































theorem bfg_status :
    
    (∀ {W : Type} {S : Set W} (comp : W → Set (Site d)) (R : ℕ),
      (∀ v ∈ S, (comp v ∩ vertexBoundary d R).Nonempty) →
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → Disjoint (comp u) (comp v)) →
      Set.InjOn (bfg_leafSel comp R) S) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bfg_GenuineExploration ω L R → bgt_GenuineForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bfg_GenuineExploration ω L R →
      (btr_genuineTrifFinset ω L R).card ≤ boxSV_boundaryCard d R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d),
      z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ →
      (∀ y, y ∈ box d R → ¬ btr_IsGenuineCoarseTrif ω L y) →
      bfg_GenuineExploration ω L R) := by
  refine ⟨fun comp R hne hdisj => bfg_leafSel_injOn comp R hne hdisj,
    fun ω L R h => bfg_genuineForest_of_exploration ω L R h,
    fun ω L R h => bfg_genuineTcount_le_boundary ω L R h, ?_⟩
  intro ω L R z₀ z₁ hz₀ hz₁ hzne hno
  exact bfg_exploration_of_noTrif ω L R hz₀ hz₁ hzne hno

end StatMech.Walls
