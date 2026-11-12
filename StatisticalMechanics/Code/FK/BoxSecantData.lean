/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.Lattice.BoundaryConditions
import Code.Lattice.HypercubicLattice
import Code.FK.InfiniteVolume

open Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice














noncomputable def boxSecantSurface (d n : ℕ) : ℝ := (2 * d) * (2 * n + 1) ^ (d - 1)




noncomputable def boxSecantVolume (d n : ℕ) : ℝ := (d : ℝ) * (2 * n + 1) ^ d


theorem boxSecantVolume_pos {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : 0 < boxSecantVolume d n := by
  unfold boxSecantVolume
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity




theorem boxSecantSurface_div_volume_eq {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    boxSecantSurface d n / boxSecantVolume d n = 2 / (2 * n + 1) := by
  unfold boxSecantSurface boxSecantVolume
  have hbase : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show ((2 * n + 1) ^ d : ℝ) = (2 * n + 1) ^ (d - 1) * (2 * n + 1) by
        rw [← pow_succ]; congr 1; omega]
  field_simp


theorem boxSecant_two_div_tendsto_zero :
    Tendsto (fun n : ℕ => (2 : ℝ) / (2 * n + 1)) atTop (𝓝 0) := by
  apply Tendsto.div_atTop tendsto_const_nhds
  apply Tendsto.atTop_add
  · exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  · exact tendsto_const_nhds



theorem boxSecantSurface_div_volume_tendsto_zero {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun n => boxSecantSurface d n / boxSecantVolume d n) atTop (𝓝 0) := by
  refine boxSecant_two_div_tendsto_zero.congr (fun n => ?_)
  exact (boxSecantSurface_div_volume_eq hd n).symm


theorem boxSecantVolume_tendsto_atTop {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun n => boxSecantVolume d n) atTop atTop := by
  unfold boxSecantVolume
  apply Tendsto.const_mul_atTop (by exact_mod_cast hd : (0 : ℝ) < d)
  refine tendsto_atTop_mono (f := fun n : ℕ => ((n : ℝ) + 1)) (fun n => ?_) ?_
  · calc ((n : ℝ) + 1) ≤ 2 * (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      _ = (2 * (n : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * (n : ℝ) + 1) ^ d :=
          pow_le_pow_right₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) hd
  · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop






theorem boxSecant_surface_volume_asymptotics {d : ℕ} (hd : 1 ≤ d) :
    (∀ n, 0 < boxSecantVolume d n)
      ∧ Tendsto (fun n => boxSecantSurface d n / boxSecantVolume d n) atTop (𝓝 0)
      ∧ Tendsto (fun n => boxSecantVolume d n) atTop atTop :=
  ⟨boxSecantVolume_pos hd, boxSecantSurface_div_volume_tendsto_zero hd,
    boxSecantVolume_tendsto_atTop hd⟩




























theorem connectedComponent_card_le_add_of_sup {V : Type*} [Fintype V]
    {G K : SimpleGraph V} {p : V → Prop} (hK : ∀ {x y}, K.Adj x y → p x ∧ p y) :
    Nat.card G.ConnectedComponent
      ≤ Nat.card (G ⊔ K).ConnectedComponent + Nat.card {v // p v} := by
  classical
  
  have core : ∀ {x y}, (∀ b, p b → ¬ G.Reachable x b) → (G ⊔ K).Walk x y →
      G.Reachable x y := by
    intro x y hx w
    induction w with
    | nil => exact Reachable.refl _
    | @cons u v t h pw ih =>
      rcases h with hg | hk
      · 
        have hxv : G.Reachable u v := hg.reachable
        exact hxv.trans (ih (fun b hb hr => hx b hb (hxv.trans hr)))
      · 
        exact absurd (Reachable.refl u) (hx u (hK hk).1)
  
  set f : G.ConnectedComponent → (G ⊔ K).ConnectedComponent ⊕ {v // p v} := fun a =>
    if h : ∃ v, p v ∧ G.connectedComponentMk v = a then
      Sum.inr ⟨h.choose, h.choose_spec.1⟩
    else
      Sum.inl (a.map (Hom.ofLE le_sup_left)) with hf
  have hinj : Function.Injective f := by
    intro a₁ a₂ heq
    simp only [hf] at heq
    by_cases h1 : ∃ v, p v ∧ G.connectedComponentMk v = a₁ <;>
      by_cases h2 : ∃ v, p v ∧ G.connectedComponentMk v = a₂
    · 
      rw [dif_pos h1, dif_pos h2] at heq
      have hc : h1.choose = h2.choose := congrArg Subtype.val (Sum.inr.inj heq)
      rw [← h1.choose_spec.2, ← h2.choose_spec.2, hc]
    · rw [dif_pos h1, dif_neg h2] at heq; exact absurd heq (by simp)
    · rw [dif_neg h1, dif_pos h2] at heq; exact absurd heq (by simp)
    · 
      rw [dif_neg h1, dif_neg h2] at heq
      have hmap := Sum.inl.inj heq
      obtain ⟨x₁, rfl⟩ := a₁.exists_rep
      obtain ⟨x₂, rfl⟩ := a₂.exists_rep
      have hx1 : ∀ b, p b → ¬ G.Reachable x₁ b := fun b hb hr =>
        h1 ⟨b, hb, ConnectedComponent.eq.mpr hr.symm⟩
      have hreach : (G ⊔ K).Reachable x₁ x₂ := ConnectedComponent.eq.mp hmap
      exact ConnectedComponent.eq.mpr (hreach.elim (fun w => core hx1 w))
  calc Nat.card G.ConnectedComponent
      ≤ Nat.card ((G ⊔ K).ConnectedComponent ⊕ {v // p v}) :=
        Nat.card_le_card_of_injective f hinj
    _ = Nat.card (G ⊔ K).ConnectedComponent + Nat.card {v // p v} := Nat.card_sum



theorem natCard_boundary_eq {V : Type*} [Fintype V] [DecidableEq V] (bdry : V → Prop)
    [DecidablePred bdry] :
    Nat.card {v // bdry v} = (Finset.univ.filter bdry).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]










theorem numClustersFree_le_numClustersWired_add {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    (ω : ConfigSpace (Sym2 V)) :
    numClustersFree G ω
      ≤ numClustersWired G bdry ω + (Finset.univ.filter bdry).card := by
  have hK : ∀ {x y}, (boundaryCliqueGraph bdry).Adj x y → bdry x ∧ bdry y := by
    intro x y h
    rw [boundaryCliqueGraph_adj] at h
    exact ⟨h.2.1, h.2.2⟩
  have hbound := connectedComponent_card_le_add_of_sup
    (G := openGraph G ω) (K := boundaryCliqueGraph bdry) (p := bdry) hK
  
  
  rw [natCard_boundary_eq bdry] at hbound
  
  show numClustersFree G ω ≤ numClustersWired G bdry ω + (Finset.univ.filter bdry).card
  rw [show numClustersFree G ω = Nat.card (openGraph G ω).ConnectedComponent from rfl,
    show numClustersWired G bdry ω = Nat.card (wiredGraph G bdry ω).ConnectedComponent from rfl,
    show wiredGraph G bdry ω = openGraph G ω ⊔ boundaryCliqueGraph bdry from rfl]
  exact hbound







theorem numClusters_wired_sandwich {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    (ω : ConfigSpace (Sym2 V)) :
    numClustersWired G bdry ω ≤ numClustersFree G ω
      ∧ numClustersFree G ω
          ≤ numClustersWired G bdry ω + (Finset.univ.filter bdry).card :=
  ⟨numClustersWired_le_numClustersFree G bdry ω,
    numClustersFree_le_numClustersWired_add G bdry ω⟩












theorem box_numClusters_wired_sandwich (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    numClustersWired (boxGraph d n) (boxBoundary d n) ω ≤ numClustersFree (boxGraph d n) ω
      ∧ numClustersFree (boxGraph d n) ω
          ≤ numClustersWired (boxGraph d n) (boxBoundary d n) ω
              + (Finset.univ.filter (boxBoundary d n)).card :=
  numClusters_wired_sandwich (boxGraph d n) (boxBoundary d n) ω

end FK

end StatMech
