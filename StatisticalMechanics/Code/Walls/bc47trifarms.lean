/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.ArmReachComponentClose
import Code.Walls.bc46funnelproof

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


















def bc47_x : Site 2 := ![0, 0]


def bc47_a1 : Site 2 := ![0, 1]


def bc47_a2 : Site 2 := ![0, -1]


def bc47_a3 : Site 2 := ![-1, 0]


def bc47_R (k : ℤ) : Site 2 := ![k, 0]

theorem bc47_R_inj : Function.Injective bc47_R := by
  intro a b h
  have : (bc47_R a) 0 = (bc47_R b) 0 := by rw [h]
  simpa [bc47_R] using this

theorem bc47_x_eq_R0 : bc47_x = bc47_R 0 := by
  funext i; fin_cases i <;> simp [bc47_x, bc47_R]


def bc47_armEdge (i : Fin 3) : Sym2 (Site 2) :=
  ![s(bc47_x, bc47_a1), s(bc47_x, bc47_a2), s(bc47_x, bc47_a3)] i

theorem bc47_armEdge_zero : bc47_armEdge 0 = s(bc47_x, bc47_a1) := rfl
theorem bc47_armEdge_one : bc47_armEdge 1 = s(bc47_x, bc47_a2) := rfl
theorem bc47_armEdge_two : bc47_armEdge 2 = s(bc47_x, bc47_a3) := rfl

open Classical in


noncomputable def bc47_fakeConfig : ConfigSpace (Sym2 (Site 2)) :=
  fun e =>
    if (∃ i : Fin 3, e = bc47_armEdge i) then true
    else if (∃ k : ℤ, 0 ≤ k ∧ e = s(bc47_R k, bc47_R (k + 1))) then true
    else false



theorem bc47_R_adj (k : ℤ) : (hypercubicLattice 2).Adj (bc47_R k) (bc47_R (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_R]

theorem bc47_x_adj_a1 : (hypercubicLattice 2).Adj bc47_x bc47_a1 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_x, bc47_a1]

theorem bc47_x_adj_a2 : (hypercubicLattice 2).Adj bc47_x bc47_a2 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_x, bc47_a2]

theorem bc47_x_adj_a3 : (hypercubicLattice 2).Adj bc47_x bc47_a3 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc47_x, bc47_a3]


theorem bc47_armEdge_open (i : Fin 3) : bc47_fakeConfig (bc47_armEdge i) = true := by
  classical
  rw [bc47_fakeConfig, if_pos ⟨i, rfl⟩]

theorem bc47_x_a1_open : bc47_fakeConfig s(bc47_x, bc47_a1) = true := bc47_armEdge_open 0

theorem bc47_x_a2_open : bc47_fakeConfig s(bc47_x, bc47_a2) = true := bc47_armEdge_open 1

theorem bc47_x_a3_open : bc47_fakeConfig s(bc47_x, bc47_a3) = true := bc47_armEdge_open 2


theorem bc47_R_edge_open (k : ℤ) (hk : 0 ≤ k) :
    bc47_fakeConfig s(bc47_R k, bc47_R (k + 1)) = true := by
  classical
  rw [bc47_fakeConfig]
  by_cases h : (∃ i : Fin 3, s(bc47_R k, bc47_R (k + 1)) = bc47_armEdge i)
  · rw [if_pos h]
  · rw [if_neg h, if_pos ⟨k, hk, rfl⟩]



theorem bc47_R_edge_connected (k : ℤ) (hk : 0 ≤ k) :
    Connected 2 bc47_fakeConfig (bc47_R k) (bc47_R (k + 1)) :=
  IsOpenEdge.connected ⟨bc47_R_adj k, bc47_R_edge_open k hk⟩


theorem bc47_x_connected_R (m : ℤ) (hm : 0 ≤ m) :
    Connected 2 bc47_fakeConfig bc47_x (bc47_R m) := by
  rw [bc47_x_eq_R0]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = (j : ℤ) := ⟨m.toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl bc47_fakeConfig (bc47_R 0)
  | succ i ih =>
    have hi : (0 : ℤ) ≤ (i : ℤ) := by positivity
    have step : Connected 2 bc47_fakeConfig (bc47_R (i : ℤ)) (bc47_R ((i : ℤ) + 1)) :=
      bc47_R_edge_connected (i : ℤ) hi
    have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at step
    exact (ih).trans step

theorem bc47_x_connected_a1 : Connected 2 bc47_fakeConfig bc47_x bc47_a1 :=
  IsOpenEdge.connected ⟨bc47_x_adj_a1, bc47_x_a1_open⟩

theorem bc47_x_connected_a2 : Connected 2 bc47_fakeConfig bc47_x bc47_a2 :=
  IsOpenEdge.connected ⟨bc47_x_adj_a2, bc47_x_a2_open⟩

theorem bc47_x_connected_a3 : Connected 2 bc47_fakeConfig bc47_x bc47_a3 :=
  IsOpenEdge.connected ⟨bc47_x_adj_a3, bc47_x_a3_open⟩

theorem bc47_R_outside_box (n : ℕ) : bc47_R (n + 1) ∉ box 2 n := by
  rw [mem_box, not_forall]
  refine ⟨0, ?_⟩
  rw [not_le]
  simp only [bc47_R, Matrix.cons_val_zero]
  omega


theorem bc47_a1_ambient_infinite : (cluster 2 bc47_fakeConfig bc47_a1).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc47_R (n + 1), bc47_R_outside_box n, ?_⟩
  exact (bc47_x_connected_a1.symm).trans (bc47_x_connected_R (n + 1) (by positivity))

theorem bc47_a2_ambient_infinite : (cluster 2 bc47_fakeConfig bc47_a2).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc47_R (n + 1), bc47_R_outside_box n, ?_⟩
  exact (bc47_x_connected_a2.symm).trans (bc47_x_connected_R (n + 1) (by positivity))

theorem bc47_a3_ambient_infinite : (cluster 2 bc47_fakeConfig bc47_a3).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  refine ⟨bc47_R (n + 1), bc47_R_outside_box n, ?_⟩
  exact (bc47_x_connected_a3.symm).trans (bc47_x_connected_R (n + 1) (by positivity))










theorem bc47_arm_not_R_edge (a : Site 2)
    (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) (k : ℤ) (hk : 0 ≤ k) :
    a ∉ s(bc47_R k, bc47_R (k + 1)) := by
  
  
  have hne : ∀ j : ℤ, a ≠ bc47_R j ∨ j < 0 := by
    intro j
    rcases ha with rfl | rfl | rfl
    · left; intro h
      have h1 := congrArg (fun v : Site 2 => v 1) h
      simp [bc47_a1, bc47_R] at h1
    · left; intro h
      have h1 := congrArg (fun v : Site 2 => v 1) h
      simp [bc47_a2, bc47_R] at h1
    · 
      by_cases hj : j < 0
      · exact Or.inr hj
      · left; intro h
        have h0 := congrArg (fun v : Site 2 => v 0) h
        simp only [bc47_a3, bc47_R, Matrix.cons_val_zero] at h0
        omega
  rw [Sym2.mem_iff]
  push Not
  refine ⟨?_, ?_⟩
  · rcases hne k with h | h
    · exact h
    · omega
  · rcases hne (k + 1) with h | h
    · exact h
    · omega



theorem bc47_arm_isolated (a : Site 2)
    (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) (y : Site 2) :
    ¬ (openSubgraph 2 (removeSite bc47_x bc47_fakeConfig)).Adj a y := by
  classical
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  by_cases hx : bc47_x ∈ s(a, y)
  · rw [removeSite_apply_of_mem hx] at hopen; exact Bool.false_ne_true hopen
  · rw [removeSite_apply_of_notMem hx, bc47_fakeConfig] at hopen
    
    have hnotstub : ¬ (∃ i : Fin 3, s(a, y) = bc47_armEdge i) := by
      rintro ⟨i, hi⟩
      apply hx
      
      have : bc47_x ∈ bc47_armEdge i := by
        fin_cases i <;> · rw [bc47_armEdge]; simp
      rwa [← hi] at this
    have hnotray : ¬ (∃ k : ℤ, 0 ≤ k ∧ s(a, y) = s(bc47_R k, bc47_R (k + 1))) := by
      rintro ⟨k, hk, hek⟩
      have hamem : a ∈ s(a, y) := Sym2.mem_mk_left a y
      rw [hek] at hamem
      exact bc47_arm_not_R_edge a ha k hk hamem
    rw [if_neg hnotstub, if_neg hnotray] at hopen
    exact Bool.false_ne_true hopen



theorem bc47_arm_removeSite_finite (a : Site 2)
    (ha : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) :
    (cluster 2 (removeSite bc47_x bc47_fakeConfig) a).Finite := by
  have hsub : cluster 2 (removeSite bc47_x bc47_fakeConfig) a ⊆ {a} := by
    intro y hy
    rw [mem_cluster] at hy
    obtain ⟨w⟩ := hy
    cases w with
    | nil => simp
    | @cons _ b _ hadj _ => exact absurd hadj (bc47_arm_isolated a ha b)
  exact (Set.finite_singleton _).subset hsub


theorem bc47_arms_removeSite_disconnected :
    ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a1 bc47_a2 ∧
    ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a1 bc47_a3 ∧
    ¬ Connected 2 (removeSite bc47_x bc47_fakeConfig) bc47_a2 bc47_a3 := by
  
  
  have key : ∀ a b : Site 2, (a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3) →
      Connected 2 (removeSite bc47_x bc47_fakeConfig) a b → b = a := by
    intro a b ha hconn
    obtain ⟨w⟩ := hconn
    cases w with
    | nil => rfl
    | @cons _ c _ hadj _ => exact absurd hadj (bc47_arm_isolated a ha c)
  refine ⟨?_, ?_, ?_⟩
  · intro h; have heq := key bc47_a1 bc47_a2 (Or.inl rfl) h
    
    have : bc47_a2 1 = bc47_a1 1 := by rw [heq]
    simp [bc47_a1, bc47_a2] at this
  · intro h; have heq := key bc47_a1 bc47_a3 (Or.inl rfl) h
    
    have : bc47_a3 0 = bc47_a1 0 := by rw [heq]
    simp [bc47_a1, bc47_a3] at this
  · intro h; have heq := key bc47_a2 bc47_a3 (Or.inr (Or.inl rfl)) h
    
    have : bc47_a3 0 = bc47_a2 0 := by rw [heq]
    simp [bc47_a2, bc47_a3] at this


theorem bc47_arms_distinct : bc47_a1 ≠ bc47_a2 ∧ bc47_a1 ≠ bc47_a3 ∧ bc47_a2 ≠ bc47_a3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; have hc : bc47_a1 1 = bc47_a2 1 := by rw [h]
    simp [bc47_a1, bc47_a2] at hc
  · intro h; have hc : bc47_a1 0 = bc47_a3 0 := by rw [h]
    simp [bc47_a1, bc47_a3] at hc
  · intro h; have hc : bc47_a2 0 = bc47_a3 0 := by rw [h]
    simp [bc47_a2, bc47_a3] at hc







theorem bc47_isTrifurcation_fakeConfig :
    IsTrifurcation 2 bc47_fakeConfig bc47_x := by
  refine ⟨bc47_a1, bc47_a2, bc47_a3, bc47_arms_distinct,
    ⟨bc47_x_connected_a1, bc47_x_connected_a2, bc47_x_connected_a3⟩,
    ⟨bc47_a1_ambient_infinite, bc47_a2_ambient_infinite, bc47_a3_ambient_infinite⟩,
    bc47_arms_removeSite_disconnected⟩











theorem bc47_isTrifurcation_not_threeRemoveSiteInfiniteArms :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2),
      IsTrifurcation 2 ω x ∧
      ∃ a₁ a₂ a₃ : Site 2,
        (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
        (Connected 2 ω x a₁ ∧ Connected 2 ω x a₂ ∧ Connected 2 ω x a₃) ∧
        ((cluster 2 ω a₁).Infinite ∧ (cluster 2 ω a₂).Infinite ∧ (cluster 2 ω a₃).Infinite) ∧
        (¬ Connected 2 (removeSite x ω) a₁ a₂ ∧
         ¬ Connected 2 (removeSite x ω) a₁ a₃ ∧
         ¬ Connected 2 (removeSite x ω) a₂ a₃) ∧
        
        (¬ (cluster 2 (removeSite x ω) a₁).Infinite ∧
         ¬ (cluster 2 (removeSite x ω) a₂).Infinite ∧
         ¬ (cluster 2 (removeSite x ω) a₃).Infinite) :=
  ⟨bc47_fakeConfig, bc47_x, bc47_isTrifurcation_fakeConfig,
    bc47_a1, bc47_a2, bc47_a3, bc47_arms_distinct,
    ⟨bc47_x_connected_a1, bc47_x_connected_a2, bc47_x_connected_a3⟩,
    ⟨bc47_a1_ambient_infinite, bc47_a2_ambient_infinite, bc47_a3_ambient_infinite⟩,
    bc47_arms_removeSite_disconnected,
    ⟨fun h => h (bc47_arm_removeSite_finite bc47_a1 (Or.inl rfl)),
     fun h => h (bc47_arm_removeSite_finite bc47_a2 (Or.inr (Or.inl rfl))),
     fun h => h (bc47_arm_removeSite_finite bc47_a3 (Or.inr (Or.inr rfl)))⟩⟩
















def bc47_IsClassicalTrifurcation (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (IsOpenEdge d ω x a₁ ∧ IsOpenEdge d ω x a₂ ∧ IsOpenEdge d ω x a₃) ∧
    ((cluster d (removeSite x ω) a₁).Infinite ∧ (cluster d (removeSite x ω) a₂).Infinite ∧
      (cluster d (removeSite x ω) a₃).Infinite) ∧
    (¬ Connected d (removeSite x ω) a₁ a₂ ∧
     ¬ Connected d (removeSite x ω) a₁ a₃ ∧
     ¬ Connected d (removeSite x ω) a₂ a₃)



theorem bc47_removeSite_le (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite x ω ≤ ω := by
  rw [← daep_removeSites_singleton x ω]
  exact daep_removeSites_le {x} ω






theorem bc47_isTrifurcation_of_classical (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc47_IsClassicalTrifurcation ω x) : IsTrifurcation d ω x := by
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := h
  refine ⟨a₁, a₂, a₃, hne, ⟨he1.connected, he2.connected, he3.connected⟩, ?_, hsep⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hi1.mono (cluster_mono (bc47_removeSite_le x ω) a₁)
  · exact hi2.mono (cluster_mono (bc47_removeSite_le x ω) a₂)
  · exact hi3.mono (cluster_mono (bc47_removeSite_le x ω) a₃)




theorem bc47_only_infinite_neighbour_is_R1 (a : Site 2)
    (hea : IsOpenEdge 2 bc47_fakeConfig bc47_x a)
    (hia : (cluster 2 (removeSite bc47_x bc47_fakeConfig) a).Infinite) : a = bc47_R 1 := by
  by_contra hne
  
  
  have hxa_ne : a ≠ bc47_x := (hea.1.ne).symm
  have hopen := hea.2
  rw [bc47_fakeConfig] at hopen
  by_cases hstub : (∃ i : Fin 3, s(bc47_x, a) = bc47_armEdge i)
  · obtain ⟨i, hi⟩ := hstub
    
    
    have harm : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3 := by
      have hedge : s(bc47_x, a) = s(bc47_x, bc47_a1) ∨ s(bc47_x, a) = s(bc47_x, bc47_a2) ∨
          s(bc47_x, a) = s(bc47_x, bc47_a3) := by
        fin_cases i
        · exact Or.inl (hi.trans bc47_armEdge_zero)
        · exact Or.inr (Or.inl (hi.trans bc47_armEdge_one))
        · exact Or.inr (Or.inr (hi.trans bc47_armEdge_two))
      rcases hedge with he | he | he <;>
        · rw [Sym2.eq_iff] at he
          rcases he with ⟨_, ha⟩ | ⟨_, hax⟩
          · first | (exact Or.inl ha) | (exact Or.inr (Or.inl ha))
                  | (exact Or.inr (Or.inr ha))
          · exact absurd hax hxa_ne
    exact absurd (bc47_arm_removeSite_finite a harm) hia
  · rw [if_neg hstub] at hopen
    by_cases hray : (∃ k : ℤ, 0 ≤ k ∧ s(bc47_x, a) = s(bc47_R k, bc47_R (k + 1)))
    · obtain ⟨k, hk, hek⟩ := hray
      rw [bc47_x_eq_R0, Sym2.eq_iff] at hek
      rcases hek with ⟨hx, ha⟩ | ⟨hx, ha⟩
      · 
        have hk0 : (0 : ℤ) = k := bc47_R_inj hx
        rw [← hk0] at ha
        exact hne (ha.trans (by norm_num))
      · 
        have : (0 : ℤ) = k + 1 := bc47_R_inj hx
        omega
    · rw [if_neg hray] at hopen; exact Bool.false_ne_true hopen




theorem bc47_not_classical_fakeConfig :
    ¬ bc47_IsClassicalTrifurcation bc47_fakeConfig bc47_x := by
  rintro ⟨a₁, a₂, a₃, ⟨h12, _, _⟩, ⟨he1, he2, _⟩, ⟨hi1, hi2, _⟩, _⟩
  have e1 := bc47_only_infinite_neighbour_is_R1 a₁ he1 hi1
  have e2 := bc47_only_infinite_neighbour_is_R1 a₂ he2 hi2
  exact h12 (e1.trans e2.symm)
















theorem arc_trifArmsRemoveSiteInfinite_of_classical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcl : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x) :
    arc_TrifArmsRemoveSiteInfinite ω n := by
  intro x hxbox htri
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, hinf, hsep⟩ := hcl x hxbox htri
  
  refine ⟨![a₁, a₂, a₃], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨he1.1, he1.2⟩
    · exact ⟨he2.1, he2.2⟩
    · exact ⟨he3.1, he3.2⟩
  · 
    intro i; fin_cases i
    · exact (he1.1.ne).symm
    · exact (he2.1.ne).symm
    · exact (he3.1.ne).symm
  · exact hsep
  · intro i; fin_cases i
    · exact hinf.1
    · exact hinf.2.1
    · exact hinf.2.2






theorem bc47_trif_arm_data_of_classical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcl : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) :=
  arc_trif_arm_data ω n (arc_trifArmsRemoveSiteInfinite_of_classical ω n hcl) x hxbox htri












def bc47_clawIsArm (v : Fin 10) : Bool := decide (4 ≤ v.val)









theorem bc47_clawShadow_classical_ok :
    ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) →
      ∃ n₁ n₂ n₃ : Fin 10,
        
        (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧
          bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧
        (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧
        (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧
        (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) := by
  decide


def bc47_chainIsArm (v : Fin 8) : Bool := decide (4 ≤ v.val)






theorem bc47_chainShadow_arms_ok :
    ∀ c : Fin 8, (c = 1 ∨ c = 2) →
      ∃ n₁ n₂ n₃ : Fin 8,
        (bc46_chainLab c n₁ ≠ bc46_chainLab c n₂ ∧ bc46_chainLab c n₁ ≠ bc46_chainLab c n₃ ∧
          bc46_chainLab c n₂ ≠ bc46_chainLab c n₃) ∧
        (∃ z₁, bc46_chainLab c z₁ = bc46_chainLab c n₁ ∧ bc47_chainIsArm z₁ = true) ∧
        (∃ z₂, bc46_chainLab c z₂ = bc46_chainLab c n₂ ∧ bc47_chainIsArm z₂ = true) ∧
        (∃ z₃, bc46_chainLab c z₃ = bc46_chainLab c n₃ ∧ bc47_chainIsArm z₃ = true) := by
  decide









theorem bc47_classical_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x :=
  fun x hxbox htri => absurd htri (hno x hxbox)














theorem bc47_x_mem_box (n : ℕ) : bc47_x ∈ box 2 n := by
  rw [mem_box]; intro i; fin_cases i <;> simp [bc47_x]






theorem bc47_arc_residue_fails_on_fakeConfig (n : ℕ) :
    ¬ arc_TrifArmsRemoveSiteInfinite bc47_fakeConfig n := by
  intro hres
  obtain ⟨c, hadj, hne, ⟨hsep01, _, _⟩, hinf⟩ :=
    hres bc47_x (bc47_x_mem_box n) bc47_isTrifurcation_fakeConfig
  
  have e0 : c 0 = bc47_R 1 := bc47_only_infinite_neighbour_is_R1 (c 0) (hadj 0) (hinf 0)
  have e1 : c 1 = bc47_R 1 := bc47_only_infinite_neighbour_is_R1 (c 1) (hadj 1) (hinf 1)
  
  exact hsep01 (e0.symm ▸ e1.symm ▸ connected_refl _ (bc47_R 1))

end StatMech.Walls
