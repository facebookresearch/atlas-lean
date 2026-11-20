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
import Code.Percolation.SingleLeafHallClose
import Code.Percolation.SecondPeelingClose
import Code.Percolation.SpanForestArmsClose

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}









theorem arc_x_isolated (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSite x ω)).Adj x y := by
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  rw [removeSite_apply_of_mem (by simp)] at hopen
  exact Bool.false_ne_true hopen




theorem arc_walk_avoids_x {x a b : Site d} {ω : ConfigSpace (Sym2 (Site d))} (hax : a ≠ x)
    (w : (openSubgraph d (removeSite x ω)).Walk a b) : x ∉ w.support := by
  induction w with
  | nil => simpa using (Ne.symm hax)
  | @cons u v c huv w' ih =>
    rw [Walk.support_cons, List.mem_cons, not_or]
    refine ⟨Ne.symm hax, ?_⟩
    have hvx : v ≠ x := fun h => by subst h; exact arc_x_isolated v ω u huv.symm
    exact ih hvx









theorem arc_infinite_cluster_reaches_boundary
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) (x a : Site d)
    (hax : a ≠ x) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, hr⟩ :=
    tfc_walk_crossing (openSubgraph d (removeSite x ω)) (fun v => v ∈ box d n) w habox hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSite x ω)) hbc
  refine ⟨b, tfc_boundary_cross_vertex n hn b c hb hc hblat, ?_⟩
  obtain ⟨wab⟩ := hr
  exact ⟨wab, arc_walk_avoids_x hax wab⟩




theorem arc_connected_removeSite_reaches_boundary
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) (x a : Site d)
    (hax : a ≠ x) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n, Connected d (removeSite x ω) a z := by
  obtain ⟨z, hzb, w, _⟩ := arc_infinite_cluster_reaches_boundary ω n hn x a hax habox hinf
  exact ⟨z, hzb, ⟨w⟩⟩


















def arc_TrifArmsRemoveSiteInfinite (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∀ x, x ∈ box d n → IsTrifurcation d ω x →
    ∃ c : Fin 3 → Site d,
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, (cluster d (removeSite x ω) (c i)).Infinite)











theorem arc_neighbour_in_box_succ {x c : Site d} {n : ℕ} (hx : x ∈ box d n)
    (hadj : (hypercubicLattice d).Adj x c) : c ∈ box d (n + 1) := by
  rw [hypercubicLattice_adj] at hadj
  rw [mem_box] at hx ⊢
  intro i
  
  have hcoord : (x i - c i).natAbs ≤ 1 := by
    have hle : (x i - c i).natAbs ≤ ∑ j, (x j - c j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - c j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have := hx i
  omega






theorem arc_trif_arm_data (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hres : arc_TrifArmsRemoveSiteInfinite ω n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) := by
  classical
  obtain ⟨c, hadj, hne, hcut, hinf⟩ := hres x hxbox htri
  
  have hcbox : ∀ i, c i ∈ box d (n + 1) := fun i =>
    arc_neighbour_in_box_succ hxbox (hadj i).1
  
  choose zr hzrb hzrw using fun i =>
    arc_infinite_cluster_reaches_boundary ω (n + 1) (by omega) x (c i) (hne i) (hcbox i) (hinf i)
  exact ⟨c, zr, hadj, hne, hcut, fun i => ⟨hzrb i, hzrw i⟩⟩



















theorem arc_armForestReaching_of_residue_single_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (_hxbox : x ∈ box d n) (_htri : IsTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    sfa_ArmForestReaching ω n :=
  sfa_armForestReaching_star ω n c hsingle hadj hbdry hne hinj hcut


theorem arc_Tcount_le_boundary_of_residue_single_boundary (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {x : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n
    (arc_armForestReaching_of_residue_single_boundary ω n hxbox htri hsingle c hadj hne hcut
      hbdry hinj)



















def arc_p (k : ℤ) : Site 2 := ![k, 0]

theorem arc_p_adj (k : ℤ) : (hypercubicLattice 2).Adj (arc_p k) (arc_p (k + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [arc_p]

theorem arc_p_inj : Function.Injective arc_p := by
  intro a b h
  have : (arc_p a) 0 = (arc_p b) 0 := by rw [h]
  simpa [arc_p] using this

open Classical in

noncomputable def arc_rayConfig : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ k : ℤ, -1 ≤ k ∧ e = s(arc_p k, arc_p (k + 1))) then true else false

theorem arc_ray_open (k : ℤ) (hk : -1 ≤ k) :
    arc_rayConfig s(arc_p k, arc_p (k + 1)) = true := by
  classical
  rw [arc_rayConfig, if_pos]; exact ⟨k, hk, rfl⟩

theorem arc_ray_edge_connected (k : ℤ) (hk : -1 ≤ k) :
    Connected 2 arc_rayConfig (arc_p k) (arc_p (k + 1)) :=
  IsOpenEdge.connected ⟨arc_p_adj k, arc_ray_open k hk⟩


theorem arc_ray_connected (m : ℤ) (hm : -1 ≤ m) :
    Connected 2 arc_rayConfig (arc_p (-1)) (arc_p m) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = -1 + j := ⟨(m + 1).toNat, by omega⟩
  clear hm
  induction j with
  | zero => simpa using connected_refl arc_rayConfig (arc_p (-1))
  | succ i ih =>
    have hi : (-1 : ℤ) ≤ -1 + i := by omega
    have step : Connected 2 arc_rayConfig (arc_p (-1 + i)) (arc_p (-1 + (i : ℤ) + 1)) :=
      arc_ray_edge_connected (-1 + i) hi
    have hcast : (-1 : ℤ) + (i + 1 : ℕ) = (-1 + (i : ℤ)) + 1 := by push_cast; ring
    rw [hcast]
    exact (ih).trans step

theorem arc_p_outside_box (n : ℕ) : arc_p (n + 1) ∉ box 2 n := by
  rw [mem_box]; rw [not_forall]
  refine ⟨0, ?_⟩
  rw [not_le]
  simp only [arc_p, Matrix.cons_val_zero]
  have h1 : (0 : ℤ) ≤ (n : ℤ) + 1 := by positivity
  have h2 : ((n : ℤ) + 1).natAbs = (n + 1 : ℕ) := by omega
  omega


theorem arc_arm_ambient_infinite : (cluster 2 arc_rayConfig (arc_p (-1))).Infinite := by
  rw [cluster_infinite_iff]
  intro n
  exact ⟨arc_p (n + 1), arc_p_outside_box n, arc_ray_connected (n + 1) (by omega)⟩


theorem arc_armNeighbour_isolated (y : Site 2) :
    ¬ (openSubgraph 2 (removeSite (arc_p 0) arc_rayConfig)).Adj (arc_p (-1)) y := by
  classical
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  by_cases hx : arc_p 0 ∈ s(arc_p (-1), y)
  · rw [removeSite_apply_of_mem hx] at hopen; exact Bool.false_ne_true hopen
  · rw [removeSite_apply_of_notMem hx] at hopen
    rw [arc_rayConfig] at hopen
    split at hopen
    · rename_i hex
      obtain ⟨k, hk, hek⟩ := hex
      rw [Sym2.eq_iff] at hek
      rcases hek with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hkeq : (-1 : ℤ) = k := arc_p_inj h1
        rw [← hkeq] at h2
        apply hx
        rw [Sym2.mem_iff]; right
        rw [h2]; norm_num
      · have : (-1 : ℤ) = k + 1 := arc_p_inj h1
        omega
    · exact Bool.false_ne_true hopen


theorem arc_arm_removeSite_finite :
    (cluster 2 (removeSite (arc_p 0) arc_rayConfig) (arc_p (-1))).Finite := by
  have hsub : cluster 2 (removeSite (arc_p 0) arc_rayConfig) (arc_p (-1)) ⊆ {arc_p (-1)} := by
    intro y hy
    rw [mem_cluster] at hy
    obtain ⟨w⟩ := hy
    cases w with
    | nil => simp
    | @cons _ b _ hadj _ => exact absurd hadj (arc_armNeighbour_isolated b)
  exact (Set.finite_singleton _).subset hsub


theorem arc_arm_adj_x : (openSubgraph 2 arc_rayConfig).Adj (arc_p 0) (arc_p (-1)) := by
  have h : arc_rayConfig s(arc_p (-1), arc_p 0) = true := by
    have := arc_ray_open (-1) (by norm_num); simpa using this
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [arc_p]
  · rw [Sym2.eq_swap]; exact h







theorem arc_ambientInfinite_not_removeSiteInfinite :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2),
      (openSubgraph 2 ω).Adj x a ∧
      Connected 2 ω x a ∧
      (cluster 2 ω a).Infinite ∧
      ¬ (cluster 2 (removeSite x ω) a).Infinite :=
  ⟨arc_rayConfig, arc_p 0, arc_p (-1), arc_arm_adj_x, arc_arm_adj_x.reachable,
    arc_arm_ambient_infinite, fun hinf => hinf arc_arm_removeSite_finite⟩

end Percolation

end StatMech
