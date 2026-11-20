/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanZ2
import Code.Lattice.ClusterBoundaryRecovery
import Code.Lattice.PeierlsEulerParity
import Code.Lattice.PeierlsSingleCircuit

open Finset Set SimpleGraph

namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable













theorem reachable_induce_of_walk_in_support {K : Set (Site 2)} {T : Finset (Site 2)}
    {f g : Site 2} (p : (faceBoundaryGraph K).Walk f g)
    (hsub : ∀ v ∈ p.support, v ∈ T) (hf : f ∈ T) :
    ((faceBoundaryGraph K).induce (T : Set (Site 2))).Reachable ⟨f, hf⟩
      ⟨g, hsub g p.end_mem_support⟩ := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab q ih =>
    
    have hbT : b ∈ T := hsub b (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ q.start_mem_support)
    have hqsub : ∀ v ∈ q.support, v ∈ T := by
      intro v hv
      exact hsub v (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hv)
    
    have hadjI : ((faceBoundaryGraph K).induce (T : Set (Site 2))).Adj ⟨a, hf⟩ ⟨b, hbT⟩ := by
      rw [SimpleGraph.induce_adj]; exact hab
    have hrec := ih hqsub hbT
    exact (SimpleGraph.Adj.reachable hadjI).trans hrec









theorem faceBoundaryConnected_of_walks {K : Set (Site 2)} {T : Finset (Site 2)}
    (hne : T.Nonempty)
    (hwalk : ∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph K).Walk f g,
        ∀ v ∈ p.support, v ∈ T) :
    FaceBoundaryConnected K T := by
  rw [FaceBoundaryConnected]
  have hnonempty : Nonempty (T : Set (Site 2)) := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨⟨t, ht⟩⟩
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, hnonempty⟩
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  obtain ⟨p, hp⟩ := hwalk f hf g hg
  have := reachable_induce_of_walk_in_support p hp hf
  
  convert this using 2














theorem mem_singletonOrigin (p q : ℤ) :
    (![p, q] : Site 2) ∈ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ↔ p = 0 ∧ q = 0 := by
  rw [Finset.mem_coe, Finset.mem_singleton, origin_eq_zerozero, site2_eq]



noncomputable def singletonBoundarySupport : Finset (Site 2) :=
  {![(0:ℤ), 0], ![(-1:ℤ), 0], ![(-1:ℤ), -1], ![(0:ℤ), -1]}



theorem singleton_adj_00_L :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(0:ℤ), 0] ![(-1:ℤ), 0] := by
  have h := latAdj_left (0:ℤ) (0:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(0:ℤ), 0]) (![(-1:ℤ), 0])
      = s(faceCorner00 0 0, faceCorner01 0 0) := by
    have := sharedPrimalEdge_left (0:ℤ) (0:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner01
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  refine ⟨fun _ ⟨_, h2⟩ => by omega, fun _ => ⟨rfl, rfl⟩⟩



theorem singleton_adj_00_B :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have h := latAdj_bottom (0:ℤ) (0:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(0:ℤ), 0]) (![(0:ℤ), -1])
      = s(faceCorner00 0 0, faceCorner10 0 0) := by
    have := sharedPrimalEdge_bottom (0:ℤ) (0:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner10
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  refine ⟨fun _ ⟨_, h2⟩ => by omega, fun _ => ⟨rfl, rfl⟩⟩



theorem singleton_adj_L_LB :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(-1:ℤ), 0] ![(-1:ℤ), -1] := by
  have h := latAdj_bottom (-1:ℤ) (0:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(-1:ℤ), 0]) (![(-1:ℤ), -1])
      = s(faceCorner00 (-1) 0, faceCorner10 (-1) 0) := by
    have := sharedPrimalEdge_bottom (-1:ℤ) (0:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner10
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  rw [show ((-1:ℤ) + 1) = 0 from by ring]
  constructor
  · rintro ⟨h1, _⟩; omega
  · rintro h; exact absurd ⟨rfl, rfl⟩ h



theorem singleton_adj_B_LB :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj
      ![(0:ℤ), -1] ![(-1:ℤ), -1] := by
  have h := latAdj_left (0:ℤ) (-1:ℤ)
  rw [show ((0:ℤ) - 1) = -1 from by ring] at h
  rw [faceBoundaryGraph_adj]
  refine ⟨h, ?_⟩
  have hs : sharedPrimalEdge (![(0:ℤ), -1]) (![(-1:ℤ), -1])
      = s(faceCorner00 0 (-1), faceCorner01 0 (-1)) := by
    have := sharedPrimalEdge_left (0:ℤ) (-1:ℤ)
    rw [show ((0:ℤ) - 1) = -1 from by ring] at this; exact this
  rw [hs]; unfold faceCorner00 faceCorner01
  rw [bdEdge_mk, mem_singletonOrigin, mem_singletonOrigin]
  rw [show ((-1:ℤ) + 1) = 0 from by ring]
  constructor
  · rintro ⟨h1, _⟩; omega
  · rintro h; exact absurd ⟨rfl, rfl⟩ h


theorem mem_singletonBoundarySupport_00 :
    (![(0:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
  unfold singletonBoundarySupport; simp


theorem singletonBoundarySupport_cases {v : Site 2} (hv : v ∈ singletonBoundarySupport) :
    v = ![(0:ℤ), 0] ∨ v = ![(-1:ℤ), 0] ∨ v = ![(-1:ℤ), -1] ∨ v = ![(0:ℤ), -1] := by
  unfold singletonBoundarySupport at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  tauto




theorem singleton_walk_from_00 {v : Site 2} (hv : v ∈ singletonBoundarySupport) :
    ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
        ![(0:ℤ), 0] v, ∀ w ∈ p.support, w ∈ singletonBoundarySupport := by
  have m00 : (![(0:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  have mL : (![(-1:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  have mLB : (![(-1:ℤ), -1] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  have mB : (![(0:ℤ), -1] : Site 2) ∈ singletonBoundarySupport := by
    unfold singletonBoundarySupport; simp
  rcases singletonBoundarySupport_cases hv with rfl | rfl | rfl | rfl
  · 
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact m00
  · 
    refine ⟨SimpleGraph.Walk.cons singleton_adj_00_L SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact m00
    · exact mL
  · 
    refine ⟨SimpleGraph.Walk.cons singleton_adj_00_L
      (SimpleGraph.Walk.cons singleton_adj_L_LB SimpleGraph.Walk.nil), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact m00
    · exact mL
    · exact mLB
  · 
    refine ⟨SimpleGraph.Walk.cons singleton_adj_00_B SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact m00
    · exact mB





theorem singletonOrigin_faceBoundaryConnected :
    FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
      singletonBoundarySupport := by
  apply faceBoundaryConnected_of_walks ⟨_, mem_singletonBoundarySupport_00⟩
  intro f hf g hg
  obtain ⟨pf, hpf⟩ := singleton_walk_from_00 hf
  obtain ⟨pg, hpg⟩ := singleton_walk_from_00 hg
  
  refine ⟨pf.reverse.append pg, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append] at hw
  rcases List.mem_append.mp hw with hwf | hwg
  · 
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hwf
    exact hpf w hwf
  · 
    exact hpg w (List.mem_of_mem_tail hwg)




theorem support_singletonOrigin_subset :
    (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support
      ⊆ (singletonBoundarySupport : Set (Site 2)) := by
  have h := support_faceBoundaryGraph_subset (↑({origin 2} : Finset (Site 2)) : Set (Site 2))
  intro f hf
  have hf' := h hf
  rw [Set.mem_iUnion] at hf'
  obtain ⟨c, hc⟩ := hf'
  rw [Set.mem_iUnion] at hc
  obtain ⟨hcS, hfc⟩ := hc
  rw [Finset.mem_coe, Finset.mem_singleton, origin_eq_zerozero] at hcS
  subst hcS
  unfold cornerFaces at hfc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.coe_insert, Set.mem_insert_iff,
    Finset.coe_singleton, Set.mem_singleton_iff] at hfc
  unfold singletonBoundarySupport
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hfc with h | h | h | h <;> subst h
  · right; right; left; congr 1
  · right; left; congr 1
  · right; right; right; congr 1
  · left; rfl








theorem singletonOrigin_single_dualCircuit :
    ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk
        ![(0:ℤ), 0] ![(0:ℤ), 0],
      c.IsTrail ∧
        ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet,
          e ∈ c.edges :=
  faceBoundaryGraph_single_dualCircuit support_singletonOrigin_subset
    singletonOrigin_faceBoundaryConnected mem_singletonBoundarySupport_00








noncomputable def boxCluster (m n : ℕ) : Finset (Site 2) :=
  (Finset.Icc (0 : ℤ) m ×ˢ Finset.Icc (0 : ℤ) n).image (fun p => ![p.1, p.2])


theorem mem_boxCluster (m n : ℕ) (x : Site 2) :
    x ∈ boxCluster m n ↔ 0 ≤ x 0 ∧ x 0 ≤ m ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
  unfold boxCluster; rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hab
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨(x 0, x 1), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; omega
    · funext i; fin_cases i <;> rfl


theorem mem_box_coords (m n : ℕ) (p q : ℤ) :
    (![p, q] : Site 2) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      0 ≤ p ∧ p ≤ m ∧ 0 ≤ q ∧ q ≤ n := by
  rw [Finset.mem_coe, mem_boxCluster]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]


theorem origin_mem_boxCluster (m n : ℕ) : origin 2 ∈ boxCluster m n := by
  rw [mem_boxCluster, origin_eq_zerozero]; simp


theorem boxR_step (m n : ℕ) (a b : ℤ) (h1 : 0 ≤ a) (h2 : a + 1 ≤ m) (h3 : 0 ≤ b) (h4 : b ≤ n) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, b] ![a + 1, b] := by
  refine ⟨latAdj_right a b, ?_, ?_⟩ <;>
    · rw [Finset.mem_coe, mem_boxCluster]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega


theorem boxT_step (m n : ℕ) (a b : ℤ) (h1 : 0 ≤ a) (h2 : a ≤ m) (h3 : 0 ≤ b) (h4 : b + 1 ≤ n) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, b] ![a, b + 1] := by
  refine ⟨latAdj_top a b, ?_, ?_⟩ <;>
    · rw [Finset.mem_coe, mem_boxCluster]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega


theorem reach_xaxis (m n : ℕ) (k : ℕ) (hk : k ≤ m) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Reachable ![(0:ℤ), 0] ![(k:ℤ), 0] := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    have hj : j ≤ m := by omega
    have step : (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![(j:ℤ), 0] ![(j:ℤ) + 1, 0] :=
      boxR_step m n (j:ℤ) 0 (by positivity)
        (by exact_mod_cast (by omega : (j:ℤ) + 1 ≤ m)) (le_refl 0) (by positivity)
    rw [show ((j:ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring] at step
    exact (ih hj).trans (SimpleGraph.Adj.reachable step)


theorem reach_ycol (m n : ℕ) (a : ℤ) (ha0 : 0 ≤ a) (ham : a ≤ m) (k : ℕ) (hk : k ≤ n) :
    (latticeOn (↑(boxCluster m n) : Set (Site 2))).Reachable ![a, 0] ![a, (k:ℤ)] := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    have hj : j ≤ n := by omega
    have step : (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, (j:ℤ)] ![a, (j:ℤ) + 1] :=
      boxT_step m n a (j:ℤ) ha0 ham (by positivity)
        (by exact_mod_cast (by omega : (j:ℤ) + 1 ≤ n))
    rw [show ((j:ℤ) + 1) = ((j + 1 : ℕ) : ℤ) from by push_cast; ring] at step
    exact (ih hj).trans (SimpleGraph.Adj.reachable step)



theorem boxCluster_isConnectedCluster (m n : ℕ) : IsConnectedCluster (boxCluster m n) := by
  refine ⟨origin_mem_boxCluster m n, ?_⟩
  intro x hx
  rw [mem_boxCluster] at hx
  obtain ⟨h0, h1, h2, h3⟩ := hx
  rw [origin_eq_zerozero, show x = ![x 0, x 1] from by funext i; fin_cases i <;> rfl]
  set kx := (x 0).toNat with hkx
  set ky := (x 1).toNat with hky
  have hx0 : (x 0) = (kx : ℤ) := by rw [hkx]; omega
  have hx1 : (x 1) = (ky : ℤ) := by rw [hky]; omega
  have hkxm : kx ≤ m := by rw [hkx]; omega
  have hkyn : ky ≤ n := by rw [hky]; omega
  rw [hx0, hx1]
  exact (reach_xaxis m n kx hkxm).trans
    (reach_ycol m n (kx:ℤ) (by positivity) (by exact_mod_cast hkxm) ky hkyn)
















noncomputable def boxFrame (m n : ℕ) : Finset (Site 2) :=
  ((Finset.Icc (-1 : ℤ) m).image (fun a => (![a, -1] : Site 2)))
  ∪ ((Finset.Icc (-1 : ℤ) m).image (fun a => (![a, (n:ℤ)] : Site 2)))
  ∪ ((Finset.Icc (-1 : ℤ) n).image (fun b => (![(-1:ℤ), b] : Site 2)))
  ∪ ((Finset.Icc (-1 : ℤ) n).image (fun b => (![(m:ℤ), b] : Site 2)))

theorem mem_boxFrame_bottom (m n : ℕ) (a : ℤ) (h1 : -1 ≤ a) (h2 : a ≤ m) :
    (![a, -1] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
  left; left; left
  rw [Finset.mem_image]; exact ⟨a, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

theorem mem_boxFrame_top (m n : ℕ) (a : ℤ) (h1 : -1 ≤ a) (h2 : a ≤ m) :
    (![a, (n:ℤ)] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
  left; left; right
  rw [Finset.mem_image]; exact ⟨a, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

theorem mem_boxFrame_left (m n : ℕ) (b : ℤ) (h1 : -1 ≤ b) (h2 : b ≤ n) :
    (![(-1:ℤ), b] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
  left; right
  rw [Finset.mem_image]; exact ⟨b, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩

theorem mem_boxFrame_right (m n : ℕ) (b : ℤ) (h1 : -1 ≤ b) (h2 : b ≤ n) :
    (![(m:ℤ), b] : Site 2) ∈ boxFrame m n := by
  unfold boxFrame
  rw [Finset.mem_union]
  right
  rw [Finset.mem_image]; exact ⟨b, Finset.mem_Icc.mpr ⟨h1, h2⟩, rfl⟩



theorem boxFrame_bottom_adj (m n : ℕ) (a : ℤ) (h1 : 0 ≤ a + 1) (h2 : a + 1 ≤ m) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![a, -1] ![a + 1, -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_right a (-1), ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords, show ((-1:ℤ) + 1) = 0 from by ring]
  exact ⟨fun ⟨_, _, h3, _⟩ => by omega, fun h => absurd ⟨h1, h2, le_refl 0, Nat.cast_nonneg n⟩ h⟩



theorem boxFrame_top_adj (m n : ℕ) (a : ℤ) (h1 : 0 ≤ a + 1) (h2 : a + 1 ≤ m) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![a, (n:ℤ)] ![a + 1, (n:ℤ)] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_right a (n:ℤ), ?_⟩
  rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords]
  exact ⟨fun ⟨_, _, _, _⟩ ⟨_, _, _, hq⟩ => by omega,
    fun h => ⟨h1, h2, Nat.cast_nonneg n, le_refl _⟩⟩



theorem boxFrame_right_adj (m n : ℕ) (b : ℤ) (h1 : 0 ≤ b + 1) (h2 : b + 1 ≤ n) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![(m:ℤ), b] ![(m:ℤ), b + 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_top (m:ℤ) b, ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords]
  exact ⟨fun _ ⟨hp1, hp2, _, _⟩ => by omega,
    fun h => ⟨Nat.cast_nonneg m, le_refl _, h1, h2⟩⟩



theorem boxFrame_left_adj (m n : ℕ) (b : ℤ) (h1 : 0 ≤ b + 1) (h2 : b + 1 ≤ n) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![(-1:ℤ), b] ![(-1:ℤ), b + 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨latAdj_top (-1:ℤ) b, ?_⟩
  rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11
  rw [bdEdge_mk, mem_box_coords, mem_box_coords, show ((-1:ℤ) + 1) = 0 from by ring]
  exact ⟨fun ⟨hp, _, _, _⟩ => by omega,
    fun h => absurd ⟨le_refl 0, Nat.cast_nonneg m, h1, h2⟩ h⟩








theorem boxFrame_bottom_walk (m n : ℕ) (k : ℕ) (hk : k ≤ m + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(k:ℤ) - 1, -1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_bottom m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ m := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjm : (j:ℤ) ≤ (m:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(j:ℤ) - 1, -1] ![(j:ℤ), -1] := by
      have h := boxFrame_bottom_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_bottom m n (j:ℤ) (by omega) hjm


theorem boxFrame_left_walk (m n : ℕ) (k : ℕ) (hk : k ≤ n + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(-1:ℤ), (k:ℤ) - 1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_left m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ n := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjn : (j:ℤ) ≤ (n:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(-1:ℤ), (j:ℤ) - 1] ![(-1:ℤ), (j:ℤ)] := by
      have h := boxFrame_left_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_left m n (j:ℤ) (by omega) hjn



theorem boxFrame_right_walk (m n : ℕ) (k : ℕ) (hk : k ≤ n + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(m:ℤ), -1] ![(m:ℤ), (k:ℤ) - 1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_right m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ n := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjn : (j:ℤ) ≤ (n:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(m:ℤ), (j:ℤ) - 1] ![(m:ℤ), (j:ℤ)] := by
      have h := boxFrame_right_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_right m n (j:ℤ) (by omega) hjn



theorem boxFrame_top_walk (m n : ℕ) (k : ℕ) (hk : k ≤ m + 1) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), (n:ℤ)] ![(k:ℤ) - 1, (n:ℤ)], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  induction k with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    have hw := SimpleGraph.Walk.mem_support_nil_iff.mp hw
    rw [hw]
    exact mem_boxFrame_top m n (-1) (le_refl _) (by omega)
  | succ j ih =>
    have hj : j ≤ m := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    have hjm : (j:ℤ) ≤ (m:ℤ) := by exact_mod_cast hj
    have hadj : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj
        ![(j:ℤ) - 1, (n:ℤ)] ![(j:ℤ), (n:ℤ)] := by
      have h := boxFrame_top_adj m n ((j:ℤ) - 1) (by omega) (by omega)
      rwa [show ((j:ℤ) - 1 + 1) = (j:ℤ) from by ring] at h
    refine ⟨(p.concat hadj).copy rfl (by rw [show (((j + 1 : ℕ):ℤ) - 1) = (j:ℤ) from by
      push_cast; ring]), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp w hw
    · rw [List.mem_singleton] at hw; rw [hw]
      exact mem_boxFrame_top m n (j:ℤ) (by omega) hjm








theorem mem_boxFrame_cases (m n : ℕ) (v : Site 2) (hv : v ∈ boxFrame m n) :
    (∃ a : ℤ, -1 ≤ a ∧ a ≤ m ∧ v = ![a, -1]) ∨
    (∃ a : ℤ, -1 ≤ a ∧ a ≤ m ∧ v = ![a, (n:ℤ)]) ∨
    (∃ b : ℤ, -1 ≤ b ∧ b ≤ n ∧ v = ![(-1:ℤ), b]) ∨
    (∃ b : ℤ, -1 ≤ b ∧ b ≤ n ∧ v = ![(m:ℤ), b]) := by
  unfold boxFrame at hv
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at hv
  rcases hv with ((hb | ht) | hl) | hr
  · rw [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb
    rw [Finset.mem_Icc] at ha; exact Or.inl ⟨a, ha.1, ha.2, rfl⟩
  · rw [Finset.mem_image] at ht; obtain ⟨a, ha, rfl⟩ := ht
    rw [Finset.mem_Icc] at ha; exact Or.inr (Or.inl ⟨a, ha.1, ha.2, rfl⟩)
  · rw [Finset.mem_image] at hl; obtain ⟨b, hb, rfl⟩ := hl
    rw [Finset.mem_Icc] at hb; exact Or.inr (Or.inr (Or.inl ⟨b, hb.1, hb.2, rfl⟩))
  · rw [Finset.mem_image] at hr; obtain ⟨b, hb, rfl⟩ := hr
    rw [Finset.mem_Icc] at hb; exact Or.inr (Or.inr (Or.inr ⟨b, hb.1, hb.2, rfl⟩))


theorem mem_boxFrame_corner (m n : ℕ) : (![(-1:ℤ), -1] : Site 2) ∈ boxFrame m n :=
  mem_boxFrame_bottom m n (-1) (le_refl _) (by omega)


theorem boxFrame_bottom_to_corner (m n : ℕ) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(m:ℤ), -1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  obtain ⟨p, hp⟩ := boxFrame_bottom_walk m n (m + 1) (le_refl _)
  refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨by push_cast; ring, rfl⟩), ?_⟩
  intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw


theorem boxFrame_left_to_corner (m n : ℕ) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk
        ![(-1:ℤ), -1] ![(-1:ℤ), (n:ℤ)], ∀ w ∈ p.support, w ∈ boxFrame m n := by
  obtain ⟨p, hp⟩ := boxFrame_left_walk m n (n + 1) (le_refl _)
  refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨rfl, by push_cast; ring⟩), ?_⟩
  intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw



theorem boxFrame_walk_from_corner (m n : ℕ) {v : Site 2} (hv : v ∈ boxFrame m n) :
    ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] v,
      ∀ w ∈ p.support, w ∈ boxFrame m n := by
  rcases mem_boxFrame_cases m n v hv with ⟨a, ha1, ha2, rfl⟩ | ⟨a, ha1, ha2, rfl⟩ |
    ⟨b, hb1, hb2, rfl⟩ | ⟨b, hb1, hb2, rfl⟩
  · 
    obtain ⟨p, hp⟩ := boxFrame_bottom_walk m n (a + 1).toNat (by omega)
    refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨by omega, rfl⟩), ?_⟩
    intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw
  · 
    obtain ⟨p1, hp1⟩ := boxFrame_left_to_corner m n
    obtain ⟨p2, hp2⟩ := boxFrame_top_walk m n (a + 1).toNat (by omega)
    refine ⟨p1.append (p2.copy rfl ((site2_eq _ _ _ _).mpr ⟨by omega, rfl⟩)), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp1 w hw
    · have hw := List.mem_of_mem_tail hw
      rw [SimpleGraph.Walk.support_copy] at hw; exact hp2 w hw
  · 
    obtain ⟨p, hp⟩ := boxFrame_left_walk m n (b + 1).toNat (by omega)
    refine ⟨p.copy rfl ((site2_eq _ _ _ _).mpr ⟨rfl, by omega⟩), ?_⟩
    intro w hw; rw [SimpleGraph.Walk.support_copy] at hw; exact hp w hw
  · 
    obtain ⟨p1, hp1⟩ := boxFrame_bottom_to_corner m n
    obtain ⟨p2, hp2⟩ := boxFrame_right_walk m n (b + 1).toNat (by omega)
    refine ⟨p1.append (p2.copy rfl ((site2_eq _ _ _ _).mpr ⟨rfl, by omega⟩)), ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hp1 w hw
    · have hw := List.mem_of_mem_tail hw
      rw [SimpleGraph.Walk.support_copy] at hw; exact hp2 w hw







theorem boxCluster_faceBoundaryConnected (m n : ℕ) :
    FaceBoundaryConnected (↑(boxCluster m n) : Set (Site 2)) (boxFrame m n) := by
  apply faceBoundaryConnected_of_walks ⟨_, mem_boxFrame_corner m n⟩
  intro f hf g hg
  obtain ⟨pf, hpf⟩ := boxFrame_walk_from_corner m n hf
  obtain ⟨pg, hpg⟩ := boxFrame_walk_from_corner m n hg
  refine ⟨pf.reverse.append pg, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_append] at hw
  rcases List.mem_append.mp hw with hwf | hwg
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hwf
    exact hpf w hwf
  · exact hpg w (List.mem_of_mem_tail hwg)











theorem straddle_implies_frame (m n : ℕ) (a b : ℤ)
    (hin : (0 ≤ a ∧ a ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ (0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨
      (0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n) ∨ (0 ≤ a ∧ a ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n))
    (hout : ¬(0 ≤ a ∧ a ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ ¬(0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨
      ¬(0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n) ∨
      ¬(0 ≤ a ∧ a ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n)) :
    (-1 ≤ a ∧ a ≤ m ∧ b = -1) ∨ (-1 ≤ a ∧ a ≤ m ∧ b = (n:ℤ)) ∨
    (a = -1 ∧ -1 ≤ b ∧ b ≤ n) ∨ (a = (m:ℤ) ∧ -1 ≤ b ∧ b ≤ n) := by
  omega



theorem bdInd_eq_zero_of_sameSide (m n : ℕ) (x y : Site 2)
    (h : (x ∈ (↑(boxCluster m n) : Set (Site 2))) ↔ (y ∈ (↑(boxCluster m n) : Set (Site 2)))) :
    bdInd (↑(boxCluster m n) : Set (Site 2)) x y = 0 := by
  unfold bdInd
  rw [if_neg]
  by_cases hx : x ∈ (↑(boxCluster m n) : Set (Site 2)) <;>
    by_cases hy : y ∈ (↑(boxCluster m n) : Set (Site 2)) <;> simp_all




theorem support_boxCluster_subset_frame (m n : ℕ) :
    (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).support
      ⊆ (boxFrame m n : Set (Site 2)) := by
  intro f hf
  rw [SimpleGraph.mem_support] at hf
  obtain ⟨g, hadj⟩ := hf
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hdeg : 0 < faceBoundaryDegree (↑(boxCluster m n) : Set (Site 2)) (f 0) (f 1) := by
    rw [← degree_faceBoundaryGraph, ← hfeq]; exact hadj.degree_pos_left
  
  have c00 : (faceCorner00 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) := by unfold faceCorner00; rw [mem_box_coords]
  have c10 : (faceCorner10 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) := by unfold faceCorner10; rw [mem_box_coords]
  have c11 : (faceCorner11 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by
    unfold faceCorner11; rw [mem_box_coords]
  have c01 : (faceCorner01 (f 0) (f 1)) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔
      (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by unfold faceCorner01; rw [mem_box_coords]
  
  have hbothdir : (∃ c : Site 2, c ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
        faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)) ∧
        c ∈ (↑(boxCluster m n) : Set (Site 2))) ∧
      (∃ c : Site 2, c ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
        faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)) ∧
        c ∉ (↑(boxCluster m n) : Set (Site 2))) := by
    by_contra hcon
    rw [not_and_or] at hcon
    have hbd0 : faceBoundaryDegree (↑(boxCluster m n) : Set (Site 2)) (f 0) (f 1) = 0 := by
      unfold faceBoundaryDegree
      have key : ∀ x ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
          faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)),
          ∀ y ∈ ({faceCorner00 (f 0) (f 1), faceCorner10 (f 0) (f 1),
          faceCorner11 (f 0) (f 1), faceCorner01 (f 0) (f 1)} : Set (Site 2)),
          (x ∈ (↑(boxCluster m n) : Set (Site 2))) ↔ (y ∈ (↑(boxCluster m n) : Set (Site 2))) := by
        rcases hcon with hcon | hcon
        · 
          push Not at hcon
          intro x hx y hy
          exact iff_of_false (hcon x hx) (hcon y hy)
        · 
          push Not at hcon
          intro x hx y hy
          exact iff_of_true (hcon x hx) (hcon y hy)
      set z00 := faceCorner00 (f 0) (f 1)
      set z10 := faceCorner10 (f 0) (f 1)
      set z11 := faceCorner11 (f 0) (f 1)
      set z01 := faceCorner01 (f 0) (f 1)
      have h00 := bdInd_eq_zero_of_sameSide m n z00 z10
        (key _ (by left; rfl) _ (by right; left; rfl))
      have h10 := bdInd_eq_zero_of_sameSide m n z10 z11
        (key _ (by right; left; rfl) _ (by right; right; left; rfl))
      have h11 := bdInd_eq_zero_of_sameSide m n z11 z01
        (key _ (by right; right; left; rfl) _ (by right; right; right; rfl))
      have h01 := bdInd_eq_zero_of_sameSide m n z01 z00
        (key _ (by right; right; right; rfl) _ (by left; rfl))
      rw [h00, h10, h11, h01]
    omega
  
  obtain ⟨⟨ci, hci, hciin⟩, ⟨co, hco, hcoout⟩⟩ := hbothdir
  rw [hfeq, Finset.mem_coe]
  
  have hin : (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      (0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) ∨
      (0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hci
    rcases hci with rfl | rfl | rfl | rfl
    · exact Or.inl (c00.mp hciin)
    · exact Or.inr (Or.inl (c10.mp hciin))
    · exact Or.inr (Or.inr (Or.inl (c11.mp hciin)))
    · exact Or.inr (Or.inr (Or.inr (c01.mp hciin)))
  have hout : ¬(0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      ¬(0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 ∧ f 1 ≤ n) ∨
      ¬(0 ≤ f 0 + 1 ∧ f 0 + 1 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) ∨
      ¬(0 ≤ f 0 ∧ f 0 ≤ m ∧ 0 ≤ f 1 + 1 ∧ f 1 + 1 ≤ n) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hco
    rcases hco with rfl | rfl | rfl | rfl
    · exact Or.inl (fun h => hcoout (c00.mpr h))
    · exact Or.inr (Or.inl (fun h => hcoout (c10.mpr h)))
    · exact Or.inr (Or.inr (Or.inl (fun h => hcoout (c11.mpr h))))
    · exact Or.inr (Or.inr (Or.inr (fun h => hcoout (c01.mpr h))))
  rcases straddle_implies_frame m n (f 0) (f 1) hin hout with
    ⟨h1, h2, hb⟩ | ⟨h1, h2, hb⟩ | ⟨ha, h2, h3⟩ | ⟨ha, h2, h3⟩
  · rw [hb]; exact mem_boxFrame_bottom m n (f 0) h1 h2
  · rw [hb]; exact mem_boxFrame_top m n (f 0) h1 h2
  · rw [ha]; exact mem_boxFrame_left m n (f 1) h2 h3
  · rw [ha]; exact mem_boxFrame_right m n (f 1) h2 h3






theorem boxCluster_single_dualCircuit (m n : ℕ) :
    ∃ c : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(-1:ℤ), -1],
      c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet,
        e ∈ c.edges :=
  faceBoundaryGraph_single_dualCircuit (support_boxCluster_subset_frame m n)
    (boxCluster_faceBoundaryConnected m n) (mem_boxFrame_corner m n)

end Lattice

end StatMech
